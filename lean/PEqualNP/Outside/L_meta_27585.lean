import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27585_aux

open PEqualNP.CircuitLowerBounds

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

lemma getD_append_lt {α : Type} (l r : List α) (d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

lemma getD_append_last {α : Type} (l : List α) (a d : α) (n : ℕ) (hn : l.length = n) :
    (l ++ [a]).getD n d = a := by
  subst hn
  simp [List.getD_eq_getElem?_getD]

lemma getD_eq_getElem_of_lt {α : Type} (l : List α) (d : α) (i : ℕ) (hi : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

inductive BRef where
  | const (b : Bool)
  | lit (v : Fin 9) (neg : Bool)
  | wire (idx : ℕ) (neg : Bool)
  deriving DecidableEq

def BRef.flip : BRef → BRef
  | .const b => .const (!b)
  | .lit v neg => .lit v (!neg)
  | .wire idx neg => .wire idx (!neg)

def BRef.isConst : BRef → Bool
  | .const _ => true
  | _ => false

def BRef.ltBound (m : ℕ) : BRef → Prop
  | .const _ => True
  | .lit _ _ => True
  | .wire idx _ => idx < m

structure BGate where
  isOr : Bool
  a : BRef
  b : BRef
  deriving DecidableEq

structure BCircuit where
  gates : List BGate
  out : BRef

def BCircuit.WF (D : BCircuit) : Prop :=
  (∀ j : ℕ, (hj : j < D.gates.length) →
    (D.gates[j]).a.ltBound j ∧ (D.gates[j]).b.ltBound j) ∧
  D.out.ltBound D.gates.length

def evalRef (x : Fin 9 → Bool) (ws : List Bool) : BRef → Bool
  | .const b => b
  | .lit v neg => xor (x v) neg
  | .wire idx neg => xor (ws.getD idx false) neg

def evalGate (x : Fin 9 → Bool) (ws : List Bool) (g : BGate) : Bool :=
  let va := evalRef x ws g.a
  let vb := evalRef x ws g.b
  if g.isOr then va || vb else va && vb

def evalWires (x : Fin 9 → Bool) (gs : List BGate) : List Bool :=
  gs.foldl (fun ws g => ws ++ [evalGate x ws g]) []

def BCircuit.eval (D : BCircuit) (x : Fin 9 → Bool) : Bool :=
  evalRef x (evalWires x D.gates) D.out

lemma evalRef_flip (x : Fin 9 → Bool) (ws : List Bool) (r : BRef) :
    evalRef x ws r.flip = !(evalRef x ws r) := by
  cases r with
  | const b => cases b <;> rfl
  | lit v neg => simp only [BRef.flip, evalRef]; cases x v <;> cases neg <;> rfl
  | wire idx neg => simp only [BRef.flip, evalRef]; cases ws.getD idx false <;> cases neg <;> rfl

lemma evalWires_append (x : Fin 9 → Bool) (gs : List BGate) (g : BGate) :
    evalWires x (gs ++ [g]) = evalWires x gs ++ [evalGate x (evalWires x gs) g] := by
  simp [evalWires, List.foldl_append]

lemma evalWires_length (x : Fin 9 → Bool) (gs : List BGate) :
    (evalWires x gs).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [evalWires]
  | append_singleton gs g ih => rw [evalWires_append]; simp [ih]

lemma evalWires_getD_lt (x : Fin 9 → Bool) (gs hs : List BGate) (i : ℕ) (hi : i < gs.length) :
    (evalWires x (gs ++ hs)).getD i false = (evalWires x gs).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, evalWires_append]
    rw [getD_append_lt _ _ _ _ (by rw [evalWires_length, List.length_append]; omega)]
    exact ih

lemma evalRef_append (x : Fin 9 → Bool) (gs hs : List BGate) (r : BRef) (hr : r.ltBound gs.length) :
    evalRef x (evalWires x (gs ++ hs)) r = evalRef x (evalWires x gs) r := by
  cases r with
  | const b => rfl
  | lit v neg => rfl
  | wire idx neg =>
    simp only [BRef.ltBound] at hr
    simp only [evalRef, evalWires_getD_lt x gs hs idx hr]

lemma evalWires_getD_at (x : Fin 9 → Bool) (gs : List BGate) (j : ℕ) (hj : j < gs.length)
    (ha : (gs[j]).a.ltBound j) (hb : (gs[j]).b.ltBound j) :
    (evalWires x gs).getD j false = evalGate x (evalWires x gs) gs[j] := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    calc gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
      _ = gs.take j ++ (gs[j] :: gs.drop (j + 1)) := by rw [List.drop_eq_getElem_cons hj]
      _ = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by simp
  have htlen : (gs.take j).length = j := by simp; omega
  have h1 : (evalWires x gs).getD j false =
      (evalWires x (gs.take j ++ [gs[j]])).getD j false := by
    conv_lhs => rw [hsplit]
    exact evalWires_getD_lt x (gs.take j ++ [gs[j]]) (gs.drop (j + 1)) j (by simp; omega)
  rw [h1, evalWires_append, getD_append_last _ _ _ j (by rw [evalWires_length, htlen])]
  unfold evalGate
  set gj := gs[j]
  have ha' : gj.a.ltBound (gs.take j).length := by rwa [htlen]
  have hb' : gj.b.ltBound (gs.take j).length := by rwa [htlen]
  have hev_a : evalRef x (evalWires x gs) gj.a = evalRef x (evalWires x (gs.take j)) gj.a := by
    have h := evalRef_append x (gs.take j) (gs.drop j) gj.a ha'
    rwa [List.take_append_drop] at h
  have hev_b : evalRef x (evalWires x gs) gj.b = evalRef x (evalWires x (gs.take j)) gj.b := by
    have h := evalRef_append x (gs.take j) (gs.drop j) gj.b hb'
    rwa [List.take_append_drop] at h
  rw [hev_a, hev_b]

lemma BRef.ltBound_mono {m n : ℕ} {r : BRef} (h : r.ltBound m) (hmn : m ≤ n) : r.ltBound n := by
  cases r with
  | const _ => trivial
  | lit _ _ => trivial
  | wire idx _ => simp only [BRef.ltBound] at h ⊢; omega

lemma BRef.ltBound_flip {m : ℕ} {r : BRef} (h : r.ltBound m) : r.flip.ltBound m := by
  cases r <;> exact h

def foldBin (isOr : Bool) (ra rb : BRef) (gs : List BGate) : List BGate × BRef :=
  match ra, rb with
  | .const c, rb =>
    if isOr then (gs, if c then .const true else rb)
    else (gs, if c then rb else .const false)
  | ra, .const c =>
    if isOr then (gs, if c then .const true else ra)
    else (gs, if c then ra else .const false)
  | ra, rb =>
    (gs ++ [⟨isOr, ra, rb⟩], .wire gs.length false)

lemma foldBin_nonconst (x : Fin 9 → Bool) (isOr : Bool) (ra rb : BRef) (gs : List BGate)
    (ha : ra.ltBound gs.length) (hb : rb.ltBound gs.length)
    (hres : foldBin isOr ra rb gs = (gs ++ [⟨isOr, ra, rb⟩], .wire gs.length false))
    (hnc : ra.isConst = false ∧ rb.isConst = false) :
    let res := foldBin isOr ra rb gs
    (gs.length ≤ res.1.length ∧ res.1.length ≤ gs.length + 1) ∧
    ((ra.isConst = true ∨ rb.isConst = true) → res.1 = gs) ∧
    (∀ j : ℕ, (hj : j < res.1.length) →
      (∀ k : ℕ, (hk : k < gs.length) → (gs[k]).a.ltBound k ∧ (gs[k]).b.ltBound k) →
      (res.1[j]).a.ltBound j ∧ (res.1[j]).b.ltBound j) ∧
    res.2.ltBound res.1.length ∧
    evalRef x (evalWires x res.1) res.2 =
      (if isOr then evalRef x (evalWires x gs) ra || evalRef x (evalWires x gs) rb
       else evalRef x (evalWires x gs) ra && evalRef x (evalWires x gs) rb) ∧
    (∀ i < gs.length, (evalWires x res.1).getD i false = (evalWires x gs).getD i false) := by
  simp only [hres]
  refine ⟨⟨by simp, by simp⟩, fun h => by simp [hnc.1, hnc.2] at h, ?_, ?_, ?_, ?_⟩
  · intro j hj hwf
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | rfl
    · rw [List.getElem_append_left hlt]; exact hwf j hlt
    · rw [List.getElem_append_right le_rfl]; simp [ha, hb]
  · simp [BRef.ltBound]
  · simp only [evalRef, evalWires_append, Bool.xor_false]
    rw [getD_append_last _ _ _ gs.length (evalWires_length x gs)]
    rfl
  · intro i hi; exact evalWires_getD_lt x gs _ i hi

lemma foldBin_sound (x : Fin 9 → Bool) (isOr : Bool) (ra rb : BRef) (gs : List BGate)
    (ha : ra.ltBound gs.length) (hb : rb.ltBound gs.length) :
    let res := foldBin isOr ra rb gs
    (gs.length ≤ res.1.length ∧ res.1.length ≤ gs.length + 1) ∧
    ((ra.isConst = true ∨ rb.isConst = true) → res.1 = gs) ∧
    (∀ j : ℕ, (hj : j < res.1.length) →
      (∀ k : ℕ, (hk : k < gs.length) → (gs[k]).a.ltBound k ∧ (gs[k]).b.ltBound k) →
      (res.1[j]).a.ltBound j ∧ (res.1[j]).b.ltBound j) ∧
    res.2.ltBound res.1.length ∧
    evalRef x (evalWires x res.1) res.2 =
      (if isOr then evalRef x (evalWires x gs) ra || evalRef x (evalWires x gs) rb
       else evalRef x (evalWires x gs) ra && evalRef x (evalWires x gs) rb) ∧
    (∀ i < gs.length, (evalWires x res.1).getD i false = (evalWires x gs).getD i false) := by
  cases ra with
  | const c =>
    cases isOr <;> cases c
    · exact ⟨⟨le_rfl, Nat.le_succ _⟩, fun _ => rfl, fun j hj hwf => hwf j hj, trivial, by simp [foldBin, evalRef], fun _ _ => rfl⟩
    · exact ⟨⟨le_rfl, Nat.le_succ _⟩, fun _ => rfl, fun j hj hwf => hwf j hj, hb, by simp [foldBin, evalRef], fun _ _ => rfl⟩
    · exact ⟨⟨le_rfl, Nat.le_succ _⟩, fun _ => rfl, fun j hj hwf => hwf j hj, hb, by simp [foldBin, evalRef], fun _ _ => rfl⟩
    · exact ⟨⟨le_rfl, Nat.le_succ _⟩, fun _ => rfl, fun j hj hwf => hwf j hj, trivial, by simp [foldBin, evalRef], fun _ _ => rfl⟩
  | lit v nv =>
    cases rb with
    | const c =>
      cases isOr <;> cases c
      · exact ⟨⟨le_rfl, Nat.le_succ _⟩, fun _ => rfl, fun j hj hwf => hwf j hj, trivial, by simp [foldBin, evalRef], fun _ _ => rfl⟩
      · exact ⟨⟨le_rfl, Nat.le_succ _⟩, fun _ => rfl, fun j hj hwf => hwf j hj, ha, by simp [foldBin, evalRef], fun _ _ => rfl⟩
      · exact ⟨⟨le_rfl, Nat.le_succ _⟩, fun _ => rfl, fun j hj hwf => hwf j hj, ha, by simp [foldBin, evalRef], fun _ _ => rfl⟩
      · exact ⟨⟨le_rfl, Nat.le_succ _⟩, fun _ => rfl, fun j hj hwf => hwf j hj, trivial, by simp [foldBin, evalRef], fun _ _ => rfl⟩
    | lit u nu => exact foldBin_nonconst x isOr _ _ gs ha hb rfl ⟨rfl, rfl⟩
    | wire iu nu => exact foldBin_nonconst x isOr _ _ gs ha hb rfl ⟨rfl, rfl⟩
  | wire iv nv =>
    cases rb with
    | const c =>
      cases isOr <;> cases c
      · exact ⟨⟨le_rfl, Nat.le_succ _⟩, fun _ => rfl, fun j hj hwf => hwf j hj, trivial, by simp [foldBin, evalRef], fun _ _ => rfl⟩
      · exact ⟨⟨le_rfl, Nat.le_succ _⟩, fun _ => rfl, fun j hj hwf => hwf j hj, ha, by simp [foldBin, evalRef], fun _ _ => rfl⟩
      · exact ⟨⟨le_rfl, Nat.le_succ _⟩, fun _ => rfl, fun j hj hwf => hwf j hj, ha, by simp [foldBin, evalRef], fun _ _ => rfl⟩
      · exact ⟨⟨le_rfl, Nat.le_succ _⟩, fun _ => rfl, fun j hj hwf => hwf j hj, trivial, by simp [foldBin, evalRef], fun _ _ => rfl⟩
    | lit u nu => exact foldBin_nonconst x isOr _ _ gs ha hb rfl ⟨rfl, rfl⟩
    | wire iu nu => exact foldBin_nonconst x isOr _ _ gs ha hb rfl ⟨rfl, rfl⟩

def substRef (v : Fin 9) (b : Bool) (env : List BRef) : BRef → BRef
  | .const c => .const c
  | .lit u neg => if u = v then .const (xor b neg) else .lit u neg
  | .wire idx neg =>
    let r := env.getD idx (.const false)
    if neg then r.flip else r

def restrictStep (v : Fin 9) (b : Bool) (st : List BGate × List BRef) (g : BGate) :
    List BGate × List BRef :=
  let ra := substRef v b st.2 g.a
  let rb := substRef v b st.2 g.b
  let (gs', r') := foldBin g.isOr ra rb st.1
  (gs', st.2 ++ [r'])

def restrictState (v : Fin 9) (b : Bool) (gs : List BGate) : List BGate × List BRef :=
  gs.foldl (restrictStep v b) ([], [])

def BCircuit.restrict (D : BCircuit) (v : Fin 9) (b : Bool) : BCircuit :=
  let st := restrictState v b D.gates
  ⟨st.1, substRef v b st.2 D.out⟩

def gateReadsVar (v : Fin 9) (g : BGate) : Prop :=
  (∃ neg, g.a = .lit v neg) ∨ (∃ neg, g.b = .lit v neg)

def gateReadsWire (idx : ℕ) (g : BGate) : Prop :=
  (∃ neg, g.a = .wire idx neg) ∨ (∃ neg, g.b = .wire idx neg)

lemma substRef_ltBound (v : Fin 9) (b : Bool) (env : List BRef) (m : ℕ)
    (henv : ∀ r ∈ env, r.ltBound m) (r : BRef) :
    (substRef v b env r).ltBound m := by
  cases r with
  | const c => trivial
  | lit u neg =>
    simp only [substRef]
    split_ifs <;> trivial
  | wire idx neg =>
    simp only [substRef]
    have hm : (env.getD idx (.const false)).ltBound m := by
      rw [List.getD_eq_getElem?_getD]
      cases h : env[idx]? with
      | none => trivial
      | some r' => exact henv r' (List.mem_of_getElem? h)
    split_ifs
    · exact BRef.ltBound_flip hm
    · exact hm

lemma substRef_eval (v : Fin 9) (b : Bool) (x : Fin 9 → Bool) (hxv : x v = b)
    (gs gs' : List BGate) (env : List BRef)
    (henv : ∀ i < gs.length, evalRef x (evalWires x gs') (env.getD i (.const false)) =
      (evalWires x gs).getD i false)
    (r : BRef) (hr : r.ltBound gs.length) :
    evalRef x (evalWires x gs') (substRef v b env r) = evalRef x (evalWires x gs) r := by
  cases r with
  | const c => rfl
  | lit u neg =>
    simp only [substRef]
    split_ifs with h
    · subst h; simp [evalRef, hxv]
    · rfl
  | wire idx neg =>
    simp only [BRef.ltBound] at hr
    simp only [substRef]
    cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte, evalRef, Bool.xor_false]
      exact henv idx hr
    · simp only [↓reduceIte]
      rw [evalRef_flip, henv idx hr]
      simp only [evalRef, Bool.xor_true]

lemma restrictState_snoc (v : Fin 9) (b : Bool) (gs : List BGate) (g : BGate) :
    restrictState v b (gs ++ [g]) = restrictStep v b (restrictState v b gs) g := by
  simp [restrictState, List.foldl_append]

lemma restrictState_env_length (v : Fin 9) (b : Bool) (gs : List BGate) :
    (restrictState v b gs).2.length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => rw [restrictState_snoc]; simp [restrictStep, ih]

lemma restrictState_env_take (v : Fin 9) (b : Bool) (gs : List BGate) (j : ℕ) (hj : j ≤ gs.length) :
    ∀ i < j, (restrictState v b gs).2.getD i (.const false) =
      (restrictState v b (gs.take j)).2.getD i (.const false) := by
  induction gs using List.reverseRecOn generalizing j with
  | nil => intro i hi; simp at hj; omega
  | append_singleton gs g ih =>
    intro i hi
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · have hjle : j ≤ gs.length := Nat.lt_succ_iff.mp hlt
      rw [List.take_append_of_le_length hjle, restrictState_snoc]
      have hslen := restrictState_env_length v b gs
      have hget : (restrictStep v b (restrictState v b gs) g).2.getD i (.const false) =
          (restrictState v b gs).2.getD i (.const false) :=
        getD_append_lt _ _ _ i (by omega)
      rw [hget]
      exact ih j hjle i hi
    · rw [show gs.length + 1 = (gs ++ [g]).length by simp, List.take_length]

def isDroppedRestrict (v : Fin 9) (b : Bool) (gs : List BGate) (j : ℕ) : Bool :=
  let stj := restrictState v b (gs.take j)
  let gj := gs.getD j ⟨false, .const false, .const false⟩
  (substRef v b stj.2 gj.a).isConst || (substRef v b stj.2 gj.b).isConst

lemma restrictState_inv (v : Fin 9) (b : Bool) (gs : List BGate)
    (hwf : ∀ j : ℕ, (hj : j < gs.length) → (gs[j]).a.ltBound j ∧ (gs[j]).b.ltBound j) :
    let st := restrictState v b gs
    st.2.length = gs.length ∧
    (∀ j : ℕ, (hj : j < st.1.length) → (st.1[j]).a.ltBound j ∧ (st.1[j]).b.ltBound j) ∧
    (∀ r ∈ st.2, r.ltBound st.1.length) ∧
    (∀ x : Fin 9 → Bool, x v = b →
      ∀ i < gs.length, evalRef x (evalWires x st.1) (st.2.getD i (.const false)) =
        (evalWires x gs).getD i false) ∧
    st.1.length + (List.range gs.length).countP (isDroppedRestrict v b gs) ≤ gs.length := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨rfl, fun j hj => by simp [restrictState] at hj,
      fun r hr => by simp [restrictState] at hr,
      fun _ _ i hi => by simp at hi, by simp [restrictState]⟩
  | append_singleton gs g ih =>
    have hwf_pre : ∀ j : ℕ, (hj : j < gs.length) → (gs[j]).a.ltBound j ∧ (gs[j]).b.ltBound j := by
      intro j hj
      have h := hwf j (by simp; omega)
      simpa [List.getElem_append_left hj] using h
    have hwf_g : g.a.ltBound gs.length ∧ g.b.ltBound gs.length := by
      have h := hwf gs.length (by simp)
      simpa using h
    obtain ⟨hlen, hwf1, hlt, heval, hcnt⟩ := ih hwf_pre
    rw [restrictState_snoc]
    set st := restrictState v b gs
    set ra := substRef v b st.2 g.a
    set rb := substRef v b st.2 g.b
    have hra : ra.ltBound st.1.length := substRef_ltBound v b st.2 st.1.length hlt g.a
    have hrb : rb.ltBound st.1.length := substRef_ltBound v b st.2 st.1.length hlt g.b
    have hfb := fun x => foldBin_sound x g.isOr ra rb st.1 hra hrb
    have hfb0 := hfb (fun _ => false)
    set res := foldBin g.isOr ra rb st.1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [restrictStep, hlen]
    · intro j hj
      exact hfb0.2.2.1 j hj hwf1
    · intro r hr
      simp only [restrictStep, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact BRef.ltBound_mono (hlt r hr) hfb0.1.1
      · exact hfb0.2.2.2.1
    · intro x hxv i hi
      simp only [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt_i | rfl
      · have hget : (st.2 ++ [res.2]).getD i (.const false) = st.2.getD i (.const false) :=
          getD_append_lt _ _ _ i (by omega)
        rw [show (restrictStep v b st g).2 = st.2 ++ [res.2] from rfl, hget]
        have hlt_r : (st.2.getD i (.const false)).ltBound st.1.length := by
          rw [List.getD_eq_getElem?_getD]
          cases h : st.2[i]? with
          | none => trivial
          | some r' => exact hlt r' (List.mem_of_getElem? h)
        have hsame : evalRef x (evalWires x res.1) (st.2.getD i (.const false)) =
            evalRef x (evalWires x st.1) (st.2.getD i (.const false)) := by
          cases hr : st.2.getD i (.const false) with
          | const _ => rfl
          | lit _ _ => rfl
          | wire idx neg =>
            rw [hr] at hlt_r
            simp only [BRef.ltBound] at hlt_r
            simp only [evalRef, (hfb x).2.2.2.2.2 idx hlt_r]
        rw [show (restrictStep v b st g).1 = res.1 from rfl, hsame, heval x hxv i hlt_i]
        exact (evalWires_getD_lt x gs [g] i hlt_i).symm
      · have hget : (st.2 ++ [res.2]).getD gs.length (.const false) = res.2 :=
          getD_append_last _ _ _ gs.length hlen
        rw [show (restrictStep v b st g).2 = st.2 ++ [res.2] from rfl, hget,
            show (restrictStep v b st g).1 = res.1 from rfl]
        rw [(hfb x).2.2.2.2.1]
        rw [substRef_eval v b x hxv gs st.1 st.2 (heval x hxv) g.a hwf_g.1,
            substRef_eval v b x hxv gs st.1 st.2 (heval x hxv) g.b hwf_g.2]
        rw [evalWires_append, getD_append_last _ _ _ gs.length (evalWires_length x gs)]
        rfl
    · rw [List.length_append, List.length_singleton, List.range_succ, List.countP_append,
          List.countP_singleton]
      have hcongr : (List.range gs.length).countP (isDroppedRestrict v b (gs ++ [g])) =
          (List.range gs.length).countP (isDroppedRestrict v b gs) := by
        rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
        congr 1
        apply List.filter_congr
        intro j hj
        have hjlt : j < gs.length := List.mem_range.mp hj
        have ht : (gs ++ [g]).take j = gs.take j := List.take_append_of_le_length (le_of_lt hjlt)
        have hg : (gs ++ [g]).getD j ⟨false, .const false, .const false⟩ =
            gs.getD j ⟨false, .const false, .const false⟩ := getD_append_lt _ _ _ j hjlt
        simp only [isDroppedRestrict, ht, hg]
      rw [hcongr]
      have htlast : (gs ++ [g]).take gs.length = gs := by simp
      have hglast : (gs ++ [g]).getD gs.length ⟨false, .const false, .const false⟩ = g :=
        getD_append_last _ _ _ gs.length rfl
      have hdrop_last : isDroppedRestrict v b (gs ++ [g]) gs.length = (ra.isConst || rb.isConst) := by
        simp only [isDroppedRestrict, htlast, hglast]; rfl
      rw [hdrop_last]
      change res.1.length + ((List.range gs.length).countP (isDroppedRestrict v b gs) +
        if (ra.isConst || rb.isConst) = true then 1 else 0) ≤ gs.length + 1
      split_ifs with hc
      · have heq : res.1 = st.1 := hfb0.2.1 (Bool.or_eq_true_iff.mp hc)
        rw [heq]; omega
      · have hle : res.1.length ≤ st.1.length + 1 := hfb0.1.2
        omega

lemma restrict_wf (D : BCircuit) (hD : D.WF) (v : Fin 9) (b : Bool) : (D.restrict v b).WF := by
  have h := restrictState_inv v b D.gates hD.1
  exact ⟨h.2.1, substRef_ltBound v b _ _ h.2.2.1 D.out⟩

lemma restrict_eval (D : BCircuit) (hD : D.WF) (v : Fin 9) (b : Bool)
    (x : Fin 9 → Bool) (hxv : x v = b) :
    (D.restrict v b).eval x = D.eval x := by
  have h := restrictState_inv v b D.gates hD.1
  unfold BCircuit.restrict BCircuit.eval
  exact substRef_eval v b x hxv D.gates (restrictState v b D.gates).1
    (restrictState v b D.gates).2 (h.2.2.2.1 x hxv) D.out hD.2

lemma countP_two_le {α : Type} [DecidableEq α] (l : List α) (p : α → Bool) (a b : α)
    (hnd : l.Nodup) (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) (hpa : p a = true) (hpb : p b = true) :
    2 ≤ l.countP p := by
  rw [List.countP_eq_length_filter]
  have hfnd : (l.filter p).Nodup := hnd.filter p
  have hfa : a ∈ (l.filter p).toFinset := List.mem_toFinset.mpr (List.mem_filter.mpr ⟨ha, hpa⟩)
  have hfb : b ∈ (l.filter p).toFinset := List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hb, hpb⟩)
  have hsub : ({a, b} : Finset α) ⊆ (l.filter p).toFinset := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair hab, List.toFinset_card_of_nodup hfnd] at hc
  exact hc

lemma countP_three_le {α : Type} [DecidableEq α] (l : List α) (p : α → Bool) (a b c : α)
    (hnd : l.Nodup) (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpa : p a = true) (hpb : p b = true) (hpc : p c = true) :
    3 ≤ l.countP p := by
  rw [List.countP_eq_length_filter]
  have hfnd : (l.filter p).Nodup := hnd.filter p
  have hfa : a ∈ (l.filter p).toFinset := List.mem_toFinset.mpr (List.mem_filter.mpr ⟨ha, hpa⟩)
  have hfb : b ∈ (l.filter p).toFinset := List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hb, hpb⟩)
  have hfc : c ∈ (l.filter p).toFinset := List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hc, hpc⟩)
  have hsub : ({a, b, c} : Finset α) ⊆ (l.filter p).toFinset := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have hcard := Finset.card_le_card hsub
  have h3 : ({a, b, c} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  rw [h3, List.toFinset_card_of_nodup hfnd] at hcard
  exact hcard

def reachStep (gs : List BGate) : ℕ → Finset ℕ → Finset ℕ
  | 0, acc => acc
  | j + 1, acc =>
    let acc' :=
      if j ∈ acc then
        let g := gs.getD j ⟨false, .const false, .const false⟩
        let acc1 := match g.a with | .wire i _ => insert i acc | _ => acc
        match g.b with | .wire i _ => insert i acc1 | _ => acc1
      else acc
    reachStep gs j acc'

def liveSet (D : BCircuit) : Finset ℕ :=
  let init : Finset ℕ := match D.out with | .wire i _ => {i} | _ => ∅
  reachStep D.gates D.gates.length init

lemma reachStep_subset (gs : List BGate) (m : ℕ) (acc : Finset ℕ) :
    acc ⊆ reachStep gs m acc := by
  induction m generalizing acc with
  | zero => exact Finset.Subset.refl _
  | succ m ih =>
    intro x hx
    apply ih
    by_cases hm : m ∈ acc
    · simp only [hm, ↓reduceIte]
      cases (gs.getD m ⟨false, .const false, .const false⟩).a <;>
        cases (gs.getD m ⟨false, .const false, .const false⟩).b <;>
        simp [hx]
    · simp [hm, hx]

lemma reachStep_bound (gs : List BGate) (hwf : ∀ j : ℕ, (hj : j < gs.length) →
    (gs[j]).a.ltBound j ∧ (gs[j]).b.ltBound j) :
    ∀ m ≤ gs.length, ∀ acc : Finset ℕ, (∀ i ∈ acc, i < gs.length) →
      ∀ i ∈ reachStep gs m acc, i < gs.length := by
  intro m
  induction m with
  | zero => intro _ acc hacc; exact hacc
  | succ m ih =>
    intro hm acc hacc
    apply ih (by omega)
    intro i hi
    by_cases hm_in : m ∈ acc
    · simp only [hm_in, ↓reduceIte] at hi
      have hgm : gs.getD m ⟨false, .const false, .const false⟩ = gs[m]'(by omega) :=
        getD_eq_getElem_of_lt gs _ m (by omega)
      rw [hgm] at hi
      obtain ⟨ha, hb⟩ := hwf m (by omega)
      cases hae : (gs[m]'(by omega)).a <;> cases hbe : (gs[m]'(by omega)).b
      all_goals rw [hae] at ha; rw [hbe] at hb; simp only [BRef.ltBound] at ha hb
      all_goals rw [hae, hbe] at hi
      all_goals try exact hacc i hi
      all_goals rcases Finset.mem_insert.mp hi with rfl | hi1
      all_goals first | omega | exact hacc i hi1 | (rcases Finset.mem_insert.mp hi1 with rfl | hi2; omega; exact hacc i hi2)
    · simp only [hm_in, ↓reduceIte] at hi
      exact hacc i hi

lemma reachStep_ge_stable (gs : List BGate) (hwf : ∀ j : ℕ, (hj : j < gs.length) →
    (gs[j]).a.ltBound j ∧ (gs[j]).b.ltBound j) :
    ∀ m ≤ gs.length, ∀ acc : Finset ℕ, ∀ x, m ≤ x → (x ∈ reachStep gs m acc ↔ x ∈ acc) := by
  intro m
  induction m with
  | zero => intro _ acc x _; rfl
  | succ m ih =>
    intro hm acc x hx
    rw [reachStep, ih (by omega) _ x (by omega)]
    by_cases hm_in : m ∈ acc
    · simp only [hm_in, ↓reduceIte]
      have hgm : gs.getD m ⟨false, .const false, .const false⟩ = gs[m]'(by omega) :=
        getD_eq_getElem_of_lt gs _ m (by omega)
      rw [hgm]
      obtain ⟨ha, hb⟩ := hwf m (by omega)
      have hstep : ∀ (r : BRef) (s : Finset ℕ), r.ltBound m →
          ((x ∈ match r with | .wire i _ => insert i s | _ => s) ↔ x ∈ s) := by
        intro r s hr
        cases r with
        | const _ => rfl
        | lit _ _ => rfl
        | wire i _ =>
          simp only [BRef.ltBound] at hr
          simp only [Finset.mem_insert]
          exact ⟨fun h => h.resolve_left (by omega), fun h => Or.inr h⟩
      rw [hstep _ _ hb, hstep _ _ ha]
    · simp [hm_in]

lemma reachStep_closed_step (gs : List BGate) (hwf : ∀ j : ℕ, (hj : j < gs.length) →
    (gs[j]).a.ltBound j ∧ (gs[j]).b.ltBound j) :
    ∀ (m : ℕ) (hm : m ≤ gs.length), ∀ acc : Finset ℕ, ∀ (j : ℕ) (hj : j < m), j ∈ reachStep gs m acc →
      (∀ i neg, (gs[j]'(by omega)).a = .wire i neg → i ∈ reachStep gs m acc) ∧
      (∀ i neg, (gs[j]'(by omega)).b = .wire i neg → i ∈ reachStep gs m acc) := by
  intro m
  induction m with
  | zero => intro _ _ j hj; omega
  | succ m ih =>
    intro hm acc j hj hmem
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | rfl
    · exact ih (by omega) _ j hlt hmem
    · have hm_in : j ∈ acc := by
        rw [reachStep, reachStep_ge_stable gs hwf j (by omega) _ j le_rfl] at hmem
        by_cases hc : j ∈ acc
        · exact hc
        · simp [hc] at hmem
      have hgm : gs.getD j ⟨false, .const false, .const false⟩ = gs[j]'(by omega) :=
        getD_eq_getElem_of_lt gs _ j (by omega)
      constructor
      · intro i neg hae
        rw [reachStep]
        apply reachStep_subset
        simp only [hm_in, ↓reduceIte, hgm, hae]
        cases (gs[j]'(by omega)).b <;> simp
      · intro i neg hbe
        rw [reachStep]
        apply reachStep_subset
        simp only [hm_in, ↓reduceIte, hgm, hbe]
        cases (gs[j]'(by omega)).a <;> simp

lemma reachStep_parent (gs : List BGate) (_hwf : ∀ j : ℕ, (hj : j < gs.length) →
    (gs[j]).a.ltBound j ∧ (gs[j]).b.ltBound j) :
    ∀ m ≤ gs.length, ∀ acc : Finset ℕ, ∀ i ∈ reachStep gs m acc,
      i ∈ acc ∨ ∃ k ∈ reachStep gs m acc, ∃ hk : k < gs.length,
        k < m ∧ gateReadsWire i (gs[k]'hk) := by
  intro m
  induction m with
  | zero => intro _ acc i hi; exact Or.inl hi
  | succ m ih =>
    intro hm acc i hi
    rcases ih (by omega) _ i hi with h1 | ⟨k, hk_in, hk_lt, hkm, hread⟩
    · by_cases hm_in : m ∈ acc
      · simp only [hm_in, ↓reduceIte] at h1
        have hgm : gs.getD m ⟨false, .const false, .const false⟩ = gs[m]'(by omega) :=
          getD_eq_getElem_of_lt gs _ m (by omega)
        rw [hgm] at h1
        have hm_live : m ∈ reachStep gs (m + 1) acc := by
          rw [reachStep]; apply reachStep_subset
          simp only [hm_in, ↓reduceIte, hgm]
          cases (gs[m]'(by omega)).a <;> cases (gs[m]'(by omega)).b <;> simp [hm_in]
        cases hae : (gs[m]'(by omega)).a with
        | const _ =>
          cases hbe : (gs[m]'(by omega)).b with
          | const _ => rw [hae, hbe] at h1; exact Or.inl h1
          | lit _ _ => rw [hae, hbe] at h1; exact Or.inl h1
          | wire ib nb =>
            rw [hae, hbe] at h1
            rcases Finset.mem_insert.mp h1 with rfl | h1'
            · exact Or.inr ⟨m, hm_live, by omega, by omega, Or.inr ⟨nb, hbe⟩⟩
            · exact Or.inl h1'
        | lit _ _ =>
          cases hbe : (gs[m]'(by omega)).b with
          | const _ => rw [hae, hbe] at h1; exact Or.inl h1
          | lit _ _ => rw [hae, hbe] at h1; exact Or.inl h1
          | wire ib nb =>
            rw [hae, hbe] at h1
            rcases Finset.mem_insert.mp h1 with rfl | h1'
            · exact Or.inr ⟨m, hm_live, by omega, by omega, Or.inr ⟨nb, hbe⟩⟩
            · exact Or.inl h1'
        | wire ia na =>
          cases hbe : (gs[m]'(by omega)).b with
          | const _ =>
            rw [hae, hbe] at h1
            rcases Finset.mem_insert.mp h1 with rfl | h1'
            · exact Or.inr ⟨m, hm_live, by omega, by omega, Or.inl ⟨na, hae⟩⟩
            · exact Or.inl h1'
          | lit _ _ =>
            rw [hae, hbe] at h1
            rcases Finset.mem_insert.mp h1 with rfl | h1'
            · exact Or.inr ⟨m, hm_live, by omega, by omega, Or.inl ⟨na, hae⟩⟩
            · exact Or.inl h1'
          | wire ib nb =>
            rw [hae, hbe] at h1
            rcases Finset.mem_insert.mp h1 with rfl | h1'
            · exact Or.inr ⟨m, hm_live, by omega, by omega, Or.inr ⟨nb, hbe⟩⟩
            · rcases Finset.mem_insert.mp h1' with rfl | h1''
              · exact Or.inr ⟨m, hm_live, by omega, by omega, Or.inl ⟨na, hae⟩⟩
              · exact Or.inl h1''
      · simp only [hm_in, ↓reduceIte] at h1; exact Or.inl h1
    · exact Or.inr ⟨k, hk_in, hk_lt, by omega, hread⟩

def slotRef (D : BCircuit) (s : Option (ℕ × Bool)) : BRef :=
  match s with
  | none => D.out
  | some (j, false) => (D.gates.getD j ⟨false, .const false, .const false⟩).a
  | some (j, true) => (D.gates.getD j ⟨false, .const false, .const false⟩).b

lemma liveSet_eval_eq (D : BCircuit) (hD : D.WF) (x y : Fin 9 → Bool)
    (hagree : ∀ v : Fin 9,
      ((∃ neg, D.out = .lit v neg) ∨
        ∃ j ∈ liveSet D, ∃ hj : j < D.gates.length, gateReadsVar v (D.gates[j]'hj)) →
      x v = y v) :
    D.eval x = D.eval y := by
  have hlive_lt : ∀ j ∈ liveSet D, j < D.gates.length := by
    apply reachStep_bound D.gates hD.1 D.gates.length le_rfl
    intro i hi
    cases h : D.out with
    | const _ => simp [h] at hi
    | lit _ _ => simp [h] at hi
    | wire idx _ =>
      rw [h] at hi; simp only [Finset.mem_singleton] at hi; subst hi
      have ho := hD.2; rw [h] at ho; exact ho
  have hwire : ∀ j, j ∈ liveSet D →
      (evalWires x D.gates).getD j false = (evalWires y D.gates).getD j false := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj_live
      have hj : j < D.gates.length := hlive_lt j hj_live
      obtain ⟨ha, hb⟩ := hD.1 j hj
      rw [evalWires_getD_at x D.gates j hj ha hb, evalWires_getD_at y D.gates j hj ha hb]
      have hcl := reachStep_closed_step D.gates hD.1 D.gates.length le_rfl _ j hj hj_live
      have href : ∀ r : BRef, r.ltBound j →
          (∀ i neg, r = .wire i neg → i ∈ liveSet D) →
          (∀ v neg, r = .lit v neg → x v = y v) →
          evalRef x (evalWires x D.gates) r = evalRef y (evalWires y D.gates) r := by
        intro r hr hwi hli
        cases r with
        | const c => rfl
        | lit v neg => simp [evalRef, hli v neg rfl]
        | wire i neg =>
          simp only [BRef.ltBound] at hr
          simp only [evalRef, ih i hr (hwi i neg rfl)]
      unfold evalGate
      rw [href _ ha hcl.1 (fun v neg hv => hagree v (Or.inr ⟨j, hj_live, hj, Or.inl ⟨neg, hv⟩⟩)),
          href _ hb hcl.2 (fun v neg hv => hagree v (Or.inr ⟨j, hj_live, hj, Or.inr ⟨neg, hv⟩⟩))]
  unfold BCircuit.eval
  cases ho : D.out with
  | const c => rfl
  | lit v neg => simp [evalRef, hagree v (Or.inl ⟨neg, ho⟩)]
  | wire i neg =>
    have hi_live : i ∈ liveSet D := by
      unfold liveSet
      apply reachStep_subset
      simp [ho]
    simp only [evalRef, hwire i hi_live]

lemma active_vars_le (D : BCircuit) (hD : D.WF) (A : Finset (Fin 9))
    (hA : ∀ v ∈ A, ∃ x y : Fin 9 → Bool, (∀ u, u ≠ v → x u = y u) ∧ D.eval x ≠ D.eval y) :
    A.card ≤ D.gates.length + 1 := by
  classical
  let L := liveSet D
  have hL_lt : ∀ j ∈ L, j < D.gates.length := by
    apply reachStep_bound D.gates hD.1 D.gates.length le_rfl
    intro i hi
    cases h : D.out with
    | const _ => simp [h] at hi
    | lit _ _ => simp [h] at hi
    | wire idx _ =>
      rw [h] at hi; simp only [Finset.mem_singleton] at hi; subst hi
      have ho := hD.2; rw [h] at ho; exact ho
  have hL_sub : L ⊆ Finset.range D.gates.length :=
    fun j hj => Finset.mem_range.mpr (hL_lt j hj)
  have hL_le : L.card ≤ D.gates.length :=
    (Finset.card_le_card hL_sub).trans (by simp)
  let slots : Finset (Option (ℕ × Bool)) :=
    insert none ((L ×ˢ (Finset.univ : Finset Bool)).image some)
  have hslots_card : slots.card ≤ 2 * L.card + 1 := by
    calc slots.card ≤ ((L ×ˢ (Finset.univ : Finset Bool)).image some).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ (L ×ˢ (Finset.univ : Finset Bool)).card + 1 :=
          Nat.add_le_add_right Finset.card_image_le 1
      _ = 2 * L.card + 1 := by simp [Finset.card_product, Nat.mul_comm]
  have hw_slot : ∀ i ∈ L, ∃ s ∈ slots, ∃ neg, slotRef D s = .wire i neg := by
    intro i hi
    rcases reachStep_parent D.gates hD.1 D.gates.length le_rfl _ i hi with hinit | ⟨k, hkL, hklt, _, hread⟩
    · cases ho : D.out with
      | const _ => simp [ho] at hinit
      | lit _ _ => simp [ho] at hinit
      | wire idx neg =>
        rw [ho] at hinit; simp only [Finset.mem_singleton] at hinit; subst hinit
        exact ⟨none, Finset.mem_insert_self _ _, neg, ho⟩
    · have hgk : D.gates.getD k ⟨false, .const false, .const false⟩ = D.gates[k]'hklt :=
        getD_eq_getElem_of_lt D.gates _ k hklt
      rcases hread with ⟨neg, hae⟩ | ⟨neg, hbe⟩
      · refine ⟨some (k, false), Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨(k, false), Finset.mem_product.mpr ⟨hkL, Finset.mem_univ _⟩, rfl⟩), neg, ?_⟩
        simp only [slotRef, hgk, hae]
      · refine ⟨some (k, true), Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨(k, true), Finset.mem_product.mpr ⟨hkL, Finset.mem_univ _⟩, rfl⟩), neg, ?_⟩
        simp only [slotRef, hgk, hbe]
  have hv_slot : ∀ v ∈ A, ∃ s ∈ slots, ∃ neg, slotRef D s = .lit v neg := by
    intro v hv
    by_contra hno
    obtain ⟨x, y, hxy, hne⟩ := hA v hv
    apply hne
    apply liveSet_eval_eq D hD x y
    intro u hu
    by_cases huv : u = v
    · subst huv
      exfalso
      rcases hu with ⟨neg, ho⟩ | ⟨j, hjL, hjlt, hread⟩
      · exact hno ⟨none, Finset.mem_insert_self _ _, neg, ho⟩
      · have hgj : D.gates.getD j ⟨false, .const false, .const false⟩ = D.gates[j]'hjlt :=
          getD_eq_getElem_of_lt D.gates _ j hjlt
        rcases hread with ⟨neg, hae⟩ | ⟨neg, hbe⟩
        · exact hno ⟨some (j, false), Finset.mem_insert_of_mem (Finset.mem_image.mpr
            ⟨(j, false), Finset.mem_product.mpr ⟨hjL, Finset.mem_univ _⟩, rfl⟩), neg, by simp only [slotRef, hgj, hae]⟩
        · exact hno ⟨some (j, true), Finset.mem_insert_of_mem (Finset.mem_image.mpr
            ⟨(j, true), Finset.mem_product.mpr ⟨hjL, Finset.mem_univ _⟩, rfl⟩), neg, by simp only [slotRef, hgj, hbe]⟩
    · exact hxy u huv
  let f : (L ⊕ A) → slots := fun z =>
    match z with
    | Sum.inl ⟨i, hi⟩ => ⟨Classical.choose (hw_slot i hi), (Classical.choose_spec (hw_slot i hi)).1⟩
    | Sum.inr ⟨v, hv⟩ => ⟨Classical.choose (hv_slot v hv), (Classical.choose_spec (hv_slot v hv)).1⟩
  have hfinj : Function.Injective f := by
    intro z1 z2 heq
    have hval : (f z1).val = (f z2).val := congrArg Subtype.val heq
    cases z1 with
    | inl i1 =>
      obtain ⟨_, n1, hr1⟩ := Classical.choose_spec (hw_slot i1.val i1.property)
      cases z2 with
      | inl i2 =>
        obtain ⟨_, n2, hr2⟩ := Classical.choose_spec (hw_slot i2.val i2.property)
        change Classical.choose (hw_slot i1.val i1.property) = Classical.choose (hw_slot i2.val i2.property) at hval
        rw [hval, hr2] at hr1
        exact congrArg Sum.inl (Subtype.ext (BRef.wire.inj hr1).1.symm)
      | inr v2 =>
        obtain ⟨_, n2, hr2⟩ := Classical.choose_spec (hv_slot v2.val v2.property)
        change Classical.choose (hw_slot i1.val i1.property) = Classical.choose (hv_slot v2.val v2.property) at hval
        rw [hval, hr2] at hr1
        exact BRef.noConfusion hr1
    | inr v1 =>
      obtain ⟨_, n1, hr1⟩ := Classical.choose_spec (hv_slot v1.val v1.property)
      cases z2 with
      | inl i2 =>
        obtain ⟨_, n2, hr2⟩ := Classical.choose_spec (hw_slot i2.val i2.property)
        change Classical.choose (hv_slot v1.val v1.property) = Classical.choose (hw_slot i2.val i2.property) at hval
        rw [hval, hr2] at hr1
        exact BRef.noConfusion hr1
      | inr v2 =>
        obtain ⟨_, n2, hr2⟩ := Classical.choose_spec (hv_slot v2.val v2.property)
        change Classical.choose (hv_slot v1.val v1.property) = Classical.choose (hv_slot v2.val v2.property) at hval
        rw [hval, hr2] at hr1
        exact congrArg Sum.inr (Subtype.ext (BRef.lit.inj hr1).1.symm)
  have hcard := Fintype.card_le_of_injective f hfinj
  simp only [Fintype.card_sum, Fintype.card_coe] at hcard
  omega

lemma evalWires_const_of_no_var (D : BCircuit) (hD : D.WF) (v : Fin 9)
    (hno : ∀ j : ℕ, (hj : j < D.gates.length) → ¬ gateReadsVar v (D.gates[j]'hj))
    (x y : Fin 9 → Bool) (hxy : ∀ u, u ≠ v → x u = y u) :
    ∀ j < D.gates.length, (evalWires x D.gates).getD j false = (evalWires y D.gates).getD j false := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    obtain ⟨ha, hb⟩ := hD.1 j hj
    rw [evalWires_getD_at x D.gates j hj ha hb, evalWires_getD_at y D.gates j hj ha hb]
    have hno_j := hno j hj
    have href : ∀ r : BRef, r.ltBound j → (∀ neg, r ≠ .lit v neg) →
        evalRef x (evalWires x D.gates) r = evalRef y (evalWires y D.gates) r := by
      intro r hr hnv
      cases r with
      | const _ => rfl
      | lit u neg =>
        have huv : u ≠ v := fun h => hnv neg (by rw [h])
        simp [evalRef, hxy u huv]
      | wire i neg =>
        simp only [BRef.ltBound] at hr
        simp only [evalRef, ih i hr (by omega)]
    unfold evalGate
    rw [href _ ha (fun neg h => hno_j (Or.inl ⟨neg, h⟩)),
        href _ hb (fun neg h => hno_j (Or.inr ⟨neg, h⟩))]

lemma evalWires_dead_wire (D : BCircuit) (hD : D.WF) (v : Fin 9) (j : ℕ) (_hj : j < D.gates.length)
    (hno_var : ∀ k : ℕ, (hk : k < D.gates.length) → k ≠ j → ¬ gateReadsVar v (D.gates[k]'hk))
    (hno_read : ∀ k : ℕ, (hk : k < D.gates.length) → ¬ gateReadsWire j (D.gates[k]'hk))
    (x y : Fin 9 → Bool) (hxy : ∀ u, u ≠ v → x u = y u) :
    ∀ k < D.gates.length, k ≠ j →
      (evalWires x D.gates).getD k false = (evalWires y D.gates).getD k false := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hkj
    obtain ⟨ha, hb⟩ := hD.1 k hk
    rw [evalWires_getD_at x D.gates k hk ha hb, evalWires_getD_at y D.gates k hk ha hb]
    have hnv := hno_var k hk hkj
    have hnr := hno_read k hk
    have href : ∀ r : BRef, r.ltBound k → (∀ neg, r ≠ .lit v neg) → (∀ neg, r ≠ .wire j neg) →
        evalRef x (evalWires x D.gates) r = evalRef y (evalWires y D.gates) r := by
      intro r hr hv' hw'
      cases r with
      | const _ => rfl
      | lit u neg =>
        have huv : u ≠ v := fun h => hv' neg (by rw [h])
        simp [evalRef, hxy u huv]
      | wire i neg =>
        simp only [BRef.ltBound] at hr
        have hij : i ≠ j := fun h => hw' neg (by rw [h])
        simp only [evalRef, ih i hr (by omega) hij]
    unfold evalGate
    rw [href _ ha (fun neg h => hnv (Or.inl ⟨neg, h⟩)) (fun neg h => hnr (Or.inl ⟨neg, h⟩)),
        href _ hb (fun neg h => hnv (Or.inr ⟨neg, h⟩)) (fun neg h => hnr (Or.inr ⟨neg, h⟩))]

lemma two_gate_elim (D : BCircuit) (hD : D.WF) (v : Fin 9)
    (hdep : ∃ x y : Fin 9 → Bool, (∀ u, u ≠ v → x u = y u) ∧ D.eval x ≠ D.eval y)
    (hnc : ∀ b : Bool, ∃ x y : Fin 9 → Bool, x v = b ∧ y v = b ∧ D.eval x ≠ D.eval y) :
    ∃ b : Bool, (D.restrict v b).gates.length + 2 ≤ D.gates.length := by
  classical
  let R := (Finset.range D.gates.length).filter fun j =>
    ∃ hj : j < D.gates.length, gateReadsVar v (D.gates[j]'hj)
  by_cases hR2 : 2 ≤ R.card
  · obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < R.card)
    obtain ⟨hj1_lt, hr1⟩ := (Finset.mem_filter.mp hj1).2
    obtain ⟨hj2_lt, hr2⟩ := (Finset.mem_filter.mp hj2).2
    refine ⟨false, ?_⟩
    have hinv := (restrictState_inv v false D.gates hD.1).2.2.2.2
    have hcnt : 2 ≤ (List.range D.gates.length).countP (isDroppedRestrict v false D.gates) := by
      apply countP_two_le (List.range D.gates.length) _ j1 j2 List.nodup_range
        (List.mem_range.mpr hj1_lt) (List.mem_range.mpr hj2_lt) hne
      · have hg1 : D.gates.getD j1 ⟨false, .const false, .const false⟩ = D.gates[j1]'hj1_lt :=
          getD_eq_getElem_of_lt D.gates _ j1 hj1_lt
        simp only [isDroppedRestrict, hg1, Bool.or_eq_true]
        rcases hr1 with ⟨neg, hae⟩ | ⟨neg, hbe⟩
        · left; simp [hae, substRef, BRef.isConst]
        · right; simp [hbe, substRef, BRef.isConst]
      · have hg2 : D.gates.getD j2 ⟨false, .const false, .const false⟩ = D.gates[j2]'hj2_lt :=
          getD_eq_getElem_of_lt D.gates _ j2 hj2_lt
        simp only [isDroppedRestrict, hg2, Bool.or_eq_true]
        rcases hr2 with ⟨neg, hae⟩ | ⟨neg, hbe⟩
        · left; simp [hae, substRef, BRef.isConst]
        · right; simp [hbe, substRef, BRef.isConst]
    change (restrictState v false D.gates).1.length + 2 ≤ D.gates.length
    omega
  · by_cases hR0 : R.card = 0
    · exfalso
      have hno : ∀ j : ℕ, (hj : j < D.gates.length) → ¬ gateReadsVar v (D.gates[j]'hj) := by
        intro j hj hr
        have hm : j ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, ⟨hj, hr⟩⟩
        have := Finset.card_pos.mpr ⟨j, hm⟩
        omega
      cases ho : D.out with
      | const c =>
        obtain ⟨x, y, _, hne⟩ := hdep
        exact hne (by simp [BCircuit.eval, ho, evalRef])
      | lit u neg =>
        by_cases huv : u = v
        · subst huv
          obtain ⟨x, y, hxv, hyv, hne⟩ := hnc false
          exact hne (by simp [BCircuit.eval, ho, evalRef, hxv, hyv])
        · obtain ⟨x, y, hxy, hne⟩ := hdep
          exact hne (by simp [BCircuit.eval, ho, evalRef, hxy u huv])
      | wire idx neg =>
        have hidx : idx < D.gates.length := by have h := hD.2; rw [ho] at h; exact h
        obtain ⟨x, y, hxy, hne⟩ := hdep
        exact hne (by simp only [BCircuit.eval, ho, evalRef, evalWires_const_of_no_var D hD v hno x y hxy idx hidx])
    · have hR1 : R.card = 1 := by omega
      obtain ⟨j, hRj⟩ := Finset.card_eq_one.mp hR1
      have hj_mem : j ∈ R := by rw [hRj]; simp
      obtain ⟨hj_lt, hr_j⟩ := (Finset.mem_filter.mp hj_mem).2
      have hno_other : ∀ k : ℕ, (hk : k < D.gates.length) → k ≠ j → ¬ gateReadsVar v (D.gates[k]'hk) := by
        intro k hk hkj hrk
        have hm : k ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, ⟨hk, hrk⟩⟩
        rw [hRj, Finset.mem_singleton] at hm
        exact hkj hm
      have hctrl : ∃ b : Bool, ∃ c : Bool,
          (restrictState v b (D.gates.take (j + 1))).2.getD j (.const false) = .const c := by
        have hsplit : D.gates.take (j + 1) = D.gates.take j ++ [D.gates[j]'hj_lt] :=
          List.take_succ_eq_append_getElem hj_lt
        rcases hr_j with ⟨neg, hae⟩ | ⟨neg, hbe⟩
        · refine ⟨xor (D.gates[j]'hj_lt).isOr neg, (D.gates[j]'hj_lt).isOr, ?_⟩
          rw [hsplit, restrictState_snoc]
          have hsl : (restrictState v (xor (D.gates[j]'hj_lt).isOr neg) (D.gates.take j)).2.length = j := by
            rw [restrictState_env_length]; simp; omega
          change ((restrictState v _ (D.gates.take j)).2 ++ [_]).getD j (.const false) = _
          rw [getD_append_last _ _ _ j hsl]
          have hsa : substRef v (xor (D.gates[j]'hj_lt).isOr neg)
              (restrictState v (xor (D.gates[j]'hj_lt).isOr neg) (D.gates.take j)).2 (D.gates[j]'hj_lt).a =
              .const (D.gates[j]'hj_lt).isOr := by
            rw [hae]; simp only [substRef, ↓reduceIte]
            cases (D.gates[j]'hj_lt).isOr <;> cases neg <;> rfl
          rw [hsa]
          cases (D.gates[j]'hj_lt).isOr <;> rfl
        · refine ⟨xor (D.gates[j]'hj_lt).isOr neg, (D.gates[j]'hj_lt).isOr, ?_⟩
          rw [hsplit, restrictState_snoc]
          have hsl : (restrictState v (xor (D.gates[j]'hj_lt).isOr neg) (D.gates.take j)).2.length = j := by
            rw [restrictState_env_length]; simp; omega
          change ((restrictState v _ (D.gates.take j)).2 ++ [_]).getD j (.const false) = _
          rw [getD_append_last _ _ _ j hsl]
          have hsb : substRef v (xor (D.gates[j]'hj_lt).isOr neg)
              (restrictState v (xor (D.gates[j]'hj_lt).isOr neg) (D.gates.take j)).2 (D.gates[j]'hj_lt).b =
              .const (D.gates[j]'hj_lt).isOr := by
            rw [hbe]; simp only [substRef, ↓reduceIte]
            cases (D.gates[j]'hj_lt).isOr <;> cases neg <;> rfl
          rw [hsb]
          cases substRef v (xor (D.gates[j]'hj_lt).isOr neg)
              (restrictState v (xor (D.gates[j]'hj_lt).isOr neg) (D.gates.take j)).2 (D.gates[j]'hj_lt).a with
          | const c' => cases (D.gates[j]'hj_lt).isOr <;> cases c' <;> rfl
          | lit _ _ => cases (D.gates[j]'hj_lt).isOr <;> rfl
          | wire _ _ => cases (D.gates[j]'hj_lt).isOr <;> rfl
      obtain ⟨b, c, hconst_j⟩ := hctrl
      by_cases hread_j : ∃ k : ℕ, ∃ hk : k < D.gates.length, j < k ∧ gateReadsWire j (D.gates[k]'hk)
      · obtain ⟨k, hk_lt, hjk, hrk⟩ := hread_j
        refine ⟨b, ?_⟩
        have hinv := (restrictState_inv v b D.gates hD.1).2.2.2.2
        have hcnt : 2 ≤ (List.range D.gates.length).countP (isDroppedRestrict v b D.gates) := by
          apply countP_two_le (List.range D.gates.length) _ j k List.nodup_range
            (List.mem_range.mpr hj_lt) (List.mem_range.mpr hk_lt) (by omega)
          · have hgj : D.gates.getD j ⟨false, .const false, .const false⟩ = D.gates[j]'hj_lt :=
              getD_eq_getElem_of_lt D.gates _ j hj_lt
            simp only [isDroppedRestrict, hgj, Bool.or_eq_true]
            rcases hr_j with ⟨neg, hae⟩ | ⟨neg, hbe⟩
            · left; simp [hae, substRef, BRef.isConst]
            · right; simp [hbe, substRef, BRef.isConst]
          · have hgk : D.gates.getD k ⟨false, .const false, .const false⟩ = D.gates[k]'hk_lt :=
              getD_eq_getElem_of_lt D.gates _ k hk_lt
            have henv_jk : (restrictState v b (D.gates.take k)).2.getD j (.const false) = .const c := by
              have h1 := restrictState_env_take v b (D.gates.take k) (j + 1) (by simp; omega) j (by omega)
              rw [List.take_take, Nat.min_eq_left (by omega)] at h1
              rw [h1, hconst_j]
            simp only [isDroppedRestrict, hgk, Bool.or_eq_true]
            rcases hrk with ⟨neg, hae⟩ | ⟨neg, hbe⟩
            · left; simp only [hae, substRef, henv_jk]; cases neg <;> rfl
            · right; simp only [hbe, substRef, henv_jk]; cases neg <;> rfl
        change (restrictState v b D.gates).1.length + 2 ≤ D.gates.length
        omega
      · exfalso
        have hno_read : ∀ k : ℕ, (hk : k < D.gates.length) → ¬ gateReadsWire j (D.gates[k]'hk) := by
          intro k hk hrk
          have hjk : j < k := by
            obtain ⟨ha, hb⟩ := hD.1 k hk
            rcases hrk with ⟨neg, hae⟩ | ⟨neg, hbe⟩
            · rw [hae] at ha; exact ha
            · rw [hbe] at hb; exact hb
          exact hread_j ⟨k, hk, hjk, hrk⟩
        cases ho : D.out with
        | const _ =>
          obtain ⟨x, y, _, hne⟩ := hdep
          exact hne (by simp [BCircuit.eval, ho, evalRef])
        | lit u neg =>
          by_cases huv : u = v
          · subst huv
            obtain ⟨x, y, hxv, hyv, hne⟩ := hnc false
            exact hne (by simp [BCircuit.eval, ho, evalRef, hxv, hyv])
          · obtain ⟨x, y, hxy, hne⟩ := hdep
            exact hne (by simp [BCircuit.eval, ho, evalRef, hxy u huv])
        | wire idx neg =>
          by_cases hidx : idx = j
          · subst hidx
            obtain ⟨x, y, hxv, hyv, hne⟩ := hnc b
            have hinv := (restrictState_inv v b D.gates hD.1).2.2.2.1
            have henv_j : (restrictState v b D.gates).2.getD idx (.const false) = .const c := by
              rw [restrictState_env_take v b D.gates (idx + 1) (by omega) idx (by omega), hconst_j]
            have hx : (evalWires x D.gates).getD idx false = c := by
              have h1 := hinv x hxv idx hj_lt
              rw [henv_j] at h1
              exact h1.symm
            have hy : (evalWires y D.gates).getD idx false = c := by
              have h1 := hinv y hyv idx hj_lt
              rw [henv_j] at h1
              exact h1.symm
            exact hne (by simp only [BCircuit.eval, ho, evalRef, hx, hy])
          · have hidx_lt : idx < D.gates.length := by have h := hD.2; rw [ho] at h; exact h
            obtain ⟨x, y, hxy, hne⟩ := hdep
            exact hne (by simp only [BCircuit.eval, ho, evalRef,
              evalWires_dead_wire D hD v j hj_lt hno_other hno_read x y hxy idx hidx_lt hidx])

def compileStep (st : List BGate × List BRef) (g : Gate) : List BGate × List BRef :=
  match g.op with
  | .not =>
    let ra := st.2.getD (g.inputs.getD 0 0) (.const false)
    (st.1, st.2 ++ [ra.flip])
  | .and =>
    let ra := st.2.getD (g.inputs.getD 0 0) (.const false)
    let rb := st.2.getD (g.inputs.getD 1 0) (.const false)
    let (gs', r') := foldBin false ra rb st.1
    (gs', st.2 ++ [r'])
  | .or =>
    let ra := st.2.getD (g.inputs.getD 0 0) (.const false)
    let rb := st.2.getD (g.inputs.getD 1 0) (.const false)
    let (gs', r') := foldBin true ra rb st.1
    (gs', st.2 ++ [r'])
  | _ => (st.1, st.2 ++ [.const false])

def initEnv0 : List BRef :=
  [.const true, .lit 1 false, .lit 2 false, .lit 3 false, .lit 4 false,
   .lit 5 false, .lit 6 false, .lit 7 false, .lit 8 false]

def compileState (gs : List Gate) : List BGate × List BRef :=
  gs.foldl compileStep ([], initEnv0)

def compileCircuit (C : Circuit) : BCircuit :=
  let st := compileState C.gates
  ⟨st.1, st.2.getD C.output (.const false)⟩

def runStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl runStep x := rfl

lemma foldl_runStep_len (gs : List Gate) (w : List Bool) :
    (gs.foldl runStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [runStep]; omega

lemma compileState_snoc (gs : List Gate) (g : Gate) :
    compileState (gs ++ [g]) = compileStep (compileState gs) g := by
  simp [compileState, List.foldl_append]

lemma compileState_env_len (gs : List Gate) :
    (compileState gs).2.length = 9 + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [compileState_snoc]
    cases h : g.op <;> simp [compileStep, h, ih] <;> omega

lemma compileState_env_take (gs : List Gate) (j : ℕ) (hj : j ≤ gs.length) :
    ∀ i < 9 + j, (compileState gs).2.getD i (.const false) =
      (compileState (gs.take j)).2.getD i (.const false) := by
  induction gs using List.reverseRecOn generalizing j with
  | nil =>
    intro i hi; simp at hj; subst hj; rfl
  | append_singleton gs g ih =>
    intro i hi
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · have hjle : j ≤ gs.length := Nat.lt_succ_iff.mp hlt
      rw [List.take_append_of_le_length hjle, compileState_snoc]
      have hsl := compileState_env_len gs
      have hget : (compileStep (compileState gs) g).2.getD i (.const false) =
          (compileState gs).2.getD i (.const false) := by
        cases h : g.op <;> simp only [compileStep, h] <;> exact getD_append_lt _ _ _ i (by omega)
      rw [hget]
      exact ih j hjle i hi
    · rw [show gs.length + 1 = (gs ++ [g]).length by simp, List.take_length]

def isDroppedGate (gs : List Gate) (j : ℕ) : Bool :=
  let stj := compileState (gs.take j)
  let g := gs.getD j ⟨.or, []⟩
  match g.op with
  | .not => true
  | .and => (stj.2.getD (g.inputs.getD 0 0) (.const false)).isConst ||
            (stj.2.getD (g.inputs.getD 1 0) (.const false)).isConst
  | .or => (stj.2.getD (g.inputs.getD 0 0) (.const false)).isConst ||
           (stj.2.getD (g.inputs.getD 1 0) (.const false)).isConst
  | _ => true

lemma initEnv0_eval (x : Fin 9 → Bool) (hx0 : x 0 = true) (i : ℕ) (hi : i < 9) :
    evalRef x (evalWires x []) (initEnv0.getD i (.const false)) = (List.ofFn x).getD i false := by
  have hget : (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
    rw [getD_eq_getElem_of_lt _ _ i (by simp; exact hi), List.getElem_ofFn]
  rw [hget]
  match i, hi with
  | 0, _ => simp [initEnv0, evalRef, hx0]
  | 1, _ => simp [initEnv0, evalRef]
  | 2, _ => simp [initEnv0, evalRef]
  | 3, _ => simp [initEnv0, evalRef]
  | 4, _ => simp [initEnv0, evalRef]
  | 5, _ => simp [initEnv0, evalRef]
  | 6, _ => simp [initEnv0, evalRef]
  | 7, _ => simp [initEnv0, evalRef]
  | 8, _ => simp [initEnv0, evalRef]

lemma compileState_inv (gs : List Gate)
    (hnf : ∀ j : ℕ, (hj : j < gs.length) →
      ((gs[j]).op = .not ∧ ∃ a, a < 9 + j ∧ (gs[j]).inputs = [a]) ∨
      (((gs[j]).op = .and ∨ (gs[j]).op = .or) ∧
        ∃ a b, a < b ∧ b < 9 + j ∧ (gs[j]).inputs = [a, b])) :
    let st := compileState gs
    (∀ j : ℕ, (hj : j < st.1.length) → (st.1[j]).a.ltBound j ∧ (st.1[j]).b.ltBound j) ∧
    (∀ r ∈ st.2, r.ltBound st.1.length) ∧
    (∀ x : Fin 9 → Bool, x 0 = true →
      ∀ i < 9 + gs.length, evalRef x (evalWires x st.1) (st.2.getD i (.const false)) =
        (gs.foldl runStep (List.ofFn x)).getD i false) ∧
    st.1.length + (List.range gs.length).countP (isDroppedGate gs) ≤ gs.length := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun j hj => by simp [compileState] at hj,
      fun r hr => by
        simp only [compileState, List.foldl_nil, initEnv0, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial,
      fun x hx0 i hi => initEnv0_eval x hx0 i (by simpa using hi),
      by simp [compileState]⟩
  | append_singleton gs g ih =>
    have hnf_pre : ∀ j : ℕ, (hj : j < gs.length) →
        ((gs[j]).op = .not ∧ ∃ a, a < 9 + j ∧ (gs[j]).inputs = [a]) ∨
        (((gs[j]).op = .and ∨ (gs[j]).op = .or) ∧
          ∃ a b, a < b ∧ b < 9 + j ∧ (gs[j]).inputs = [a, b]) := by
      intro j hj
      have h := hnf j (by simp; omega)
      simpa [List.getElem_append_left hj] using h
    have hnf_g := hnf gs.length (by simp)
    simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero] at hnf_g
    obtain ⟨hwf1, hlt, heval, hcnt⟩ := ih hnf_pre
    rw [compileState_snoc]
    set st := compileState gs
    have hsl : st.2.length = 9 + gs.length := compileState_env_len gs
    have hcongr_drop : (List.range gs.length).countP (isDroppedGate (gs ++ [g])) =
        (List.range gs.length).countP (isDroppedGate gs) := by
      rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
      congr 1
      apply List.filter_congr
      intro j hj
      have hjlt : j < gs.length := List.mem_range.mp hj
      have ht : (gs ++ [g]).take j = gs.take j := List.take_append_of_le_length (le_of_lt hjlt)
      have hg : (gs ++ [g]).getD j ⟨.or, []⟩ = gs.getD j ⟨.or, []⟩ := getD_append_lt _ _ _ j hjlt
      simp only [isDroppedGate, ht, hg]
    have htlast : (gs ++ [g]).take gs.length = gs := by simp
    have hglast : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := getD_append_last _ _ _ gs.length rfl
    have hget_lt : ∀ a < 9 + gs.length, (st.2.getD a (.const false)).ltBound st.1.length := by
      intro a ha
      rw [List.getD_eq_getElem?_getD]
      cases h : st.2[a]? with
      | none => trivial
      | some r => exact hlt r (List.mem_of_getElem? h)
    have hrun_len : ∀ x : Fin 9 → Bool, (gs.foldl runStep (List.ofFn x)).length = 9 + gs.length := by
      intro x; rw [foldl_runStep_len]; simp
    rcases hnf_g with ⟨hop, a, ha, hins⟩ | ⟨hop, a, b, hab, hb, hins⟩
    · have hra : (st.2.getD a (.const false)).ltBound st.1.length := hget_lt a ha
      have hcs : compileStep st g = (st.1, st.2 ++ [(st.2.getD a (.const false)).flip]) := by
        simp [compileStep, hop, hins]
      rw [hcs]
      refine ⟨hwf1, ?_, ?_, ?_⟩
      · intro r hr
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact hlt r hr
        · exact BRef.ltBound_flip hra
      · intro x hx0 i hi
        simp only [List.length_append, List.length_singleton] at hi
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rcases (by omega : i < 9 + gs.length ∨ i = 9 + gs.length) with hlt_i | rfl
        · rw [getD_append_lt _ _ _ i (by omega), heval x hx0 i hlt_i]
          exact (getD_append_lt _ _ _ i (by rw [hrun_len]; omega)).symm
        · rw [getD_append_last _ _ _ (9 + gs.length) hsl, evalRef_flip, heval x hx0 a ha]
          rw [show runStep _ _ = _ ++ _ from rfl, getD_append_last _ _ _ (9 + gs.length) (hrun_len x)]
          simp [hop, hins, GateOp.eval]
      · rw [List.length_append, List.length_singleton, List.range_succ, List.countP_append,
            List.countP_singleton, hcongr_drop]
        simp only [isDroppedGate, hglast, hop, ↓reduceIte]
        omega
    · have ha : a < 9 + gs.length := by omega
      have hra : (st.2.getD a (.const false)).ltBound st.1.length := hget_lt a ha
      have hrb : (st.2.getD b (.const false)).ltBound st.1.length := hget_lt b hb
      rcases hop with hop | hop
      · have hfb := fun x => foldBin_sound x false (st.2.getD a (.const false)) (st.2.getD b (.const false)) st.1 hra hrb
        have hfb0 := hfb (fun _ => false)
        set res := foldBin false (st.2.getD a (.const false)) (st.2.getD b (.const false)) st.1
        have hcs : compileStep st g = (res.1, st.2 ++ [res.2]) := by
          simp [compileStep, hop, hins, res]
        rw [hcs]
        refine ⟨fun j hj => hfb0.2.2.1 j hj hwf1, ?_, ?_, ?_⟩
        · intro r hr
          simp only [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact BRef.ltBound_mono (hlt r hr) hfb0.1.1
          · exact hfb0.2.2.2.1
        · intro x hx0 i hi
          simp only [List.length_append, List.length_singleton] at hi
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          rcases (by omega : i < 9 + gs.length ∨ i = 9 + gs.length) with hlt_i | rfl
          · rw [getD_append_lt _ _ _ i (by omega)]
            have hlt_r := hget_lt i hlt_i
            have hsame : evalRef x (evalWires x res.1) (st.2.getD i (.const false)) =
                evalRef x (evalWires x st.1) (st.2.getD i (.const false)) := by
              cases hr : st.2.getD i (.const false) with
              | const _ => rfl
              | lit _ _ => rfl
              | wire idx neg =>
                rw [hr] at hlt_r; simp only [BRef.ltBound] at hlt_r
                simp only [evalRef, (hfb x).2.2.2.2.2 idx hlt_r]
            rw [hsame, heval x hx0 i hlt_i]
            exact (getD_append_lt _ _ _ i (by rw [hrun_len]; omega)).symm
          · rw [getD_append_last _ _ _ (9 + gs.length) hsl, (hfb x).2.2.2.2.1]
            simp only [Bool.false_eq_true, ↓reduceIte, heval x hx0 a ha, heval x hx0 b hb]
            rw [show runStep _ _ = _ ++ _ from rfl, getD_append_last _ _ _ (9 + gs.length) (hrun_len x)]
            simp [hop, hins, GateOp.eval]
        · rw [List.length_append, List.length_singleton, List.range_succ, List.countP_append,
              List.countP_singleton, hcongr_drop]
          have hdl : isDroppedGate (gs ++ [g]) gs.length =
              ((st.2.getD a (.const false)).isConst || (st.2.getD b (.const false)).isConst) := by
            simp only [isDroppedGate, htlast, hglast, hop, hins, List.getD_cons_zero, List.getD_cons_succ]; rfl
          rw [hdl]
          dsimp only
          split_ifs with hc
          · have heq : res.1 = st.1 := hfb0.2.1 (Bool.or_eq_true_iff.mp hc)
            rw [heq]; omega
          · have hle : res.1.length ≤ st.1.length + 1 := hfb0.1.2
            omega
      · have hfb := fun x => foldBin_sound x true (st.2.getD a (.const false)) (st.2.getD b (.const false)) st.1 hra hrb
        have hfb0 := hfb (fun _ => false)
        set res := foldBin true (st.2.getD a (.const false)) (st.2.getD b (.const false)) st.1
        have hcs : compileStep st g = (res.1, st.2 ++ [res.2]) := by
          simp [compileStep, hop, hins, res]
        rw [hcs]
        refine ⟨fun j hj => hfb0.2.2.1 j hj hwf1, ?_, ?_, ?_⟩
        · intro r hr
          simp only [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact BRef.ltBound_mono (hlt r hr) hfb0.1.1
          · exact hfb0.2.2.2.1
        · intro x hx0 i hi
          simp only [List.length_append, List.length_singleton] at hi
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          rcases (by omega : i < 9 + gs.length ∨ i = 9 + gs.length) with hlt_i | rfl
          · rw [getD_append_lt _ _ _ i (by omega)]
            have hlt_r := hget_lt i hlt_i
            have hsame : evalRef x (evalWires x res.1) (st.2.getD i (.const false)) =
                evalRef x (evalWires x st.1) (st.2.getD i (.const false)) := by
              cases hr : st.2.getD i (.const false) with
              | const _ => rfl
              | lit _ _ => rfl
              | wire idx neg =>
                rw [hr] at hlt_r; simp only [BRef.ltBound] at hlt_r
                simp only [evalRef, (hfb x).2.2.2.2.2 idx hlt_r]
            rw [hsame, heval x hx0 i hlt_i]
            exact (getD_append_lt _ _ _ i (by rw [hrun_len]; omega)).symm
          · rw [getD_append_last _ _ _ (9 + gs.length) hsl, (hfb x).2.2.2.2.1]
            simp only [↓reduceIte, heval x hx0 a ha, heval x hx0 b hb]
            rw [show runStep _ _ = _ ++ _ from rfl, getD_append_last _ _ _ (9 + gs.length) (hrun_len x)]
            simp [hop, hins, GateOp.eval]
        · rw [List.length_append, List.length_singleton, List.range_succ, List.countP_append,
              List.countP_singleton, hcongr_drop]
          have hdl : isDroppedGate (gs ++ [g]) gs.length =
              ((st.2.getD a (.const false)).isConst || (st.2.getD b (.const false)).isConst) := by
            simp only [isDroppedGate, htlast, hglast, hop, hins, List.getD_cons_zero, List.getD_cons_succ]; rfl
          rw [hdl]
          dsimp only
          split_ifs with hc
          · have heq : res.1 = st.1 := hfb0.2.1 (Bool.or_eq_true_iff.mp hc)
            rw [heq]; omega
          · have hle : res.1.length ≤ st.1.length + 1 := hfb0.1.2
            omega

def mkIn (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Fin 9 → Bool
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4
  | ⟨5, _⟩ => b5
  | ⟨6, _⟩ => b6
  | ⟨7, _⟩ => b7
  | ⟨8, _⟩ => b8

lemma fin9_ne_cases {u v : Fin 9} {f g : Fin 9 → Bool} (hv : u ≠ v)
    (h0 : v ≠ 0 → f 0 = g 0) (h1 : v ≠ 1 → f 1 = g 1) (h2 : v ≠ 2 → f 2 = g 2)
    (h3 : v ≠ 3 → f 3 = g 3) (h4 : v ≠ 4 → f 4 = g 4) (h5 : v ≠ 5 → f 5 = g 5)
    (h6 : v ≠ 6 → f 6 = g 6) (h7 : v ≠ 7 → f 7 = g 7) (h8 : v ≠ 8 → f 8 = g 8) :
    f u = g u := by
  match u with
  | ⟨0, _⟩ => exact h0 hv.symm
  | ⟨1, _⟩ => exact h1 hv.symm
  | ⟨2, _⟩ => exact h2 hv.symm
  | ⟨3, _⟩ => exact h3 hv.symm
  | ⟨4, _⟩ => exact h4 hv.symm
  | ⟨5, _⟩ => exact h5 hv.symm
  | ⟨6, _⟩ => exact h6 hv.symm
  | ⟨7, _⟩ => exact h7 hv.symm
  | ⟨8, _⟩ => exact h8 hv.symm

lemma leaf_x4_false (b2 b6 : Bool) (D : BCircuit) (hD : D.WF)
    (heq : ∀ x : Fin 9 → Bool, x 0 = true → x 4 = false → x 2 = b2 → x 6 = b6 → D.eval x = pm3 x) :
    4 ≤ D.gates.length := by
  have hA : ({1, 3, 5, 7, 8} : Finset (Fin 9)).card ≤ D.gates.length + 1 := by
    apply active_vars_le D hD {1, 3, 5, 7, 8}
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · refine ⟨mkIn true false b2 true false false b6 false true,
              mkIn true true  b2 true false false b6 false true, ?_, ?_⟩
      · intro u hu; exact fin9_ne_cases hu (fun _ => rfl) (fun h => absurd rfl h) (fun _ => rfl)
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      · rw [heq _ rfl rfl rfl rfl, heq _ rfl rfl rfl rfl]; cases b2 <;> cases b6 <;> decide
    · refine ⟨mkIn true true b2 false false false b6 false true,
              mkIn true true b2 true  false false b6 false true, ?_, ?_⟩
      · intro u hu; exact fin9_ne_cases hu (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun h => absurd rfl h) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      · rw [heq _ rfl rfl rfl rfl, heq _ rfl rfl rfl rfl]; cases b2 <;> cases b6 <;> decide
    · refine ⟨mkIn true false b2 false false false b6 true false,
              mkIn true false b2 false false true  b6 true false, ?_, ?_⟩
      · intro u hu; exact fin9_ne_cases hu (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun _ => rfl) (fun _ => rfl) (fun h => absurd rfl h) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      · rw [heq _ rfl rfl rfl rfl, heq _ rfl rfl rfl rfl]; cases b2 <;> cases b6 <;> decide
    · refine ⟨mkIn true false b2 false false true b6 false false,
              mkIn true false b2 false false true b6 true  false, ?_, ?_⟩
      · intro u hu; exact fin9_ne_cases hu (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun h => absurd rfl h) (fun _ => rfl)
      · rw [heq _ rfl rfl rfl rfl, heq _ rfl rfl rfl rfl]; cases b2 <;> cases b6 <;> decide
    · refine ⟨mkIn true true b2 true false false b6 false false,
              mkIn true true b2 true false false b6 false true, ?_, ?_⟩
      · intro u hu; exact fin9_ne_cases hu (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun h => absurd rfl h)
      · rw [heq _ rfl rfl rfl rfl, heq _ rfl rfl rfl rfl]; cases b2 <;> cases b6 <;> decide
  have hc : ({1, 3, 5, 7, 8} : Finset (Fin 9)).card = 5 := by decide
  omega

lemma leaf_x4_true (b1 b3 : Bool) (D : BCircuit) (hD : D.WF)
    (heq : ∀ x : Fin 9 → Bool, x 0 = true → x 4 = true → x 1 = b1 → x 3 = b3 → D.eval x = pm3 x) :
    4 ≤ D.gates.length := by
  have hA : ({2, 5, 6, 7, 8} : Finset (Fin 9)).card ≤ D.gates.length + 1 := by
    apply active_vars_le D hD {2, 5, 6, 7, 8}
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · refine ⟨mkIn true b1 false b3 true false true false false,
              mkIn true b1 true  b3 true false true false false, ?_, ?_⟩
      · intro u hu; exact fin9_ne_cases hu (fun _ => rfl) (fun _ => rfl) (fun h => absurd rfl h)
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      · rw [heq _ rfl rfl rfl rfl, heq _ rfl rfl rfl rfl]; cases b1 <;> cases b3 <;> decide
    · refine ⟨mkIn true b1 false b3 true false false true false,
              mkIn true b1 false b3 true true  false true false, ?_, ?_⟩
      · intro u hu; exact fin9_ne_cases hu (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun _ => rfl) (fun _ => rfl) (fun h => absurd rfl h) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      · rw [heq _ rfl rfl rfl rfl, heq _ rfl rfl rfl rfl]; cases b1 <;> cases b3 <;> decide
    · refine ⟨mkIn true b1 true b3 true false false false false,
              mkIn true b1 true b3 true false true  false false, ?_, ?_⟩
      · intro u hu; exact fin9_ne_cases hu (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun h => absurd rfl h) (fun _ => rfl) (fun _ => rfl)
      · rw [heq _ rfl rfl rfl rfl, heq _ rfl rfl rfl rfl]; cases b1 <;> cases b3 <;> decide
    · refine ⟨mkIn true b1 false b3 true true false false false,
              mkIn true b1 false b3 true true false true  false, ?_, ?_⟩
      · intro u hu; exact fin9_ne_cases hu (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun h => absurd rfl h) (fun _ => rfl)
      · rw [heq _ rfl rfl rfl rfl, heq _ rfl rfl rfl rfl]; cases b1 <;> cases b3 <;> decide
    · refine ⟨mkIn true b1 false b3 true false false false false,
              mkIn true b1 false b3 true false false false true, ?_, ?_⟩
      · intro u hu; exact fin9_ne_cases hu (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun h => absurd rfl h)
      · rw [heq _ rfl rfl rfl rfl, heq _ rfl rfl rfl rfl]; cases b1 <;> cases b3 <;> decide
  have hc : ({2, 5, 6, 7, 8} : Finset (Fin 9)).card = 5 := by decide
  omega

lemma h8_lower_bound (D : BCircuit) (hD : D.WF)
    (heq : ∀ x : Fin 9 → Bool, x 0 = true → D.eval x = pm3 x) :
    10 ≤ D.gates.length := by
  have ⟨b4, hb4⟩ := two_gate_elim D hD 4
    ⟨mkIn true false false false false false false false true,
     mkIn true false false false true  false false false true,
     fun u hu => fin9_ne_cases hu (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
       (fun h => absurd rfl h) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
     by rw [heq _ rfl, heq _ rfl]; decide⟩
    (fun b => ⟨mkIn true false false false b false false false false,
               mkIn true false false false b true  false true  false, rfl, rfl,
               by rw [heq _ rfl, heq _ rfl]; cases b <;> decide⟩)
  set D1 := D.restrict 4 b4
  have hD1 : D1.WF := restrict_wf D hD 4 b4
  have heq1 : ∀ x, x 0 = true → x 4 = b4 → D1.eval x = pm3 x :=
    fun x h0 h4 => (restrict_eval D hD 4 b4 x h4).trans (heq x h0)
  cases b4 with
  | false =>
    have ⟨b2, hb2⟩ := two_gate_elim D1 hD1 2
      ⟨mkIn true false false true false false false true false,
       mkIn true false true  true false false false true false,
       fun u hu => fin9_ne_cases hu (fun _ => rfl) (fun _ => rfl) (fun h => absurd rfl h)
         (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
       by rw [heq1 _ rfl rfl, heq1 _ rfl rfl]; decide⟩
      (fun b => ⟨mkIn true false b false false false false false false,
                 mkIn true false b false false true  false true  false, rfl, rfl,
                 by rw [heq1 _ rfl rfl, heq1 _ rfl rfl]; cases b <;> decide⟩)
    set D2 := D1.restrict 2 b2
    have hD2 : D2.WF := restrict_wf D1 hD1 2 b2
    have heq2 : ∀ x, x 0 = true → x 4 = false → x 2 = b2 → D2.eval x = pm3 x :=
      fun x h0 h4 h2 => (restrict_eval D1 hD1 2 b2 x h2).trans (heq1 x h0 h4)
    have ⟨b6, hb6⟩ := two_gate_elim D2 hD2 6
      ⟨mkIn true true b2 false false true false false false,
       mkIn true true b2 false false true true  false false,
       fun u hu => fin9_ne_cases hu (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
         (fun _ => rfl) (fun _ => rfl) (fun h => absurd rfl h) (fun _ => rfl) (fun _ => rfl),
       by rw [heq2 _ rfl rfl rfl, heq2 _ rfl rfl rfl]; cases b2 <;> decide⟩
      (fun b => ⟨mkIn true false b2 false false false b false false,
                 mkIn true false b2 false false true  b true  false, rfl, rfl,
                 by rw [heq2 _ rfl rfl rfl, heq2 _ rfl rfl rfl]; cases b2 <;> cases b <;> decide⟩)
    set D3 := D2.restrict 6 b6
    have hD3 : D3.WF := restrict_wf D2 hD2 6 b6
    have heq3 : ∀ x, x 0 = true → x 4 = false → x 2 = b2 → x 6 = b6 → D3.eval x = pm3 x :=
      fun x h0 h4 h2 h6 => (restrict_eval D2 hD2 6 b6 x h6).trans (heq2 x h0 h4 h2)
    have hleaf := leaf_x4_false b2 b6 D3 hD3 heq3
    omega
  | true =>
    have ⟨b1, hb1⟩ := two_gate_elim D1 hD1 1
      ⟨mkIn true false false false true true true false false,
       mkIn true true  false false true true true false false,
       fun u hu => fin9_ne_cases hu (fun _ => rfl) (fun h => absurd rfl h) (fun _ => rfl)
         (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
       by rw [heq1 _ rfl rfl, heq1 _ rfl rfl]; decide⟩
      (fun b => ⟨mkIn true b false false true false false false false,
                 mkIn true b false false true false false false true, rfl, rfl,
                 by rw [heq1 _ rfl rfl, heq1 _ rfl rfl]; cases b <;> decide⟩)
    set D2 := D1.restrict 1 b1
    have hD2 : D2.WF := restrict_wf D1 hD1 1 b1
    have heq2 : ∀ x, x 0 = true → x 4 = true → x 1 = b1 → D2.eval x = pm3 x :=
      fun x h0 h4 h1 => (restrict_eval D1 hD1 1 b1 x h1).trans (heq1 x h0 h4)
    have ⟨b3, hb3⟩ := two_gate_elim D2 hD2 3
      ⟨mkIn true b1 true false true false false true false,
       mkIn true b1 true true  true false false true false,
       fun u hu => fin9_ne_cases hu (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
         (fun h => absurd rfl h) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
       by rw [heq2 _ rfl rfl rfl, heq2 _ rfl rfl rfl]; cases b1 <;> decide⟩
      (fun b => ⟨mkIn true b1 false b true false false false false,
                 mkIn true b1 false b true false false false true, rfl, rfl,
                 by rw [heq2 _ rfl rfl rfl, heq2 _ rfl rfl rfl]; cases b1 <;> cases b <;> decide⟩)
    set D3 := D2.restrict 3 b3
    have hD3 : D3.WF := restrict_wf D2 hD2 3 b3
    have heq3 : ∀ x, x 0 = true → x 4 = true → x 1 = b1 → x 3 = b3 → D3.eval x = pm3 x :=
      fun x h0 h4 h1 h3 => (restrict_eval D2 hD2 3 b3 x h3).trans (heq2 x h0 h4 h1)
    have hleaf := leaf_x4_true b1 b3 D3 hD3 heq3
    omega

theorem main : ¬ (∃ C : Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pm3 x) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = GateOp.not ∧ ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
        ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨GateOp.and, [0, 5]⟩) := by
  rintro ⟨C, _, hsz, hpm, hout, hnf_fin, _, hused, h0, h1⟩
  have hnf : ∀ j : ℕ, (hj : j < C.gates.length) →
      ((C.gates[j]).op = .not ∧ ∃ a, a < 9 + j ∧ (C.gates[j]).inputs = [a]) ∨
      (((C.gates[j]).op = .and ∨ (C.gates[j]).op = .or) ∧
        ∃ a b, a < b ∧ b < 9 + j ∧ (C.gates[j]).inputs = [a, b]) :=
    fun j hj => hnf_fin ⟨j, hj⟩
  cases hgs : C.gates with
  | nil => rw [hgs] at h0; cases h0
  | cons g0 rest =>
    rw [hgs] at h0; simp at h0; subst h0
    cases rest with
    | nil => rw [hgs] at h1; simp at h1
    | cons g1 rest2 =>
      rw [hgs] at h1; simp at h1; subst h1
      have hlen2 : 2 ≤ C.gates.length := by rw [hgs]; simp
      have hlen3 : 3 ≤ C.gates.length := by
        by_contra hlt
        have hlen_eq : C.gates.length = 2 := by omega
        have hr2 : rest2 = [] := by
          rw [hgs] at hlen_eq; simp at hlen_eq; exact hlen_eq
        have hout_eq : C.output = 10 := by unfold Circuit.size at hout; omega
        have hev := hpm (mkIn true false false false true false false false true)
        rw [Circuit.eval, wires_eq_foldl, hgs, hr2, hout_eq] at hev
        simp [runStep, mkIn, pm3, GateOp.eval] at hev
      obtain ⟨r, hr_gt, hr_in⟩ := hused ⟨0, by omega⟩ (show 0 + 1 < C.gates.length by omega)
      have hr_ne1 : r.val ≠ 1 := by
        intro heq
        have hg1 : C.gates.get r = ⟨GateOp.and, [0, 5]⟩ := by
          simp [List.get_eq_getElem, hgs, heq]
        rw [hg1] at hr_in
        simp at hr_in
      have hr_ge2 : 2 ≤ r.val := by omega
      let D := compileCircuit C
      obtain ⟨hwf1, hlt, heval, hdrop⟩ := compileState_inv C.gates hnf
      have hout_lt : C.output < 9 + C.gates.length := by unfold Circuit.size at hout; omega
      have hD_wf : D.WF := by
        refine ⟨hwf1, ?_⟩
        change ((compileState C.gates).2.getD C.output (.const false)).ltBound _
        rw [List.getD_eq_getElem?_getD]
        cases h : (compileState C.gates).2[C.output]? with
        | none => trivial
        | some ref => exact hlt ref (List.mem_of_getElem? h)
      have hD_eval : ∀ x : Fin 9 → Bool, x 0 = true → D.eval x = pm3 x := by
        intro x hx0
        change evalRef x (evalWires x (compileState C.gates).1)
          ((compileState C.gates).2.getD C.output (.const false)) = pm3 x
        rw [heval x hx0 C.output hout_lt]
        exact hpm x
      have hd0 : isDroppedGate C.gates 0 = true := by
        simp [isDroppedGate, hgs, compileState, initEnv0, BRef.isConst]
      have hd1 : isDroppedGate C.gates 1 = true := by
        simp [isDroppedGate, hgs, compileState, compileStep, initEnv0, foldBin, BRef.isConst]
      have hwire9_const : ∀ j : ℕ, 1 ≤ j → j ≤ C.gates.length →
          (compileState (C.gates.take j)).2.getD 9 (.const false) = .const true := by
        intro j hj1 hjle
        have h1 := compileState_env_take (C.gates.take j) 1 (by simp; omega) 9 (by omega)
        rw [List.take_take, Nat.min_eq_left hj1] at h1
        rw [h1]
        simp [hgs, compileState, compileStep, initEnv0, foldBin]
      have hdr : isDroppedGate C.gates r.val = true := by
        have hgr : C.gates.getD r.val ⟨.or, []⟩ = C.gates[r.val]'r.isLt :=
          getD_eq_getElem_of_lt C.gates _ r.val r.isLt
        have h9c : (compileState (C.gates.take r.val)).2.getD 9 (.const false) = .const true :=
          hwire9_const r.val (by omega) (le_of_lt r.isLt)
        unfold isDroppedGate
        rw [hgr]
        rcases hnf r.val r.isLt with ⟨hop, _, _, _⟩ | ⟨hop, a, b, _, _, hins⟩
        · simp [hop]
        · have h9in : 9 = a ∨ 9 = b := by
            have hr_in' : 9 ∈ (C.gates[r.val]'r.isLt).inputs := by simpa [List.get_eq_getElem] using hr_in
            rw [hins] at hr_in'
            simpa using hr_in'
          rcases hop with hop | hop <;>
            rcases h9in with rfl | rfl <;>
            simp only [hop, hins, List.getD_cons_zero, List.getD_cons_succ, h9c, BRef.isConst, Bool.true_or, Bool.or_true]
      have hcnt3 : 3 ≤ (List.range C.gates.length).countP (isDroppedGate C.gates) :=
        countP_three_le (List.range C.gates.length) (isDroppedGate C.gates) 0 1 r.val
          List.nodup_range (List.mem_range.mpr (by omega)) (List.mem_range.mpr (by omega))
          (List.mem_range.mpr r.isLt) (by omega) (by omega) (by omega) hd0 hd1 hdr
      have hD_le9 : D.gates.length ≤ 9 := by
        change (compileState C.gates).1.length ≤ 9
        unfold Circuit.size at hsz
        omega
      have hD_ge10 : 10 ≤ D.gates.length := h8_lower_bound D hD_wf hD_eval
      omega

end PEqualNP.Outside.L_meta_27585_aux

theorem PEqualNP.Outside.L_meta_27585 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩)) := by
  exact PEqualNP.Outside.L_meta_27585_aux.main
