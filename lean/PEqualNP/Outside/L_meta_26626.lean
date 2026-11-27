import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26626
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

abbrev Sig (X : Type) := X → Bool

def GateOK (g : Gate) := g.inputs.length ≤ 2 ∧
  (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))

def Ready {X : Type} (N : Nat) (enc : X → List Bool) (d : Nat) (S : Set (Sig X)) :=
  ∃ gs : List Gate, gs.length ≤ d ∧ ReadsBack N ⟨gs,0⟩ ∧ (∀ g ∈ gs, GateOK g) ∧
    ∀ f ∈ S, ∃ i < N+gs.length, ∀ x, ((Circuit.mk gs 0).wires (enc x)).getD i false = f x

lemma wlen (gs : List Gate) (xs : List Bool) :
    ((Circuit.mk gs 0).wires xs).length = xs.length + gs.length := by
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs).length = _
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp <;> omega

variable {X : Type} {N : Nat} {enc : X → List Bool} {d : Nat} {S : Set (Sig X)}

lemma weaken {c : Nat} {T : Set (Sig X)} (h : Ready N enc d S) (hc : d ≤ c) (hs : T ⊆ S) :
    Ready N enc c T := by
  obtain ⟨gs, hd, rb, fit, hw⟩ := h
  exact ⟨gs, hd.trans hc, rb, fit, fun f hf => hw f (hs hf)⟩

lemma emit (len : ∀ x, (enc x).length = N) (h : Ready N enc d S) (op : GateOp)
    (deps : List (Sig X)) (f : Sig X) (hop : deps.length ≤ 2 ∧
      (op = .and ∨ op = .or ∨ (op = .not ∧ deps.length = 1)))
    (hd : ∀ z ∈ deps, z ∈ S) (val : ∀ x, op.eval (deps.map fun z => z x) = f x) :
    Ready N enc (d+1) (insert f S) := by
  classical
  obtain ⟨gs, hb, hr, hf, hw⟩ := h
  let wire (z : Sig X) := if hz : z ∈ S then (hw z hz).choose else 0
  have spec (z : Sig X) (hz : z ∈ S) : wire z < N+gs.length ∧
      ∀ x, ((Circuit.mk gs 0).wires (enc x)).getD (wire z) false = z x := by
    simpa [wire, hz] using (hw z hz).choose_spec
  let g : Gate := ⟨op,deps.map wire⟩
  have snoc (x : X) : (Circuit.mk (gs++[g]) 0).wires (enc x) =
      (Circuit.mk gs 0).wires (enc x) ++ [f x] := by
    have mapped : (deps.map wire).map (fun i => ((Circuit.mk gs 0).wires (enc x)).getD i false) =
        deps.map (fun z => z x) := by
      rw [List.map_map]; apply List.map_congr_left; exact fun z hz => (spec z (hd z hz)).2 x
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change _ ++ [op.eval ((deps.map wire).map (fun i => ((Circuit.mk gs 0).wires (enc x)).getD i false))] = _
    rw [mapped, val]
  refine ⟨gs++[g], by simp <;> omega, ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs++[g]).length at hj
    change i ∈ ((gs++[g]).getD j ⟨GateOp.or,[]⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have eq : j = gs.length := by simp at hj; omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hm : i ∈ deps.map wire := by simpa [g] using hi
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hm
      exact (spec z (hd z hz)).1
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hf z hz
    · obtain rfl := List.mem_singleton.mp hz
      simpa [GateOK,g] using hop
  · intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · refine ⟨N+gs.length, by simp <;> omega, fun x => ?_⟩
      rw [snoc, List.getD_append_right _ _ _ _ (by simp [wlen,len])]
      simp [wlen,len]
    · obtain ⟨i,hi,he⟩ := hw z hz
      refine ⟨i, by simp <;> omega, fun x => ?_⟩
      rw [snoc, List.getD_append _ _ _ _ (by simpa [wlen,len] using hi), he]

def conj (a b : Sig X) : Sig X := fun x => a x && b x

def disj (a b : Sig X) : Sig X := fun x => a x || b x

def negB (a : Sig X) : Sig X := fun x => !a x

def parity (a b : Sig X) : Sig X := fun x => xor (a x) (b x)

lemma conjG (len : ∀ x, (enc x).length = N) (h : Ready N enc d S) {a b : Sig X}
    (ha : a ∈ S) (hb : b ∈ S) : Ready N enc (d+1) (insert (conj a b) S) :=
  emit len h .and [a,b] _ (by simp) (by simpa using And.intro ha hb) (by simp [conj,GateOp.eval])

lemma disjG (len : ∀ x, (enc x).length = N) (h : Ready N enc d S) {a b : Sig X}
    (ha : a ∈ S) (hb : b ∈ S) : Ready N enc (d+1) (insert (disj a b) S) :=
  emit len h .or [a,b] _ (by simp) (by simpa using And.intro ha hb) (by simp [disj,GateOp.eval])

lemma negG (len : ∀ x, (enc x).length = N) (h : Ready N enc d S) {a : Sig X}
    (ha : a ∈ S) : Ready N enc (d+1) (insert (negB a) S) :=
  emit len h .not [a] _ (by simp) (by simpa using ha) (by simp [negB,GateOp.eval])

lemma constG (len : ∀ x, (enc x).length = N) (h : Ready N enc d S) (b : Bool) :
    Ready N enc (d+1) (insert (fun _ => b) S) := by
  cases b
  · exact emit len h .or [] _ (by simp) (by simp) (by intro; rfl)
  · exact emit len h .and [] _ (by simp) (by simp) (by intro; rfl)

lemma xorG (len : ∀ x, (enc x).length = N) (h : Ready N enc d S) {a b : Sig X}
    (ha : a ∈ S) (hb : b ∈ S) : Ready N enc (d+4) (insert (parity a b) S) := by
  have eq : parity a b = conj (disj a b) (negB (conj a b)) := by
    funext x; cases e : a x <;> cases f : b x <;> simp [parity,conj,disj,negB,e,f]
  rw [eq]
  have h1 := conjG len h ha hb
  have h2 := disjG len h1 (Set.mem_insert_of_mem _ ha) (Set.mem_insert_of_mem _ hb)
  have h3 := negG len h2 (Set.mem_insert_of_mem _ (Set.mem_insert (conj a b) S))
  have h4 := conjG len h3 (Set.mem_insert_of_mem _ (Set.mem_insert (disj a b) _)) (Set.mem_insert _ _)
  exact weaken h4 le_rfl (by intro z hz; simp_all only [Set.mem_insert_iff]; tauto)

lemma muxG (len : ∀ x, (enc x).length = N) (h : Ready N enc d S) {a b sel : Sig X}
    (ha : a ∈ S) (hb : b ∈ S) (hs : sel ∈ S) (hn : negB sel ∈ S) :
    Ready N enc (d+3) (insert (fun x => if sel x then b x else a x) S) := by
  have eq : (fun x => if sel x then b x else a x) = disj (conj (negB sel) a) (conj sel b) := by
    funext x; cases e : sel x <;> simp [disj,conj,negB,e]
  rw [eq]
  have h1 := conjG len h hn ha
  have h2 := conjG len h1 (Set.mem_insert_of_mem _ hs) (Set.mem_insert_of_mem _ hb)
  have h3 := disjG len h2 (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (Set.mem_insert _ _)
  exact weaken h3 le_rfl (by intro z hz; simp_all only [Set.mem_insert_iff]; tauto)

lemma batch (h : Ready N enc d S) (f : Nat → Sig X) (b L : Nat)
    (build : ∀ i < L, ∀ {c U}, S ⊆ U → Ready N enc c U → Ready N enc (c+b) (insert (f i) U)) :
    Ready N enc (d+L*b) (S ∪ {g | ∃ i < L, g = f i}) := by
  induction L with
  | zero => simpa using h
  | succ L ih =>
    have prev := ih (fun i hi {c U} hs hr => build i (Nat.lt_succ_of_lt hi) hs hr)
    have step := build L (Nat.lt_succ_self _) Set.subset_union_left prev
    apply weaken step (by rw [Nat.succ_mul]; omega)
    intro g hg
    rcases hg with hg | ⟨i,hi,rfl⟩
    · exact Or.inr (Or.inl hg)
    · by_cases eq : i = L
      · exact Or.inl (congrArg f eq)
      · exact Or.inr (Or.inr ⟨i,by omega,rfl⟩)

def addr (bits : Nat → Sig X) : Nat → X → Nat
  | 0, _ => 0
  | q+1, x => (if bits q x then 2^q else 0) + addr bits q x

lemma decode (a : X → Nat) (q : Nat) (x : X) :
    addr (fun i v => (a v).testBit i) q x = a x % 2^q := by
  induction q with
  | zero => simp [addr,Nat.mod_one]
  | succ q ih =>
    rw [addr, ih, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    by_cases h : a x / 2^q % 2 = 1
    · simp [h,Nat.add_comm]
    · have hz : a x / 2^q % 2 = 0 := by omega
      simp [hz]

lemma sweep (len : ∀ x, (enc x).length = N) (bits : Nat → Sig X) (u q : Nat)
    (T : Nat → Sig X) (h : Ready N enc d S) (hb : ∀ z < q, bits z ∈ S)
    (ht : ∀ i < u+2^q, T i ∈ S) :
    Ready N enc (d+3*(u*q+(2^q-1))+q)
      (S ∪ {g | ∃ i < u+1, g = fun x => T (addr bits q x + i) x}) := by
  induction q generalizing S d T with
  | zero =>
    apply weaken h (by simp)
    rintro g (hg | ⟨i,hi,rfl⟩)
    · exact hg
    · simpa [addr] using ht i (by simpa using hi)
  | succ q ih =>
    let L := u+2^q
    let T' (i : Nat) : Sig X := fun x => if bits q x then T (2^q+i) x else T i x
    let S1 := insert (negB (bits q)) S
    let S2 := S1 ∪ {g | ∃ i < L, g = T' i}
    have h1 : Ready N enc (d+1) S1 := negG len h (hb q (Nat.lt_succ_self _))
    have h2 : Ready N enc (d+1+L*3) S2 := by
      apply batch h1 T' 3 L
      intro i hi c U sub pre
      have hwidth : 2^(q+1) = 2^q*2 := pow_succ _ _
      dsimp only [L] at hi
      exact muxG len pre (sub (Or.inr (ht i (by omega))))
        (sub (Or.inr (ht (2^q+i) (by omega)))) (sub (Or.inr (hb q (Nat.lt_succ_self _))))
        (sub (Set.mem_insert _ _))
    have restBuilt := ih T' h2 (fun z hz => Or.inl (Or.inr (hb z (Nat.lt_succ_of_lt hz))))
      (fun i hi => Or.inr ⟨i,hi,rfl⟩)
    apply weaken restBuilt
    · have hmul : u*(q+1) = u*q+u := Nat.mul_succ u q
      have hp := Nat.two_pow_pos q
      dsimp only [L]
      rw [pow_succ 2 q, hmul]
      omega
    · rintro g (hg | ⟨i,hi,rfl⟩)
      · exact Or.inl (Or.inl (Or.inr hg))
      · refine Or.inr ⟨i,hi,?_⟩
        funext x; cases e : bits q x <;> simp [addr,T',e,Nat.add_assoc]

lemma dotG {k : Nat} (len : ∀ x, (enc x).length = N) (a b : Fin k → Sig X)
    (h : Ready N enc d S) (ha : ∀ i, a i ∈ S) (hb : ∀ i, b i ∈ S)
    (hz : (fun _ : X => false) ∈ S) (K : Finset (Fin k)) :
    Ready N enc (d+5*K.card) (insert (fun x => decide ((K.filter
      (fun i => a i x && b i x)).card % 2 = 1)) S) := by
  classical
  induction K using Finset.induction_on with
  | empty => simpa [Set.insert_eq_of_mem hz] using h
  | @insert i K hi ih =>
    let prev : Sig X := fun x => decide ((K.filter (fun j => a j x && b j x)).card % 2 = 1)
    let term := conj (a i) (b i)
    have h1 := conjG len ih (Set.mem_insert_of_mem _ (ha i)) (Set.mem_insert_of_mem _ (hb i))
    have h2 := xorG len h1 (Set.mem_insert_of_mem term (Set.mem_insert prev S)) (Set.mem_insert term _)
    have eq : (fun x => decide ((((insert i K).filter (fun j => a j x && b j x)).card % 2) = 1)) =
        parity prev term := by
      funext x
      have notmem : i ∉ K.filter (fun j => a j x && b j x) := fun h => hi (Finset.mem_filter.mp h).1
      cases e : a i x && b i x
      · have off : ¬ (a i x && b i x) = true := by rw [e]; decide
        rw [Finset.filter_insert, ite_eq_right off]
        simp only [parity,prev,term,conj,e,Bool.xor_false]
      · simp only [Finset.filter_insert, e, ite_true, Finset.card_insert_of_notMem notmem,
          parity,prev,term,conj,Bool.xor_true]
        apply Bool.eq_iff_iff.mpr
        simp; omega
    rw [eq]
    apply weaken h2 (by rw [Finset.card_insert_of_notMem hi, Nat.mul_succ]; omega)
    intro g hg
    rcases Set.mem_insert_iff.mp hg with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inr (Or.inr e))

end PEqualNP.Outside.L_meta_26626

open PEqualNP.Outside.L_meta_26626 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.L_meta_26626 : (∀ (k t n : ℕ), 0 < k →
  ∀ tape : ℕ → Fin n ⊕ Bool,
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+k+t) C ∧
      C.output < n+k+t+C.size ∧
      C.size ≤ 3*((k-1)*t+(2^t-1))+t+5*k+2 ∧
      (∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
        (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
      ∀ (data : Fin n → Bool) (row : Fin k → Bool) (j : Fin (2^t)),
        C.eval (List.ofFn data ++ List.ofFn row ++
          List.ofFn (fun z : Fin t => j.val.testBit z.val)) =
          decide ((((Finset.univ : Finset (Fin k)).filter (fun i =>
            row i && Sum.elim data id (tape (j.val+i.val)))).card % 2) = 1)) := by
  classical
  intro k t n hk tape
  let X := (Fin n → Bool) × (Fin k → Bool) × Fin (2^t)
  let N := n+k+t
  let bits (z : Nat) (x : X) := x.2.2.val.testBit z
  let row (i : Fin k) (x : X) := x.2.1 i
  let inp (i : Fin n) (x : X) := x.1 i
  let enc (x : X) := List.ofFn x.1 ++ List.ofFn x.2.1 ++ List.ofFn (fun z : Fin t => bits z.val x)
  have len (x) : (enc x).length = N := by simp [enc,N,Nat.add_assoc]
  let A : Set (Sig X) := {f | ∃ i < N, ∀ x, (enc x).getD i false = f x}
  have start : Ready N enc 0 A := by
    refine ⟨[], le_rfl, ?_, by simp, ?_⟩
    · intro j hj; simp at hj
    · rintro f ⟨i,hi,h⟩; exact ⟨i, by simpa using hi, h⟩
  have atFn {q : Nat} (f : Fin q → Bool) (i : Fin q) : (List.ofFn f).getD i.val false = f i := by
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn]
  have imem (i : Fin n) : inp i ∈ A := by
    refine ⟨i.val, by dsimp [N]; omega, fun x => ?_⟩
    dsimp only [enc,inp]
    rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simpa using i.isLt), atFn]
  have rmem (i : Fin k) : row i ∈ A := by
    refine ⟨n+i.val, by dsimp [N]; omega, fun x => ?_⟩
    dsimp only [enc,row]
    rw [List.getD_append _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
    simpa only [List.length_ofFn,Nat.add_sub_cancel_left] using atFn x.2.1 i
  have bmem (z : Nat) (hz : z < t) : bits z ∈ A := by
    refine ⟨n+k+z, by dsimp [N]; omega, fun x => ?_⟩
    dsimp only [enc]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simpa only [List.length_append,List.length_ofFn,Nat.add_sub_cancel_left] using
      atFn (fun i : Fin t => bits i.val x) ⟨z,hz⟩
  let Cst : Set (Sig X) := insert (fun _ => true) (insert (fun _ => false) A)
  have constants : Ready N enc 2 Cst := constG len (constG len start false) true
  let T (i : Nat) (x : X) := Sum.elim x.1 id (tape i)
  have tin (i : Nat) : T i ∈ Cst := by
    cases e : tape i with
    | inl j =>
      have eq : T i = inp j := by funext x; simp [T,inp,e]
      exact eq.symm ▸ (Or.inr (Or.inr (imem j)) : inp j ∈ Cst)
    | inr b => cases b <;> simp [Cst,T,e]
  let win (i : Fin k) (x : X) := T (addr bits t x+i.val) x
  let U := Cst ∪ {g | ∃ i < k-1+1, g = fun x => T (addr bits t x+i) x}
  have built : Ready N enc (2+3*((k-1)*t+(2^t-1))+t) U :=
    sweep len bits (k-1) t T constants (fun z hz => Or.inr (Or.inr (bmem z hz))) (fun i _ => tin i)
  have ws (i : Fin k) : win i ∈ U := Or.inr ⟨i.val,by omega,rfl⟩
  let out : Sig X := fun x => decide (((Finset.univ.filter (fun i : Fin k => row i x && win i x)).card % 2) = 1)
  obtain ⟨gs, hb, hr, hg, hw⟩ := dotG len row win built
    (fun i => Or.inl (Or.inr (Or.inr (rmem i)))) ws (Or.inl (Or.inr (Set.mem_insert _ _))) Finset.univ
  obtain ⟨i,hi,he⟩ := hw out (Set.mem_insert _ _)
  have decj (x : X) : addr bits t x = x.2.2.val :=
    (decode (fun x : X => x.2.2.val) t x).trans (Nat.mod_eq_of_lt x.2.2.isLt)
  refine ⟨⟨gs,i⟩, hr, hi, ?_, hg, ?_⟩
  · simp only [Finset.card_univ,Fintype.card_fin] at hb
    change gs.length ≤ _
    omega
  · intro data r j
    simpa only [Circuit.eval,Circuit.wires,out,row,win,decj,T,enc,bits] using he (data,r,j)
