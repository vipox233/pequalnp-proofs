import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_068_aux

namespace GateBridgeN

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

variable {α : Type*}

private def Scheduled (n : Nat) (F : α → (Fin n → Bool) → Bool) (k nc : Nat) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ notCount ⟨gs, 0⟩ = nc ∧ ReadsBack n ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x

private theorem wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.gates.length := by
  rcases C with ⟨gs, out⟩
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    w).length = w.length + gs.length
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem start {n : Nat} {F : α → (Fin n → Bool) → Bool}
    (input : Fin n → α) (h : ∀ i x, F (input i) x = x i) :
    Scheduled n F 0 0 (Set.range input) := by
  refine ⟨[], rfl, rfl, ?_, ?_, ?_⟩
  · simp [ReadsBack]
  · simp [FanInTwo]
  · intro a ha
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
    refine ⟨i.val, by simp, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = F (input i) x
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, h i x]

private theorem restrict {n k nc : Nat} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k nc S) (hsub : T ⊆ S) : Scheduled n F k nc T := by
  obtain ⟨gs, hs, hnc, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hnc, hr, hf, fun a ha => hw a (hsub ha)⟩

private theorem realizeDeps {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x)
    (deps : List α) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List Nat, is.length = deps.length ∧ (∀ i ∈ is, i < n + k) ∧
      ∀ x : Fin n → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => F a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

private def isNotGate : GateOp → Nat
  | .not => 1
  | _ => 0

private theorem push {n k nc : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    (h : Scheduled n F k nc S) (op : GateOp) (deps : List α) (out : α)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, F out x = op.eval (deps.map fun a => F a x)) :
    Scheduled n F (k + 1) (nc + isNotGate op) (insert out S) := by
  obtain ⟨gs, hgs, hnc, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin n → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + k := by
    rw [wireLength]
    simpa using congrArg (n + ·) hgs
  have hsnoc (x : Fin n → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x]
    rw [hvalues x, hval x]
  have hnc_new : notCount ⟨gs ++ [g], 0⟩ = nc + isNotGate op := by
    dsimp only [notCount] at hnc ⊢
    rw [List.filter_append, List.length_append, hnc, List.filter_cons, List.filter_nil]
    cases op <;> rfl
  refine ⟨gs ++ [g], by simp [hgs], hnc_new, ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    change g' ∈ gs ++ [g] at hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · have heq : g' = g := List.mem_singleton.mp hg'
      subst g'
      refine ⟨hop, ?_⟩
      change is.length ≤ 2
      simpa only [his] using hlen
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨n + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

end GateBridgeN

namespace Build068

open PEqualNP.CircuitLowerBounds

variable {n : Nat}
private abbrev Sig (n : Nat) := (Fin n → Bool) → Bool

private def BuildN (A B : Set (Sig n)) (b nb : Nat) : Prop :=
  True ∧ (∀ {m mn S}, GateBridgeN.Scheduled n id m mn S → A ⊆ S →
    ∃ c ≤ b, ∃ cn ≤ nb, GateBridgeN.Scheduled n id (m + c) (mn + cn) (S ∪ B))

private theorem BuildN.run {A B : Set (Sig n)} {b nb m mn S} (H : BuildN A B b nb)
    (HS : GateBridgeN.Scheduled n id m mn S) (hA : A ⊆ S) :
    ∃ c ≤ b, ∃ cn ≤ nb, GateBridgeN.Scheduled n id (m + c) (mn + cn) (S ∪ B) := H.2 HS hA

private theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : BuildN A B 0 0 := by
  refine ⟨trivial, ?_⟩
  intro m mn S HS hA
  refine ⟨0, Nat.le_refl _, 0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

private theorem relax {A B C D : Set (Sig n)} {b d nb nd : Nat}
    (H : BuildN A B b nb) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) (hn : nb ≤ nd) : BuildN C D d nd := by
  refine ⟨trivial, ?_⟩
  intro m mn S HS hC
  obtain ⟨c, hc, cn, hcn, HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c, hc.trans h, cn, hcn.trans hn, GateBridgeN.restrict HS' (Set.union_subset_union le_rfl hB)⟩

private theorem seq {A B C : Set (Sig n)} {b c nb nc : Nat}
    (H : BuildN A B b nb) (J : BuildN (A ∪ B) C c nc) : BuildN A (B ∪ C) (b + c) (nb + nc) := by
  refine ⟨trivial, ?_⟩
  intro m mn S HS hA
  obtain ⟨d, hd, dn, hdn, K⟩ := H.run HS hA
  obtain ⟨e, he, en, hen, K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d + e, Nat.add_le_add hd he, dn + en, Nat.add_le_add hdn hen,
    by simpa [Nat.add_assoc, Set.union_assoc] using K'⟩

private theorem one {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : deps.length ≤ 2)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) :
    BuildN A {f} 1 (GateBridgeN.isNotGate op) := by
  refine ⟨trivial, ?_⟩
  intro m mn S HS hA
  refine ⟨1, le_rfl, GateBridgeN.isNotGate op, le_rfl, ?_⟩
  have h := GateBridgeN.push HS op deps f hop hlen (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact GateBridgeN.restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

private def ban (f g : Sig n) : Sig n := fun x => f x && g x
private def bor (f g : Sig n) : Sig n := fun x => f x || g x
private def bnt (f : Sig n) : Sig n := fun x => !f x

private theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    BuildN A {ban f g} 1 0 :=
  one .and [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) (ban f g) (by simp [GateOp.eval, ban])

private theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    BuildN A {bor f g} 1 0 :=
  one .or [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) (bor f g) (by simp [GateOp.eval, bor])

private theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : BuildN A {bnt f} 1 1 :=
  one .not [f] (by simp) (by simp) (by simpa using hf) (bnt f) (by simp [GateOp.eval, bnt])

private theorem constG {A : Set (Sig n)} (b : Bool) : BuildN A {fun _ => b} 1 0 := by
  cases b
  · exact one .or [] (by simp) (by simp) (by simp) (fun _ => false) (by intro; rfl)
  · exact one .and [] (by simp) (by simp) (by simp) (fun _ => true) (by intro; rfl)

private theorem muxG {A : Set (Sig n)} {sw nsw t f : Sig n}
    (hsw : sw ∈ A) (hnsw : nsw ∈ A) (ht : t ∈ A) (hf : f ∈ A) :
    BuildN A {bor (ban sw t) (ban nsw f)} 3 0 := by
  have h1 := andG hsw ht
  have h2 := andG (A := A ∪ {ban sw t}) (Or.inl hnsw) (Or.inl hf)
  have h3 := orG (A := A ∪ ({ban sw t} ∪ {ban nsw f}))
    (f := ban sw t) (g := ban nsw f) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  exact relax (seq (seq h1 h2) h3) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl le_rfl

private theorem listBuild {α : Type*} {A : Set (Sig n)} (xs : List α)
    (F : α → Sig n) (c cn : Nat) (H : ∀ a ∈ xs, BuildN A {F a} c cn) :
    BuildN A {f | ∃ a ∈ xs, f = F a} (xs.length * c) (xs.length * cn) := by
  induction xs with
  | nil =>
    exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp) (by simp)
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih (fun b hb => H b (List.mem_cons_of_mem a hb))
    have h2' := relax h2 (C := A ∪ {F a}) Set.subset_union_left le_rfl le_rfl le_rfl
    refine relax (seq h1 h2') le_rfl ?_ ?_ ?_
    · rintro f ⟨b, hb, rfl⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr ⟨b, hb, rfl⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul xs.length, Nat.add_comm]
    · simp only [List.length_cons]
      rw [Nat.succ_mul xs.length, Nat.add_comm]

private theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c cn : Nat)
    (H : ∀ i, BuildN A {F i} c cn) : BuildN A (Set.range F) (k * c) (k * cn) := by
  have h := listBuild (List.finRange k) F c cn (fun i _ => H i)
  rw [List.length_finRange] at h
  refine relax h le_rfl ?_ le_rfl le_rfl
  rintro _ ⟨i, rfl⟩
  exact ⟨i, List.mem_finRange i, rfl⟩

private theorem andListG {A : Set (Sig n)} (xs : List (Sig n))
    (hxs : ∀ f ∈ xs, f ∈ A) (htrue : (fun _ => true) ∈ A) :
    BuildN A {fun x => xs.all (fun f => f x)} xs.length 0 := by
  induction xs with
  | nil =>
    have he : (fun x : Fin n → Bool => ([] : List (Sig n)).all (fun f => f x)) = (fun _ => true) := rfl
    rw [he]
    exact relax (idle (Set.singleton_subset_iff.mpr htrue)) le_rfl le_rfl (by simp) le_rfl
  | cons a xs ih =>
    have h1 := ih (fun f hf => hxs f (List.mem_cons_of_mem a hf))
    let restSig : Sig n := fun x => xs.all (fun f => f x)
    have h2 := andG (A := A ∪ {restSig}) (Or.inl (hxs a List.mem_cons_self)) (Or.inr rfl)
    have he : ban a restSig = fun x => (a :: xs).all (fun f => f x) := by
      funext x; simp [ban, restSig]
    rw [he] at h2
    refine relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) ?_ le_rfl
    simp only [List.length_cons]; omega

private def bitsVal (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => bitsVal f m + if f m then 2 ^ m else 0

private theorem bitsVal_lt (f : Nat → Bool) : ∀ m, bitsVal f m < 2 ^ m
  | 0 => by simp [bitsVal]
  | m + 1 => by
    have ih := bitsVal_lt f m
    simp only [bitsVal, Nat.pow_succ]
    cases f m <;> simp <;> omega

private theorem bitsVal_testBit (f : Nat → Bool) : ∀ m i, i < m → (bitsVal f m).testBit i = f i
  | 0, _, hi => by omega
  | m + 1, i, hi => by
    simp only [bitsVal]
    have hlt := bitsVal_lt f m
    by_cases him : i = m
    · subst him
      cases hfm : f i
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact Nat.testBit_lt_two_pow hlt
      · simp only [↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
    · have him' : i < m := by omega
      cases hfm : f m
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact bitsVal_testBit f m i him'
      · simp only [↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt him']
        exact bitsVal_testBit f m i him'


private theorem bitsVal_lt_step_dual (f g : Nat → Bool) (m : Nat) :
    decide (bitsVal f (m + 1) < bitsVal g (m + 1)) =
      ((!(f m) && g m) || ((!(f m) || g m) && decide (bitsVal f m < bitsVal g m))) ∧
    decide (bitsVal g (m + 1) ≤ bitsVal f (m + 1)) =
      ((f m && !(g m)) || ((f m || !(g m)) && decide (bitsVal g m ≤ bitsVal f m))) := by
  have hf := bitsVal_lt f m
  have hg := bitsVal_lt g m
  constructor
  · apply Bool.eq_iff_iff.mpr; rw [decide_eq_true_eq]
    simp only [bitsVal, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    cases f m <;> cases g m <;> simp <;> omega
  · apply Bool.eq_iff_iff.mpr; rw [decide_eq_true_eq]
    simp only [bitsVal, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    cases f m <;> cases g m <;> simp <;> omega

private theorem dualStepG {A : Set (Sig n)} {a b p : Sig n}
    (ha : a ∈ A) (hb : b ∈ A) (hp : p ∈ A) :
    BuildN A {bor (ban a b) (ban (bor a b) p)} 4 0 := by
  have h1 := andG ha hb
  have h2 := orG (A := A ∪ {ban a b}) (Or.inl ha) (Or.inl hb)
  have h3 := andG (A := A ∪ ({ban a b} ∪ {bor a b})) (Or.inr (Or.inr rfl)) (Or.inl hp)
  have h4 := orG (A := A ∪ (({ban a b} ∪ {bor a b}) ∪ {ban (bor a b) p}))
    (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  exact relax (seq (seq (seq h1 h2) h3) h4) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl le_rfl

private def dualLt (f nf g ng : Nat → Sig n) : Nat → Sig n
  | 0 => fun _ => false
  | m + 1 => bor (ban (nf m) (g m)) (ban (bor (nf m) (g m)) (dualLt f nf g ng m))

private def dualGe (f nf g ng : Nat → Sig n) : Nat → Sig n
  | 0 => fun _ => true
  | m + 1 => bor (ban (f m) (ng m)) (ban (bor (f m) (ng m)) (dualGe f nf g ng m))

private theorem dualLtGe_eval {f nf g ng : Nat → Sig n} (x : Fin n → Bool) (m : Nat)
    (hnf : ∀ i < m, nf i x = !(f i x)) (hng : ∀ i < m, ng i x = !(g i x)) :
    dualLt f nf g ng m x = decide (bitsVal (fun i => f i x) m < bitsVal (fun i => g i x) m) ∧
    dualGe f nf g ng m x = decide (bitsVal (fun i => g i x) m ≤ bitsVal (fun i => f i x) m) := by
  induction m with
  | zero => simp [dualLt, dualGe, bitsVal]
  | succ m ih =>
    have hih := ih (fun i hi => hnf i (by omega)) (fun i hi => hng i (by omega))
    have hst := bitsVal_lt_step_dual (fun i => f i x) (fun i => g i x) m
    have hnf_m := hnf m (by omega)
    have hng_m := hng m (by omega)
    constructor
    · simp only [dualLt, bor, ban, hnf_m, hih.1]
      exact hst.1.symm
    · simp only [dualGe, bor, ban, hng_m, hih.2]
      exact hst.2.symm

private theorem dualLtGeG {A : Set (Sig n)} (f nf g ng : Nat → Sig n) (m : Nat)
    (hf : ∀ i < m, f i ∈ A) (hnf : ∀ i < m, nf i ∈ A)
    (hg : ∀ i < m, g i ∈ A) (hng : ∀ i < m, ng i ∈ A)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    BuildN A ({dualLt f nf g ng m} ∪ {dualGe f nf g ng m}) (8 * m) 0 := by
  induction m with
  | zero =>
    refine relax (idle ?_) le_rfl le_rfl (by simp) le_rfl
    rintro s (rfl | rfl)
    · exact hfalse
    · exact htrue
  | succ m ih =>
    have hprev := ih (fun i hi => hf i (by omega)) (fun i hi => hnf i (by omega))
      (fun i hi => hg i (by omega)) (fun i hi => hng i (by omega))
    have h1 := dualStepG (A := A ∪ ({dualLt f nf g ng m} ∪ {dualGe f nf g ng m}))
      (Or.inl (hnf m (by omega))) (Or.inl (hg m (by omega))) (Or.inr (Or.inl rfl))
    have h2 := dualStepG (A := A ∪ (({dualLt f nf g ng m} ∪ {dualGe f nf g ng m}) ∪ {dualLt f nf g ng (m + 1)}))
      (Or.inl (hf m (by omega))) (Or.inl (hng m (by omega))) (Or.inr (Or.inl (Or.inr rfl)))
    refine relax (seq (seq hprev h1) h2) le_rfl ?_ (by omega) le_rfl
    rintro s (rfl | rfl)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr rfl

end Build068

namespace Bitonic

private def bitonicMerge (off : Nat) : Nat → Bool → List (Nat × Nat × Bool)
  | 0, _ => []
  | k + 1, asc =>
    let h := 2 ^ k
    let stage := (List.range h).map (fun i => (off + i, off + h + i, asc))
    stage ++ bitonicMerge off k asc ++ bitonicMerge (off + h) k asc

private def bitonicSort (off : Nat) : Nat → Bool → List (Nat × Nat × Bool)
  | 0, _ => []
  | k + 1, asc =>
    let h := 2 ^ k
    bitonicSort off k true ++ bitonicSort (off + h) k false ++ bitonicMerge off (k + 1) asc

private theorem bitonicMerge_length (off : Nat) : ∀ k asc,
    2 * (bitonicMerge off k asc).length = k * 2 ^ k
  | 0, _ => by simp [bitonicMerge]
  | k + 1, asc => by
    simp only [bitonicMerge, List.length_append, List.length_map, List.length_range]
    have h1 := bitonicMerge_length off k asc
    have h2 := bitonicMerge_length (off + 2 ^ k) k asc
    have he : (k + 1) * 2 ^ (k + 1) = 2 * 2 ^ k + 2 * (k * 2 ^ k) := by
      rw [Nat.pow_succ, Nat.succ_mul]
      rw [← Nat.mul_assoc k (2 ^ k) 2, Nat.mul_comm (k * 2 ^ k) 2, Nat.mul_comm (2 ^ k) 2, Nat.add_comm]
    omega

private theorem bitonicSort_length (off : Nat) : ∀ k asc,
    4 * (bitonicSort off k asc).length = k * (k + 1) * 2 ^ k
  | 0, _ => by simp [bitonicSort]
  | k + 1, asc => by
    simp only [bitonicSort, List.length_append]
    have h1 := bitonicSort_length off k true
    have h2 := bitonicSort_length (off + 2 ^ k) k false
    have hm := bitonicMerge_length off (k + 1) asc
    have he : (k + 1) * (k + 1 + 1) * 2 ^ (k + 1) =
        2 * (k * (k + 1) * 2 ^ k) + 2 * ((k + 1) * 2 ^ (k + 1)) := by
      rw [Nat.pow_succ]
      have e1 : k * (k + 1) * 2 ^ k = (k + 1) * k * 2 ^ k := by rw [Nat.mul_comm k (k + 1)]
      have e2 : (k + 1) * (k + 2) * (2 ^ k * 2) =
          (k + 1) * k * (2 ^ k * 2) + (k + 1) * 2 * (2 ^ k * 2) := by
        rw [Nat.mul_add (k + 1) k 2, Nat.add_mul]
      rw [e2]
      have e3 : 2 * (k * (k + 1) * 2 ^ k) = (k + 1) * k * (2 ^ k * 2) := by
        rw [e1, Nat.mul_comm 2, Nat.mul_assoc]
      have e4 : 2 * ((k + 1) * (2 ^ k * 2)) = (k + 1) * 2 * (2 ^ k * 2) := by
        rw [← Nat.mul_assoc 2 (k + 1), Nat.mul_comm 2 (k + 1)]
      omega
    omega

private theorem bitonicMerge_mem (off : Nat) : ∀ k asc c,
    c ∈ bitonicMerge off k asc → off ≤ c.1 ∧ c.1 < c.2.1 ∧ c.2.1 < off + 2 ^ k
  | 0, _, c, hc => by simp [bitonicMerge] at hc
  | k + 1, asc, c, hc => by
    simp only [bitonicMerge, List.mem_append, List.mem_map, List.mem_range] at hc
    rcases hc with (⟨i, hi, rfl⟩ | hc) | hc
    · dsimp only
      rw [Nat.pow_succ]
      omega
    · have h := bitonicMerge_mem off k asc c hc
      rw [Nat.pow_succ]
      omega
    · have h := bitonicMerge_mem (off + 2 ^ k) k asc c hc
      rw [Nat.pow_succ]
      omega

private theorem bitonicSort_mem (off : Nat) : ∀ k asc c,
    c ∈ bitonicSort off k asc → off ≤ c.1 ∧ c.1 < c.2.1 ∧ c.2.1 < off + 2 ^ k
  | 0, _, c, hc => by simp [bitonicSort] at hc
  | k + 1, asc, c, hc => by
    simp only [bitonicSort, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · have h := bitonicSort_mem off k true c hc
      rw [Nat.pow_succ]
      omega
    · have h := bitonicSort_mem (off + 2 ^ k) k false c hc
      rw [Nat.pow_succ]
      omega
    · exact bitonicMerge_mem off (k + 1) asc c hc

private def swapBit (k1 k2 : Nat) (asc : Bool) : Bool :=
  if asc then decide (k2 < k1) else decide (k1 < k2)

private def applySwap {α : Type*} (u v : Nat) (sw : Bool) (st : Nat → α) : Nat → α :=
  fun idx =>
    if sw then
      if idx = u then st v else if idx = v then st u else st idx
    else st idx

private theorem applySwap_invol {α : Type*} (u v : Nat) (sw : Bool) (st : Nat → α) :
    applySwap u v sw (applySwap u v sw st) = st := by
  funext idx
  simp only [applySwap]
  cases sw with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    by_cases h1 : idx = u
    · subst h1
      by_cases huv : idx = v
      · subst huv; simp
      · simp [huv, Ne.symm huv]
    · by_cases h2 : idx = v
      · subst h2; simp [h1]
      · simp [h1, h2]

private theorem applySwap_comp {α β : Type*} (u v : Nat) (sw : Bool) (f : α → β) (st : Nat → α) :
    applySwap u v sw (fun idx => f (st idx)) = fun idx => f (applySwap u v sw st idx) := by
  funext idx
  simp only [applySwap]
  cases sw <;> simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases h1 : idx = u
  · simp [h1]
  · by_cases h2 : idx = v
    · subst h2; simp [h1]
    · simp [h1, h2]

private def runNet {α : Type*} (key : α → Nat) : List (Nat × Nat × Bool) → (Nat → α) → (Nat → α)
  | [], st => st
  | (u, v, asc) :: rest, st =>
    let sw := swapBit (key (st u)) (key (st v)) asc
    runNet key rest (applySwap u v sw st)

private theorem runNet_append {α : Type*} (key : α → Nat) (n1 n2 : List (Nat × Nat × Bool)) (st : Nat → α) :
    runNet key (n1 ++ n2) st = runNet key n2 (runNet key n1 st) := by
  induction n1 generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [List.cons_append, runNet]
    exact ih _

private def netSwaps {α : Type*} (key : α → Nat) : List (Nat × Nat × Bool) → (Nat → α) → List (Nat × Nat × Bool)
  | [], _ => []
  | (u, v, asc) :: rest, st =>
    let sw := swapBit (key (st u)) (key (st v)) asc
    (u, v, sw) :: netSwaps key rest (applySwap u v sw st)

private def replaySwaps {β : Type*} : List (Nat × Nat × Bool) → (Nat → β) → (Nat → β)
  | [], st => st
  | (u, v, sw) :: rest, st => replaySwaps rest (applySwap u v sw st)

private theorem replaySwaps_append {β : Type*} (s1 s2 : List (Nat × Nat × Bool)) (st : Nat → β) :
    replaySwaps (s1 ++ s2) st = replaySwaps s2 (replaySwaps s1 st) := by
  induction s1 generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [List.cons_append, replaySwaps]
    exact ih _

private theorem replaySwaps_comp {α β : Type*} (sws : List (Nat × Nat × Bool)) (f : α → β) (st : Nat → α) :
    replaySwaps sws (fun idx => f (st idx)) = fun idx => f (replaySwaps sws st idx) := by
  induction sws generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [replaySwaps]
    rw [applySwap_comp]
    exact ih _

private theorem replaySwaps_reverse_cancel {β : Type*} (sws : List (Nat × Nat × Bool)) (st : Nat → β) :
    replaySwaps sws.reverse (replaySwaps sws st) = st := by
  induction sws generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    simp only [List.reverse_cons, replaySwaps, replaySwaps_append]
    rw [ih, applySwap_invol]

private theorem runNet_eq_replay {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    runNet key net st = replaySwaps (netSwaps key net st) st := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [runNet, netSwaps, replaySwaps]
    exact ih _

private theorem runNet_unchanged {α : Type*} (key : α → Nat) (net : List (Nat × Nat × Bool))
    (st : Nat → α) (idx : Nat) (h : ∀ c ∈ net, idx ≠ c.1 ∧ idx ≠ c.2.1) :
    runNet key net st idx = st idx := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    have hc := h (u, v, asc) List.mem_cons_self
    simp only [runNet]
    rw [ih _ (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
    simp only [applySwap]
    cases swapBit (key (st u)) (key (st v)) asc
    · rfl
    · simp only [↓reduceIte, hc.1, hc.2]

private theorem runNet_mono_map {α : Type*} (key : α → Nat) (f : Nat → Bool)
    (hf : ∀ x y, x ≤ y → f x = true → f y = true)
    (net : List (Nat × Nat × Bool)) (st : Nat → α) :
    (fun idx => f (key (runNet key net st idx))) =
      runNet (fun b : Bool => b.toNat) net (fun idx => f (key (st idx))) := by
  induction net generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    simp only [runNet]
    rw [ih]
    congr 1
    funext idx
    simp only [applySwap, swapBit]
    have hpair :
        (f (key (if (if asc then decide (key (st v) < key (st u)) else decide (key (st u) < key (st v)))
          then st v else st u)) =
         if (if asc then decide ((f (key (st v))).toNat < (f (key (st u))).toNat)
             else decide ((f (key (st u))).toNat < (f (key (st v))).toNat))
          then f (key (st v)) else f (key (st u))) ∧
        (f (key (if (if asc then decide (key (st v) < key (st u)) else decide (key (st u) < key (st v)))
          then st u else st v)) =
         if (if asc then decide ((f (key (st v))).toNat < (f (key (st u))).toNat)
             else decide ((f (key (st u))).toNat < (f (key (st v))).toNat))
          then f (key (st u)) else f (key (st v))) := by
      cases asc <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · by_cases hlt : key (st u) < key (st v)
        · have hle : key (st u) ≤ key (st v) := Nat.le_of_lt hlt
          simp only [hlt, decide_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · simp
          · exact absurd (hf _ _ hle hfu) (by rw [hfv]; decide)
          · simp
        · have hle : key (st v) ≤ key (st u) := Nat.le_of_not_lt hlt
          simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · exact absurd (hf _ _ hle hfv) (by rw [hfu]; decide)
          · simp
          · simp
      · by_cases hlt : key (st v) < key (st u)
        · have hle : key (st v) ≤ key (st u) := Nat.le_of_lt hlt
          simp only [hlt, decide_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · exact absurd (hf _ _ hle hfv) (by rw [hfu]; decide)
          · simp
          · simp
        · have hle : key (st u) ≤ key (st v) := Nat.le_of_not_lt hlt
          simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
          cases hfu : f (key (st u)) <;> cases hfv : f (key (st v))
          · simp
          · simp
          · exact absurd (hf _ _ hle hfu) (by rw [hfv]; decide)
          · simp
    by_cases h1 : idx = u
    · subst h1
      have hl := hpair.1
      by_cases hs1 : (if asc then decide (key (st v) < key (st idx)) else decide (key (st idx) < key (st v))) = true <;>
        by_cases hs2 : (if asc then decide ((f (key (st v))).toNat < (f (key (st idx))).toNat)
          else decide ((f (key (st idx))).toNat < (f (key (st v))).toNat)) = true <;>
        simp only [hs1, hs2, ↓reduceIte] at hl ⊢ <;> exact hl
    · by_cases h2 : idx = v
      · subst h2
        have hr := hpair.2
        by_cases hs1 : (if asc then decide (key (st idx) < key (st u)) else decide (key (st u) < key (st idx))) = true <;>
          by_cases hs2 : (if asc then decide ((f (key (st idx))).toNat < (f (key (st u))).toNat)
            else decide ((f (key (st u))).toNat < (f (key (st idx))).toNat)) = true <;>
          simp only [hs1, hs2, h1, ↓reduceIte] at hr ⊢ <;> exact hr
      · by_cases hs1 : (if asc then decide (key (st v) < key (st u)) else decide (key (st u) < key (st v))) = true <;>
          by_cases hs2 : (if asc then decide ((f (key (st v))).toNat < (f (key (st u))).toNat)
            else decide ((f (key (st u))).toNat < (f (key (st v))).toNat)) = true <;>
          simp only [hs1, hs2, h1, h2, Bool.false_eq_true, ↓reduceIte]

private def IsBitonic (off len : Nat) (g : Nat → Bool) : Prop :=
  ∃ s e, s ≤ e ∧ e ≤ len ∧
    ((∀ i < len, g (off + i) = true ↔ s ≤ i ∧ i < e) ∨
     (∀ i < len, g (off + i) = false ↔ s ≤ i ∧ i < e))

private def IsSortedBool (off len : Nat) (asc : Bool) (g : Nat → Bool) : Prop :=
  ∀ i j, i ≤ j → j < len →
    if asc then (g (off + i) = true → g (off + j) = true)
    else (g (off + j) = true → g (off + i) = true)

private theorem runNet_bool_const (net : List (Nat × Nat × Bool)) (off len : Nat) (v : Bool)
    (g : Nat → Bool)
    (hnet : ∀ c ∈ net, off ≤ c.1 ∧ c.1 < off + len ∧ off ≤ c.2.1 ∧ c.2.1 < off + len)
    (hg : ∀ i < len, g (off + i) = v) :
    ∀ i < len, runNet (fun b : Bool => b.toNat) net g (off + i) = v := by
  induction net generalizing g with
  | nil => exact hg
  | cons c rest ih =>
    rcases c with ⟨x, y, asc⟩
    have hc := hnet (x, y, asc) List.mem_cons_self
    dsimp only at hc
    simp only [runNet]
    apply ih _ (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc'))
    intro i hi
    simp only [applySwap]
    have hx : g x = v := by
      have e : off + (x - off) = x := by omega
      rw [← e]; exact hg (x - off) (by omega)
    have hy : g y = v := by
      have e : off + (y - off) = y := by omega
      rw [← e]; exact hg (y - off) (by omega)
    cases swapBit (g x).toNat (g y).toNat asc
    · exact hg i hi
    · simp only [↓reduceIte]
      by_cases h1 : off + i = x
      · simp [h1, hy]
      · by_cases h2 : off + i = y
        · simp only [h1, ↓reduceIte]; simp only [h2, ↓reduceIte]; exact hx
        · simp [h1, h2, hg i hi]

private theorem stage_eval (off h : Nat) (asc : Bool) (g : Nat → Bool) :
    ∀ m ≤ h, ∀ idx,
      let stage := (List.range m).map (fun i => (off + i, off + h + i, asc))
      runNet (fun b : Bool => b.toNat) stage g idx =
        if off ≤ idx ∧ idx < off + m then
          if asc then g idx && g (idx + h) else g idx || g (idx + h)
        else if off + h ≤ idx ∧ idx < off + h + m then
          if asc then g (idx - h) || g idx else g (idx - h) && g idx
        else g idx := by
  intro m
  induction m with
  | zero =>
    intro _ idx
    dsimp only
    simp only [List.range_zero, List.map_nil, runNet, Nat.add_zero]
    simp only [show ¬ (off ≤ idx ∧ idx < off) by omega,
      show ¬ (off + h ≤ idx ∧ idx < off + h) by omega, ↓reduceIte]
  | succ m ih =>
    intro hm idx
    dsimp only
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, runNet_append]
    simp only [runNet, applySwap, swapBit]
    have h1 := ih (by omega) (off + m)
    have h2 := ih (by omega) (off + h + m)
    have h3 := ih (by omega) idx
    have h1' : runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g (off + m) = g (off + m) := by
      rw [h1]; simp only [show ¬ (off ≤ off + m ∧ off + m < off + m) by omega,
        show ¬ (off + h ≤ off + m ∧ off + m < off + h + m) by omega, ↓reduceIte]
    have h2' : runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g (off + h + m) = g (off + h + m) := by
      rw [h2]; simp only [show ¬ (off ≤ off + h + m ∧ off + h + m < off + m) by omega,
        show ¬ (off + h ≤ off + h + m ∧ off + h + m < off + h + m) by omega, ↓reduceIte]
    rw [h1', h2']
    by_cases hidx1 : idx = off + m
    · subst hidx1
      rw [h1']
      have e1 : off + m + h = off + h + m := by omega
      have hc1 : off ≤ off + m ∧ off + m < off + (m + 1) := by omega
      simp only [hc1, ↓reduceIte, e1]
      cases asc <;> cases g (off + m) <;> cases g (off + h + m) <;> rfl
    · by_cases hidx2 : idx = off + h + m
      · subst hidx2
        rw [h2']
        have e1 : off + h + m - h = off + m := by omega
        have hc1 : ¬ (off ≤ off + h + m ∧ off + h + m < off + (m + 1)) := by omega
        have hc2 : off + h ≤ off + h + m ∧ off + h + m < off + h + (m + 1) := by omega
        have hne : off + h + m ≠ off + m := by omega
        simp only [hc1, hc2, hne, ↓reduceIte, e1]
        cases asc <;> cases g (off + m) <;> cases g (off + h + m) <;> rfl
      · have hne1 : ¬ (idx = off + m) := hidx1
        have hne2 : ¬ (idx = off + h + m) := hidx2
        have heq : (if (if asc then decide ((g (off + h + m)).toNat < (g (off + m)).toNat)
            else decide ((g (off + m)).toNat < (g (off + h + m)).toNat)) then
            if idx = off + m then g (off + h + m) else if idx = off + h + m then g (off + m)
            else runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g idx
          else runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g idx) =
          runNet (fun b : Bool => b.toNat) ((List.range m).map (fun i => (off + i, off + h + i, asc))) g idx := by
          cases (if asc then decide ((g (off + h + m)).toNat < (g (off + m)).toNat)
            else decide ((g (off + m)).toNat < (g (off + h + m)).toNat)) <;> simp [hne1, hne2]
        rw [heq, h3]
        by_cases c1 : off ≤ idx ∧ idx < off + m
        · have c1' : off ≤ idx ∧ idx < off + (m + 1) := by omega
          simp only [c1, c1', and_self, ↓reduceIte]
        · by_cases c2 : off + h ≤ idx ∧ idx < off + h + m
          · have c1' : ¬ (off ≤ idx ∧ idx < off + (m + 1)) := by omega
            have c2' : off + h ≤ idx ∧ idx < off + h + (m + 1) := by omega
            simp only [c1, c2, c1', c2', and_self, ↓reduceIte]
          · have c1' : ¬ (off ≤ idx ∧ idx < off + (m + 1)) := by omega
            have c2' : ¬ (off + h ≤ idx ∧ idx < off + h + (m + 1)) := by omega
            simp only [c1, c2, c1', c2', and_self, ↓reduceIte]

private theorem bitonic_split_true (off h : Nat) (g : Nat → Bool) (hb : IsBitonic off (2 * h) g) :
    let lo : Nat → Bool := fun idx => g idx && g (idx + h)
    let hi : Nat → Bool := fun idx => g (idx - h) || g idx
    IsBitonic off h lo ∧ IsBitonic (off + h) h hi ∧
      ((∀ i < h, lo (off + i) = false) ∨ (∀ i < h, hi (off + h + i) = true)) := by
  intro lo hi
  rcases hb with ⟨s, e, hse, he2h, htr | hfa⟩
  · by_cases hlen : e - s ≤ h
    · have hlo_all : ∀ i < h, lo (off + i) = false := by
        intro i hi_lt
        dsimp only [lo]
        cases h1 : g (off + i) with
        | false => rfl
        | true =>
          have hi1 := (htr i (by omega)).mp h1
          cases h2 : g (off + i + h) with
          | false => rfl
          | true =>
            have e1 : off + i + h = off + (h + i) := by omega
            rw [e1] at h2
            have hi2 := (htr (h + i) (by omega)).mp h2
            omega
      refine ⟨⟨0, 0, Nat.le_refl 0, Nat.zero_le h, Or.inl (fun i hi_lt => by rw [hlo_all i hi_lt]; simp)⟩,
        ?_, Or.inl hlo_all⟩
      have hhi_iff : ∀ i < h, hi (off + h + i) = true ↔ (s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e) := by
        intro i hi_lt
        dsimp only [hi]
        have e1 : off + h + i - h = off + i := by omega
        have e2 : off + h + i = off + (h + i) := by omega
        rw [e1, e2, Bool.or_eq_true, htr i (by omega), htr (h + i) (by omega)]
      by_cases heh : e ≤ h
      · exact ⟨s, e, hse, heh, Or.inl (fun i hi_lt => by rw [hhi_iff i hi_lt]; omega)⟩
      · by_cases hhs : h ≤ s
        · exact ⟨s - h, e - h, by omega, by omega, Or.inl (fun i hi_lt => by rw [hhi_iff i hi_lt]; omega)⟩
        · refine ⟨e - h, s, by omega, by omega, Or.inr (fun i hi_lt => ?_)⟩
          have h1 := hhi_iff i hi_lt
          cases hval : hi (off + h + i) with
          | false =>
            have hnt : ¬ ((s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e)) := fun hp => by
              have := h1.mpr hp; rw [hval] at this; cases this
            constructor
            · intro _; omega
            · intro _; rfl
          | true =>
            have ht := h1.mp hval
            constructor
            · intro hc; cases hc
            · intro hr; omega
    · have hhi_all : ∀ i < h, hi (off + h + i) = true := by
        intro i hi_lt
        dsimp only [hi]
        have e1 : off + h + i - h = off + i := by omega
        have e2 : off + h + i = off + (h + i) := by omega
        rw [e1, e2, Bool.or_eq_true, htr i (by omega), htr (h + i) (by omega)]
        omega
      refine ⟨⟨s, e - h, by omega, by omega, Or.inl (fun i hi_lt => ?_)⟩,
        ⟨0, h, Nat.zero_le h, Nat.le_refl h, Or.inl (fun i hi_lt => by rw [hhi_all i hi_lt]; simp [hi_lt])⟩,
        Or.inr hhi_all⟩
      dsimp only [lo]
      have e1 : off + i + h = off + (h + i) := by omega
      rw [e1, Bool.and_eq_true, htr i (by omega), htr (h + i) (by omega)]
      omega
  · by_cases hlen : e - s ≤ h
    · have hhi_all : ∀ i < h, hi (off + h + i) = true := by
        intro i hi_lt
        dsimp only [hi]
        have e1 : off + h + i - h = off + i := by omega
        have e2 : off + h + i = off + (h + i) := by omega
        rw [e1, e2]
        cases h1 : g (off + i) with
        | true => rfl
        | false =>
          have hi1 := (hfa i (by omega)).mp h1
          cases h2 : g (off + (h + i)) with
          | true => rfl
          | false =>
            have hi2 := (hfa (h + i) (by omega)).mp h2
            omega
      refine ⟨?_, ⟨0, h, Nat.zero_le h, Nat.le_refl h, Or.inl (fun i hi_lt => by rw [hhi_all i hi_lt]; simp [hi_lt])⟩,
        Or.inr hhi_all⟩
      have hlo_iff : ∀ i < h, lo (off + i) = false ↔ (s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e) := by
        intro i hi_lt
        dsimp only [lo]
        have e1 : off + i + h = off + (h + i) := by omega
        rw [e1, Bool.and_eq_false_iff, hfa i (by omega), hfa (h + i) (by omega)]
      by_cases heh : e ≤ h
      · exact ⟨s, e, hse, heh, Or.inr (fun i hi_lt => by rw [hlo_iff i hi_lt]; omega)⟩
      · by_cases hhs : h ≤ s
        · exact ⟨s - h, e - h, by omega, by omega, Or.inr (fun i hi_lt => by rw [hlo_iff i hi_lt]; omega)⟩
        · refine ⟨e - h, s, by omega, by omega, Or.inl (fun i hi_lt => ?_)⟩
          have h1 := hlo_iff i hi_lt
          cases hval : lo (off + i) with
          | true =>
            have hnf : ¬ ((s ≤ i ∧ i < e) ∨ (s ≤ h + i ∧ h + i < e)) := fun hp => by
              have := h1.mpr hp; rw [hval] at this; cases this
            constructor
            · intro _; omega
            · intro _; rfl
          | false =>
            have hf := h1.mp hval
            constructor
            · intro hc; cases hc
            · intro hr; omega
    · have hlo_all : ∀ i < h, lo (off + i) = false := by
        intro i hi_lt
        dsimp only [lo]
        have e1 : off + i + h = off + (h + i) := by omega
        rw [e1, Bool.and_eq_false_iff, hfa i (by omega), hfa (h + i) (by omega)]
        omega
      refine ⟨⟨0, 0, Nat.le_refl 0, Nat.zero_le h, Or.inl (fun i hi_lt => by rw [hlo_all i hi_lt]; simp)⟩,
        ⟨s, e - h, by omega, by omega, Or.inr (fun i hi_lt => ?_)⟩,
        Or.inl hlo_all⟩
      dsimp only [hi]
      have e1 : off + h + i - h = off + i := by omega
      have e2 : off + h + i = off + (h + i) := by omega
      rw [e1, e2, Bool.or_eq_false_iff, hfa i (by omega), hfa (h + i) (by omega)]
      omega

private theorem bitonicMerge_sorted (off : Nat) : ∀ k asc (g : Nat → Bool),
    IsBitonic off (2 ^ k) g →
    IsSortedBool off (2 ^ k) asc (runNet (fun b : Bool => b.toNat) (bitonicMerge off k asc) g)
  | 0, asc, g, _ => by
    intro i j hij hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    cases asc <;> exact fun h => h
  | k + 1, asc, g, hb => by
    let h := 2 ^ k
    have h2 : 2 ^ (k + 1) = 2 * h := by dsimp [h]; rw [Nat.pow_succ, Nat.mul_comm]
    rw [h2] at hb ⊢
    simp only [bitonicMerge, runNet_append]
    let stage := (List.range h).map (fun i => (off + i, off + h + i, asc))
    let g1 := runNet (fun b : Bool => b.toNat) stage g
    let g2 := runNet (fun b : Bool => b.toNat) (bitonicMerge off k asc) g1
    let g3 := runNet (fun b : Bool => b.toNat) (bitonicMerge (off + h) k asc) g2
    change IsSortedBool off (2 * h) asc g3
    have hstage := stage_eval off h asc g h (Nat.le_refl h)
    have hg1_L : ∀ i < h, g1 (off + i) = if asc then g (off + i) && g (off + i + h) else g (off + i) || g (off + i + h) := by
      intro i hi_lt
      have hs := hstage (off + i)
      dsimp only at hs
      have hc1 : off ≤ off + i ∧ off + i < off + h := by omega
      simp only [hc1, and_self, ↓reduceIte] at hs
      exact hs
    have hg1_R : ∀ i < h, g1 (off + h + i) = if asc then g (off + h + i - h) || g (off + h + i) else g (off + h + i - h) && g (off + h + i) := by
      intro i hi_lt
      have hs := hstage (off + h + i)
      dsimp only at hs
      have hc1 : ¬ (off ≤ off + h + i ∧ off + h + i < off + h) := by omega
      have hc2 : off + h ≤ off + h + i ∧ off + h + i < off + h + h := by omega
      simp only [hc1, hc2, and_self, ↓reduceIte] at hs
      exact hs
    have hsp := bitonic_split_true off h g hb
    have hleft_bit : IsBitonic off h g1 := by
      cases asc with
      | true =>
        rcases hsp.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          rw [hg1_L i hi_lt]
          exact h3 i hi_lt
        · right
          intro i hi_lt
          rw [hg1_L i hi_lt]
          exact h3 i hi_lt
      | false =>
        rcases hsp.2.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          have h3' := h3 i hi_lt
          dsimp only at h3'
          rw [e1, e2] at h3'
          rw [hg1_L i hi_lt]
          exact h3'
        · right
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          have h3' := h3 i hi_lt
          dsimp only at h3'
          rw [e1, e2] at h3'
          rw [hg1_L i hi_lt]
          exact h3'
    have hright_bit : IsBitonic (off + h) h g2 := by
      have hg2_eq : ∀ i < h, g2 (off + h + i) = g1 (off + h + i) := by
        intro i hi_lt
        apply runNet_unchanged
        intro c hc
        have hm := bitonicMerge_mem off k asc c hc
        dsimp only [h] at hi_lt ⊢
        omega
      cases asc with
      | true =>
        rcases hsp.2.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          exact h3 i hi_lt
        · right
          intro i hi_lt
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          exact h3 i hi_lt
      | false =>
        rcases hsp.1 with ⟨s, e, h1, h2', h3⟩
        refine ⟨s, e, h1, h2', ?_⟩
        rcases h3 with h3 | h3
        · left
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [e1, e2]
          exact h3 i hi_lt
        · right
          intro i hi_lt
          have e1 : off + h + i - h = off + i := by omega
          have e2 : off + h + i = off + i + h := by omega
          rw [hg2_eq i hi_lt, hg1_R i hi_lt]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [e1, e2]
          exact h3 i hi_lt
    have hsL : IsSortedBool off h asc g2 := bitonicMerge_sorted off k asc g1 hleft_bit
    have hsR : IsSortedBool (off + h) h asc g3 := bitonicMerge_sorted (off + h) k asc g2 hright_bit
    have hg3_left : ∀ i < h, g3 (off + i) = g2 (off + i) := by
      intro i hi_lt
      apply runNet_unchanged
      intro c hc
      have hm := bitonicMerge_mem (off + h) k asc c hc
      dsimp only [h] at hi_lt ⊢
      omega
    have hnetL : ∀ c ∈ bitonicMerge off k asc, off ≤ c.1 ∧ c.1 < off + h ∧ off ≤ c.2.1 ∧ c.2.1 < off + h := by
      intro c hc; have hm := bitonicMerge_mem off k asc c hc; dsimp [h]; omega
    have hnetR : ∀ c ∈ bitonicMerge (off + h) k asc,
        off + h ≤ c.1 ∧ c.1 < off + h + h ∧ off + h ≤ c.2.1 ∧ c.2.1 < off + h + h := by
      intro c hc; have hm := bitonicMerge_mem (off + h) k asc c hc; dsimp [h]; omega
    intro i j hij hj
    by_cases hjh : j < h
    · rw [hg3_left i (by omega), hg3_left j hjh]
      exact hsL i j hij hjh
    · by_cases hih : h ≤ i
      · have ei : off + i = off + h + (i - h) := by omega
        have ej : off + j = off + h + (j - h) := by omega
        rw [ei, ej]
        exact hsR (i - h) (j - h) (by omega) (by omega)
      · have hi_lt : i < h := by omega
        have hj_lt : j - h < h := by omega
        have ej : off + j = off + h + (j - h) := by omega
        rw [hg3_left i hi_lt, ej]
        cases asc with
        | true =>
          simp only [↓reduceIte]
          rcases hsp.2.2 with hlo | hhi
          · have hg1L : ∀ x < h, g1 (off + x) = false := by
              intro x hx
              rw [hg1_L x hx]
              exact hlo x hx
            have hg2i : g2 (off + i) = false :=
              runNet_bool_const (bitonicMerge off k true) off h false g1 hnetL hg1L i hi_lt
            intro ht; rw [hg2i] at ht; cases ht
          · have hg2R : ∀ x < h, g2 (off + h + x) = true := by
              intro x hx
              have heq : g2 (off + h + x) = g1 (off + h + x) := by
                apply runNet_unchanged; intro c hc; have hm := bitonicMerge_mem off k true c hc; dsimp [h] at hx ⊢; omega
              rw [heq, hg1_R x hx]
              exact hhi x hx
            intro _
            exact runNet_bool_const (bitonicMerge (off + h) k true) (off + h) h true g2 hnetR hg2R (j - h) hj_lt
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rcases hsp.2.2 with hlo | hhi
          · have hg2R : ∀ x < h, g2 (off + h + x) = false := by
              intro x hx
              have heq : g2 (off + h + x) = g1 (off + h + x) := by
                apply runNet_unchanged; intro c hc; have hm := bitonicMerge_mem off k false c hc; dsimp [h] at hx ⊢; omega
              rw [heq, hg1_R x hx]
              simp only [Bool.false_eq_true, ↓reduceIte]
              have e1 : off + h + x - h = off + x := by omega
              have e2 : off + h + x = off + x + h := by omega
              rw [e1, e2]
              exact hlo x hx
            have hg3j : g3 (off + h + (j - h)) = false :=
              runNet_bool_const (bitonicMerge (off + h) k false) (off + h) h false g2 hnetR hg2R (j - h) hj_lt
            intro ht; rw [hg3j] at ht; cases ht
          · have hg1L : ∀ x < h, g1 (off + x) = true := by
              intro x hx
              rw [hg1_L x hx]
              simp only [Bool.false_eq_true, ↓reduceIte]
              have e1 : off + h + x - h = off + x := by omega
              have e2 : off + h + x = off + x + h := by omega
              have hhi' := hhi x hx
              dsimp only at hhi'
              rw [e1, e2] at hhi'
              exact hhi'
            intro _
            exact runNet_bool_const (bitonicMerge off k false) off h true g1 hnetL hg1L i hi_lt

private theorem sorted_asc_desc_bitonic (off h : Nat) (g : Nat → Bool)
    (hL : IsSortedBool off h true g) (hR : IsSortedBool (off + h) h false g) :
    IsBitonic off (2 * h) g := by
  have hexL : ∃ s ≤ h, ∀ i < h, g (off + i) = true ↔ s ≤ i := by
    have hgenL : ∀ n, IsSortedBool off n true g → ∃ s ≤ n, ∀ i < n, g (off + i) = true ↔ s ≤ i := by
      intro n
      induction n with
      | zero => intro _; exact ⟨0, Nat.le_refl 0, fun i hi => by omega⟩
      | succ m ih =>
        intro hLm
        rcases ih (fun i j hij hj => hLm i j hij (by omega)) with ⟨s, hsm, hs⟩
        cases hgm : g (off + m) with
        | false =>
          refine ⟨m + 1, Nat.le_refl _, fun i hi => ?_⟩
          constructor
          · intro ht
            by_cases him : i = m
            · subst him; rw [hgm] at ht; cases ht
            · have hgt := hLm i m (by omega) (by omega)
              simp only [↓reduceIte] at hgt
              have := hgt ht; rw [hgm] at this; cases this
          · intro hc; omega
        | true =>
          refine ⟨s, by omega, fun i hi => ?_⟩
          by_cases him : i = m
          · subst i; rw [hgm]; simp [show s ≤ m from hsm]
          · exact hs i (by omega)
    exact hgenL h hL
  have hexR : ∃ e ≤ h, ∀ i < h, g (off + h + i) = true ↔ i < e := by
    have hgen : ∀ n (g' : Nat → Bool), IsSortedBool 0 n false g' →
        ∃ e ≤ n, ∀ i < n, g' i = true ↔ i < e := by
      intro n g'
      induction n with
      | zero => intro _; exact ⟨0, Nat.le_refl 0, fun i hi => by omega⟩
      | succ m ih =>
        intro hg'
        rcases ih (fun i j hij hj => hg' i j hij (by omega)) with ⟨e, hem, he⟩
        cases hgm : g' m with
        | false =>
          refine ⟨e, by omega, fun i hi => ?_⟩
          by_cases him : i = m
          · subst i; rw [hgm]; simp [show ¬ m < e by omega]
          · exact he i (by omega)
        | true =>
          refine ⟨m + 1, Nat.le_refl _, fun i hi => ?_⟩
          constructor
          · intro _; omega
          · intro _
            have := hg' i m (by omega) (by omega)
            simp only [Nat.zero_add, Bool.false_eq_true, ↓reduceIte] at this
            exact this hgm
    have hR' : IsSortedBool 0 h false (fun i => g (off + h + i)) := by
      intro i j hij hj
      simpa only [Nat.zero_add] using hR i j hij hj
    exact hgen h (fun i => g (off + h + i)) hR'
  rcases hexL with ⟨s, hsh, hs⟩
  rcases hexR with ⟨e, heh, he⟩
  refine ⟨s, h + e, by omega, by omega, Or.inl (fun i hi => ?_)⟩
  by_cases hih : i < h
  · rw [hs i hih]
    omega
  · have e1 : off + i = off + h + (i - h) := by omega
    rw [e1, he (i - h) (by omega)]
    omega

private theorem bitonicSort_sorted_bool (off : Nat) : ∀ k asc (g : Nat → Bool),
    IsSortedBool off (2 ^ k) asc (runNet (fun b : Bool => b.toNat) (bitonicSort off k asc) g)
  | 0, asc, g => by
    intro i j hij hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    cases asc <;> exact fun h => h
  | k + 1, asc, g => by
    let h := 2 ^ k
    simp only [bitonicSort, runNet_append]
    let g1 := runNet (fun b : Bool => b.toNat) (bitonicSort off k true) g
    let g2 := runNet (fun b : Bool => b.toNat) (bitonicSort (off + h) k false) g1
    have hsL : IsSortedBool off h true g1 := bitonicSort_sorted_bool off k true g
    have hsR : IsSortedBool (off + h) h false g2 := bitonicSort_sorted_bool (off + h) k false g1
    have hg2L : IsSortedBool off h true g2 := by
      intro i j hij hj
      have e1 : g2 (off + i) = g1 (off + i) := by
        apply runNet_unchanged; intro c hc; have hm := bitonicSort_mem (off + h) k false c hc; dsimp [h] at hij hj ⊢; omega
      have e2 : g2 (off + j) = g1 (off + j) := by
        apply runNet_unchanged; intro c hc; have hm := bitonicSort_mem (off + h) k false c hc; dsimp [h] at hj ⊢; omega
      rw [e1, e2]
      exact hsL i j hij hj
    have hbit : IsBitonic off (2 ^ (k + 1)) g2 := by
      rw [Nat.pow_succ, Nat.mul_comm]
      exact sorted_asc_desc_bitonic off h g2 hg2L hsR
    exact bitonicMerge_sorted off (k + 1) asc g2 hbit

private theorem bitonicSort_sorted {α : Type*} (key : α → Nat) (p : Nat) (st : Nat → α) :
    ∀ i j, i ≤ j → j < 2 ^ p →
      key (runNet key (bitonicSort 0 p true) st i) ≤ key (runNet key (bitonicSort 0 p true) st j) := by
  intro i j hij hj
  let T := key (runNet key (bitonicSort 0 p true) st i)
  let f : Nat → Bool := fun x => decide (T ≤ x)
  have hf : ∀ x y, x ≤ y → f x = true → f y = true := by
    intro x y hxy hx
    simp only [f, decide_eq_true_eq] at hx ⊢
    omega
  have hs := bitonicSort_sorted_bool 0 p true (fun idx => f (key (st idx))) i j hij hj
  simp only [Nat.zero_add, ↓reduceIte] at hs
  rw [← runNet_mono_map key f hf] at hs
  have hiT : f (key (runNet key (bitonicSort 0 p true) st i)) = true := by
    simp [f, T]
  have hjT := hs hiT
  simp only [f, decide_eq_true_eq] at hjT
  exact hjT

end Bitonic

namespace Circuit068

open Build068 Bitonic
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

private def markovNotCount : Nat → Nat
  | 0 => 0
  | L + 1 => 1 + markovNotCount ((L + 1) / 2)

private theorem markovNotCount_le_of_le_pow : ∀ L k, L + 1 ≤ 2 ^ k → markovNotCount L ≤ k := by
  intro L
  induction L using Nat.strong_induction_on with
  | ind L ih =>
    intro k hk
    cases L with
    | zero => simp [markovNotCount]
    | succ L =>
      cases k with
      | zero => simp at hk
      | succ k =>
        simp only [markovNotCount]
        have hhalf : (L + 1) / 2 < L + 1 := Nat.div_lt_self (Nat.succ_pos L) (by omega)
        have hpow : (L + 1) / 2 + 1 ≤ 2 ^ k := by
          rw [Nat.pow_succ] at hk
          omega
        have hih := ih ((L + 1) / 2) hhalf k hpow
        omega

private theorem markovNotCount_le_clog (L : Nat) : markovNotCount L ≤ Nat.clog 2 (L + 1) :=
  markovNotCount_le_of_le_pow L (Nat.clog 2 (L + 1)) (Nat.le_pow_clog (by omega) (L + 1))

private def isDecSorted {I : Nat} (L : Nat) (u : Fin L → Sig I) (x : Fin I → Bool) : Prop :=
  ∀ i j : Fin L, i.val ≤ j.val → u j x = true → u i x = true

private theorem markovInvert {I : Nat} : ∀ (L : Nat) {A : Set (Sig I)} (u : Fin L → Sig I)
    (hu : ∀ j : Fin L, u j ∈ A) (hfalse : (fun _ => false) ∈ A),
    ∃ nu : Fin L → Sig I,
      BuildN A (Set.range nu) (5 * L) (markovNotCount L) ∧
      ∀ x, isDecSorted L u x → ∀ j : Fin L, nu j x = !(u j x) := by
  intro L
  induction L using Nat.strong_induction_on with
  | ind L ih =>
    intro A u hu hfalse
    cases L with
    | zero =>
      refine ⟨fun j => Fin.elim0 j, relax (idle (by simp)) le_rfl le_rfl (by simp) (by simp), ?_⟩
      intro _ _ j; exact Fin.elim0 j
    | succ L' =>
      let L := L' + 1
      let k := L / 2
      have hk_lt : k < L := Nat.div_lt_self (Nat.succ_pos L') (by omega)
      have hmid_lt : k < L' + 1 := hk_lt
      let uk : Sig I := u ⟨k, hmid_lt⟩
      let nk : Sig I := bnt uk
      have Hnk : BuildN A {nk} 1 1 := notG (hu ⟨k, hmid_lt⟩)
      let rightBit : Fin k → Sig I := fun j =>
        if hlt : k + 1 + j.val < L then u ⟨k + 1 + j.val, hlt⟩ else fun _ => false
      let w : Fin k → Sig I := fun j => bor (ban (u ⟨j.val, by omega⟩) nk) (rightBit j)
      have Hw : BuildN (A ∪ {nk}) (Set.range w) (k * 2) 0 := finG w 2 0 fun j => by
        have h1 := andG (A := A ∪ {nk}) (Or.inl (hu ⟨j.val, by omega⟩)) (Or.inr rfl)
        have hrb : rightBit j ∈ A ∪ {nk} ∪ {ban (u ⟨j.val, by omega⟩) nk} := by
          dsimp only [rightBit]
          split
          · exact Or.inl (Or.inl (hu _))
          · exact Or.inl (Or.inl hfalse)
        have h2 := orG (A := (A ∪ {nk}) ∪ {ban (u ⟨j.val, by omega⟩) nk}) (Or.inr rfl) hrb
        exact relax (seq h1 h2) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl le_rfl
      have hw_mem : ∀ j : Fin k, w j ∈ (A ∪ {nk}) ∪ Set.range w := fun j => Or.inr ⟨j, rfl⟩
      obtain ⟨nw, Hnw, hnw_spec⟩ := ih k hk_lt w hw_mem (Or.inl (Or.inl hfalse))
      let A2 := A ∪ ({nk} ∪ Set.range w) ∪ Set.range nw
      let nu : Fin (L' + 1) → Sig I := fun j =>
        if hj : j.val < k then ban (nw ⟨j.val, hj⟩) nk
        else if hje : j.val = k then nk
        else bor (nw ⟨j.val - (k + 1), by have := j.isLt; have hk_def : k = (L' + 1) / 2 := rfl; omega⟩) nk
      have Hnu : BuildN A2 (Set.range nu) (L * 1) 0 := finG nu 1 0 fun j => by
        dsimp only [nu]
        split
        · rename_i hlt
          exact andG (Or.inr ⟨⟨j.val, hlt⟩, rfl⟩) (Or.inl (Or.inr (Or.inl rfl)))
        · split
          · exact relax (idle (Set.singleton_subset_iff.mpr (Or.inl (Or.inr (Or.inl rfl)))))
              le_rfl le_rfl (by omega) le_rfl
          · exact orG (Or.inr ⟨⟨j.val - (k + 1), by have := j.isLt; have hk_def : k = (L' + 1) / 2 := rfl; omega⟩, rfl⟩)
              (Or.inl (Or.inr (Or.inl rfl)))
      have H01 : BuildN A ({nk} ∪ Set.range w) (1 + k * 2) (1 + 0) := seq Hnk Hw
      have H012 : BuildN A (({nk} ∪ Set.range w) ∪ Set.range nw) (1 + k * 2 + 5 * k) (1 + 0 + markovNotCount k) :=
        seq H01 (relax Hnw (by intro s hs; rcases hs with (hs | hs) | hs; exact Or.inl hs; exact Or.inr (Or.inl hs); exact Or.inr (Or.inr hs)) le_rfl le_rfl le_rfl)
      have Htot := seq H012 (relax Hnu (by intro s hs; rcases hs with (hs | hs) | hs; exact Or.inl hs; exact Or.inr (Or.inl hs); exact Or.inr (Or.inr hs)) le_rfl le_rfl le_rfl)
      have hnot_eq : 1 + 0 + markovNotCount k + 0 = markovNotCount (L' + 1) := by
        have hrec : markovNotCount (L' + 1) = 1 + markovNotCount ((L' + 1) / 2) := by
          conv_lhs => rw [markovNotCount]
        rw [hrec]
        have hk_def : k = (L' + 1) / 2 := rfl
        rw [hk_def]
        omega
      have hgate_le : 1 + k * 2 + 5 * k + L * 1 ≤ 5 * (L' + 1) := by
        have hk_def : k = (L' + 1) / 2 := rfl
        dsimp only [L]
        rw [hk_def]
        omega
      refine ⟨nu, relax Htot le_rfl (Set.subset_union_right) hgate_le (by omega), ?_⟩
      intro x hsort
      have hw_sort : isDecSorted k w x := by
        intro i j hij hj_true
        dsimp only [w, bor, ban, nk, bnt, uk] at hj_true ⊢
        cases huk : u ⟨k, hmid_lt⟩ x with
        | false =>
          have hrb_j : rightBit j x = false := by
            dsimp only [rightBit]
            split
            · rename_i hlt
              cases h : u ⟨k + 1 + j.val, hlt⟩ x with
              | false => rfl
              | true =>
                have := hsort ⟨k, hmid_lt⟩ ⟨k + 1 + j.val, hlt⟩ (by dsimp; omega) h
                rw [huk] at this; cases this
            · rfl
          simp only [huk, Bool.not_false, Bool.and_true, hrb_j, Bool.or_false] at hj_true
          have hi_true := hsort ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij hj_true
          simp [hi_true]
        | true =>
          simp only [huk, Bool.not_true, Bool.and_false, Bool.false_or] at hj_true ⊢
          dsimp only [rightBit] at hj_true ⊢
          split at hj_true
          · rename_i hlt_j
            have hlt_i : k + 1 + i.val < L := by omega
            simp only [hlt_i, ↓reduceDIte]
            exact hsort ⟨k + 1 + i.val, hlt_i⟩ ⟨k + 1 + j.val, hlt_j⟩ (by dsimp; omega) hj_true
          · cases hj_true
      have hnw := hnw_spec x hw_sort
      intro j
      dsimp only [nu]
      split
      · rename_i hlt
        simp only [ban, hnw ⟨j.val, hlt⟩, w, bor, nk, bnt, uk]
        cases huk : u ⟨k, hmid_lt⟩ x with
        | true =>
          have hjt : u j x = true := hsort j ⟨k, hmid_lt⟩ (by dsimp; omega) huk
          simp [hjt]
        | false =>
          have hrb : rightBit ⟨j.val, hlt⟩ x = false := by
            dsimp only [rightBit]
            split
            · rename_i hlt2
              cases h : u ⟨k + 1 + j.val, hlt2⟩ x with
              | false => rfl
              | true =>
                have := hsort ⟨k, hmid_lt⟩ ⟨k + 1 + j.val, hlt2⟩ (by dsimp; omega) h
                rw [huk] at this; cases this
            · rfl
          have hjeq : (⟨j.val, by omega⟩ : Fin (L' + 1)) = j := Fin.ext rfl
          simp [hrb, hjeq]
      · rename_i hnotlt
        split
        · rename_i heq
          have hjeq : (⟨k, hmid_lt⟩ : Fin (L' + 1)) = j := Fin.ext heq.symm
          simp [nk, bnt, uk, hjeq]
        · rename_i hne
          let idx : Fin k := ⟨j.val - (k + 1), by have := j.isLt; have hk_def : k = (L' + 1) / 2 := rfl; omega⟩
          change bor (nw idx) nk x = !u j x
          simp only [bor, nk, bnt, uk]
          cases huk : u ⟨k, hmid_lt⟩ x with
          | false =>
            have hjf : u j x = false := by
              cases h : u j x with
              | false => rfl
              | true =>
                have := hsort ⟨k, hmid_lt⟩ j (by dsimp; omega) h
                rw [huk] at this; cases this
            simp [hjf]
          | true =>
            have hlt2 : k + 1 + idx.val < L := by have := j.isLt; dsimp [idx, L]; omega
            have hjeq : (⟨k + 1 + idx.val, hlt2⟩ : Fin (L' + 1)) = j := by
              apply Fin.ext; dsimp [idx]; omega
            rw [hnw idx]
            simp [w, bor, ban, nk, bnt, uk, huk, rightBit, hlt2, hjeq]

private def boolNetFwd {I : Nat} (net : List (Nat × Nat × Bool))
    (st0 : Nat → Sig I) : Nat → Sig I :=
  fun idx x => runNet (fun b : Bool => b.toNat) net (fun k => st0 k x) idx

private theorem boolNetStep_eval (u v : Nat) (asc : Bool) (g : Nat → Bool) :
    let g1 := applySwap u v (swapBit (g u).toNat (g v).toNat asc) g
    g1 u = (if asc then g u && g v else g u || g v) ∧
    g1 v = (if asc then g u || g v else g u && g v) ∧
    (∀ idx, idx ≠ u → idx ≠ v → g1 idx = g idx) := by
  intro g1
  refine ⟨?_, ?_, ?_⟩
  · simp only [g1, applySwap, swapBit]
    cases asc <;> cases g u <;> cases g v <;> rfl
  · simp only [g1, applySwap, swapBit]
    by_cases huv : v = u
    · subst huv; cases asc <;> cases g v <;> rfl
    · cases asc <;> cases g u <;> cases g v <;> simp [huv]
  · intro idx hu hv
    simp only [g1, applySwap]
    cases swapBit (g u).toNat (g v).toNat asc <;> simp [hu, hv]

private theorem boolNetFwd_rev {I : Nat} (N : Nat)
    (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N) :
    ∀ {A : Set (Sig I)} (st0 : Nat → Sig I) (hst0 : ∀ i < N, st0 i ∈ A)
      (P : (Fin I → Bool) → Prop),
      ∃ revMap : (Nat → Sig I) → (Nat → Sig I),
        BuildN A {f | ∃ i < N, f = boolNetFwd net st0 i} (2 * net.length) 0 ∧
        (∀ {B : Set (Sig I)} (nsEnd : Nat → Sig I),
          (∀ i < N, st0 i ∈ B) → (∀ i < N, nsEnd i ∈ B) →
          BuildN (B ∪ {f | ∃ i < N, f = boolNetFwd net st0 i})
            {f | ∃ i < N, f = revMap nsEnd i} (6 * net.length) 0) ∧
        (∀ (nsEnd : Nat → Sig I) (x : Fin I → Bool),
          (∀ i < N, nsEnd i x = !(boolNetFwd net st0 i x)) →
          ∀ i < N, revMap nsEnd i x = !(st0 i x)) := by
  induction net with
  | nil =>
    intro A st0 hst0 _
    refine ⟨fun ns => ns, relax (idle ?_) le_rfl le_rfl (by simp) le_rfl, ?_, ?_⟩
    · rintro f ⟨i, hi, rfl⟩; exact hst0 i hi
    · intro B nsEnd _ hns
      refine relax (idle ?_) le_rfl le_rfl (by simp) le_rfl
      rintro f ⟨i, hi, rfl⟩; exact Or.inl (hns i hi)
    · intro nsEnd x hns i hi; exact hns i hi
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    intro A st0 hst0 P
    have hc := hnet (u, v, asc) List.mem_cons_self
    let hiSig : Sig I := if asc then ban (st0 u) (st0 v) else bor (st0 u) (st0 v)
    let loSig : Sig I := if asc then bor (st0 u) (st0 v) else ban (st0 u) (st0 v)
    have Hstep : BuildN A ({hiSig} ∪ {loSig}) 2 0 := by
      dsimp only [hiSig, loSig]
      cases asc with
      | true =>
        have h1 := andG (hst0 u hc.1) (hst0 v hc.2)
        have h2 := orG (A := A ∪ {ban (st0 u) (st0 v)}) (Or.inl (hst0 u hc.1)) (Or.inl (hst0 v hc.2))
        exact seq h1 h2
      | false =>
        have h1 := orG (hst0 u hc.1) (hst0 v hc.2)
        have h2 := andG (A := A ∪ {bor (st0 u) (st0 v)}) (Or.inl (hst0 u hc.1)) (Or.inl (hst0 v hc.2))
        exact seq h1 h2
    let st1 : Nat → Sig I := fun idx x =>
      applySwap u v (swapBit (st0 u x).toNat (st0 v x).toNat asc) (fun k => st0 k x) idx
    have hst1_u : st1 u = hiSig := by
      funext x
      have h := (boolNetStep_eval u v asc (fun k => st0 k x)).1
      cases asc <;> simpa [hiSig, ban, bor] using h
    have hst1_v : st1 v = loSig := by
      funext x
      have h := (boolNetStep_eval u v asc (fun k => st0 k x)).2.1
      cases asc <;> simpa [loSig, ban, bor] using h
    have hst1_mem : ∀ i < N, st1 i ∈ A ∪ ({hiSig} ∪ {loSig}) := by
      intro i hi
      by_cases hu : i = u
      · subst hu; rw [hst1_u]; exact Or.inr (Or.inl rfl)
      · by_cases hv : i = v
        · subst hv; rw [hst1_v]; exact Or.inr (Or.inr rfl)
        · have he : st1 i = st0 i := by
            funext x; exact (boolNetStep_eval u v asc (fun k => st0 k x)).2.2 i hu hv
          rw [he]; exact Or.inl (hst0 i hi)
    have hfwd_eq : ∀ i, boolNetFwd ((u, v, asc) :: rest) st0 i = boolNetFwd rest st1 i := by
      intro i; funext x; rfl
    obtain ⟨revRest, HfwdRest, HrevRest, hspecRest⟩ :=
      ih (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc')) st1 hst1_mem P
    let revStep (ns1 : Nat → Sig I) : Nat → Sig I := fun idx =>
      if idx = u then
        if asc then bor (ns1 v) (ban (ns1 u) (st0 v)) else bor (ns1 u) (ban (ns1 v) (st0 v))
      else if idx = v then
        if asc then bor (ns1 v) (ban (ns1 u) (st0 u)) else bor (ns1 u) (ban (ns1 v) (st0 u))
      else ns1 idx
    let revFull (nsEnd : Nat → Sig I) : Nat → Sig I := revStep (revRest nsEnd)
    refine ⟨revFull, ?_, ?_, ?_⟩
    · have Htot := seq Hstep HfwdRest
      refine relax Htot le_rfl ?_ (by simp only [List.length_cons]; omega) le_rfl
      rintro f ⟨i, hi, rfl⟩
      rw [hfwd_eq i]
      exact Or.inr ⟨i, hi, rfl⟩
    · intro B nsEnd hstB hnsB
      have Hst1_on_B : BuildN B ({hiSig} ∪ {loSig}) 2 0 := by
        dsimp only [hiSig, loSig]
        cases asc with
        | true =>
          have h1 := andG (hstB u hc.1) (hstB v hc.2)
          have h2 := orG (A := B ∪ {ban (st0 u) (st0 v)}) (Or.inl (hstB u hc.1)) (Or.inl (hstB v hc.2))
          exact seq h1 h2
        | false =>
          have h1 := orG (hstB u hc.1) (hstB v hc.2)
          have h2 := andG (A := B ∪ {bor (st0 u) (st0 v)}) (Or.inl (hstB u hc.1)) (Or.inl (hstB v hc.2))
          exact seq h1 h2
      have Hst1B' : BuildN (B ∪ {f | ∃ i < N, f = boolNetFwd ((u, v, asc) :: rest) st0 i})
          ({hiSig} ∪ {loSig}) 2 0 :=
        relax Hst1_on_B Set.subset_union_left le_rfl le_rfl le_rfl
      let B1 := B ∪ ({hiSig} ∪ {loSig})
      have hst1_B1 : ∀ i < N, st1 i ∈ B1 := by
        intro i hi
        by_cases hu : i = u
        · subst hu; rw [hst1_u]; exact Or.inr (Or.inl rfl)
        · by_cases hv : i = v
          · subst hv; rw [hst1_v]; exact Or.inr (Or.inr rfl)
          · have he : st1 i = st0 i := by
              funext x; exact (boolNetStep_eval u v asc (fun k => st0 k x)).2.2 i hu hv
            rw [he]; exact Or.inl (hstB i hi)
      have hns_B1 : ∀ i < N, nsEnd i ∈ B1 := fun i hi => Or.inl (hnsB i hi)
      have Hrr := HrevRest (B := B1) nsEnd hst1_B1 hns_B1
      have Hrr' : BuildN ((B ∪ {f | ∃ i < N, f = boolNetFwd ((u, v, asc) :: rest) st0 i}) ∪ ({hiSig} ∪ {loSig}))
          {f | ∃ i < N, f = revRest nsEnd i} (6 * rest.length) 0 := by
        refine relax Hrr ?_ le_rfl le_rfl le_rfl
        rintro f (hf | ⟨i, hi, rfl⟩)
        · rcases hf with hf | hf
          · exact Or.inl (Or.inl hf)
          · exact Or.inr hf
        · exact Or.inl (Or.inr ⟨i, hi, (hfwd_eq i).symm⟩)
      let ns1 := revRest nsEnd
      let S2 := (B ∪ {f | ∃ i < N, f = boolNetFwd ((u, v, asc) :: rest) st0 i}) ∪
        (({hiSig} ∪ {loSig}) ∪ {f | ∃ i < N, f = ns1 i})
      have hns1_u : ns1 u ∈ S2 := Or.inr (Or.inr ⟨u, hc.1, rfl⟩)
      have hns1_v : ns1 v ∈ S2 := Or.inr (Or.inr ⟨v, hc.2, rfl⟩)
      have hst0_u : st0 u ∈ S2 := Or.inl (Or.inl (hstB u hc.1))
      have hst0_v : st0 v ∈ S2 := Or.inl (Or.inl (hstB v hc.2))
      let nuSig : Sig I := if asc then bor (ns1 v) (ban (ns1 u) (st0 v)) else bor (ns1 u) (ban (ns1 v) (st0 v))
      let nvSig : Sig I := if asc then bor (ns1 v) (ban (ns1 u) (st0 u)) else bor (ns1 u) (ban (ns1 v) (st0 u))
      have Hrev1 : BuildN S2 ({nuSig} ∪ {nvSig}) 4 0 := by
        dsimp only [nuSig, nvSig]
        cases asc with
        | true =>
          have g1 := andG hns1_u hst0_v
          have g2 := orG (A := S2 ∪ {ban (ns1 u) (st0 v)}) (Or.inl hns1_v) (Or.inr rfl)
          have g3 := andG (A := S2 ∪ ({ban (ns1 u) (st0 v)} ∪ {bor (ns1 v) (ban (ns1 u) (st0 v))}))
            (Or.inl hns1_u) (Or.inl hst0_u)
          have g4 := orG (A := S2 ∪ (({ban (ns1 u) (st0 v)} ∪ {bor (ns1 v) (ban (ns1 u) (st0 v))}) ∪ {ban (ns1 u) (st0 u)}))
            (Or.inl hns1_v) (Or.inr (Or.inr rfl))
          refine relax (seq (seq (seq g1 g2) g3) g4) le_rfl ?_ le_rfl le_rfl
          rintro f (rfl | rfl)
          · exact Or.inl (Or.inl (Or.inr rfl))
          · exact Or.inr rfl
        | false =>
          have g1 := andG hns1_v hst0_v
          have g2 := orG (A := S2 ∪ {ban (ns1 v) (st0 v)}) (Or.inl hns1_u) (Or.inr rfl)
          have g3 := andG (A := S2 ∪ ({ban (ns1 v) (st0 v)} ∪ {bor (ns1 u) (ban (ns1 v) (st0 v))}))
            (Or.inl hns1_v) (Or.inl hst0_u)
          have g4 := orG (A := S2 ∪ (({ban (ns1 v) (st0 v)} ∪ {bor (ns1 u) (ban (ns1 v) (st0 v))}) ∪ {ban (ns1 v) (st0 u)}))
            (Or.inl hns1_u) (Or.inr (Or.inr rfl))
          refine relax (seq (seq (seq g1 g2) g3) g4) le_rfl ?_ le_rfl le_rfl
          rintro f (rfl | rfl)
          · exact Or.inl (Or.inl (Or.inr rfl))
          · exact Or.inr rfl
      have Hall := seq (seq Hst1B' Hrr') Hrev1
      refine relax Hall le_rfl ?_ (by simp only [List.length_cons]; omega) le_rfl
      rintro f ⟨i, hi, rfl⟩
      dsimp only [revFull, revStep]
      by_cases hu : i = u
      · simp only [hu, ↓reduceIte]; exact Or.inr (Or.inl rfl)
      · simp only [hu, ↓reduceIte]
        by_cases hv : i = v
        · simp only [hv, ↓reduceIte]; exact Or.inr (Or.inr rfl)
        · simp only [hv, ↓reduceIte]; exact Or.inl (Or.inr ⟨i, hi, rfl⟩)
    · intro nsEnd x hns i hi
      have h1 := hspecRest nsEnd x (fun k hk => by rw [← hfwd_eq k]; exact hns k hk)
      dsimp only [revFull, revStep]
      by_cases hu : i = u
      · subst i
        simp only [↓reduceIte, bor, ban]
        have hu1 := h1 u hc.1
        have hv1 := h1 v hc.2
        rw [hst1_u] at hu1
        rw [hst1_v] at hv1
        cases asc <;> simp only [hiSig, loSig, ban, bor, ↓reduceIte, Bool.false_eq_true] at hu1 hv1 ⊢ <;>
          rw [hu1, hv1] <;> cases st0 u x <;> cases st0 v x <;> rfl
      · by_cases hv : i = v
        · subst i
          simp only [hu, ↓reduceIte, bor, ban]
          have hu1 := h1 u hc.1
          have hv1 := h1 v hc.2
          rw [hst1_u] at hu1
          rw [hst1_v] at hv1
          cases asc <;> simp only [hiSig, loSig, ban, bor, ↓reduceIte, Bool.false_eq_true] at hu1 hv1 ⊢ <;>
            rw [hu1, hv1] <;> cases st0 u x <;> cases st0 v x <;> rfl
        · simp only [hu, hv, ↓reduceIte]
          rw [h1 i hi]
          have he := (boolNetStep_eval u v asc (fun k => st0 k x)).2.2 i hu hv
          exact congrArg Bool.not he

private structure DRec (m : Nat) where
  kb : Nat → Bool
  nkb : Nat → Bool

private def drecKey {m : Nat} (r : DRec m) : Nat := bitsVal r.kb m

private def drecDual {m : Nat} (r : DRec m) : Prop := ∀ j < m, r.nkb j = !(r.kb j)

private def dualStepRec {I m : Nat} (u v : Nat) (asc : Bool)
    (st : (Fin I → Bool) → Nat → DRec m) : (Fin I → Bool) → Nat → DRec m :=
  fun x =>
    let sw := if asc then dualLt (fun j => fun y => (st y v).kb j) (fun j => fun y => (st y v).nkb j)
      (fun j => fun y => (st y u).kb j) (fun j => fun y => (st y u).nkb j) m x
      else dualLt (fun j => fun y => (st y u).kb j) (fun j => fun y => (st y u).nkb j)
      (fun j => fun y => (st y v).kb j) (fun j => fun y => (st y v).nkb j) m x
    let nsw := if asc then dualGe (fun j => fun y => (st y v).kb j) (fun j => fun y => (st y v).nkb j)
      (fun j => fun y => (st y u).kb j) (fun j => fun y => (st y u).nkb j) m x
      else dualGe (fun j => fun y => (st y u).kb j) (fun j => fun y => (st y u).nkb j)
      (fun j => fun y => (st y v).kb j) (fun j => fun y => (st y v).nkb j) m x
    fun idx =>
      if idx = u then
        ⟨fun j => (sw && (st x v).kb j) || (nsw && (st x u).kb j),
         fun j => (sw && (st x v).nkb j) || (nsw && (st x u).nkb j)⟩
      else if idx = v then
        ⟨fun j => (sw && (st x u).kb j) || (nsw && (st x v).kb j),
         fun j => (sw && (st x u).nkb j) || (nsw && (st x v).nkb j)⟩
      else st x idx

private def dualRunNet {I m : Nat} : List (Nat × Nat × Bool) →
    ((Fin I → Bool) → Nat → DRec m) → ((Fin I → Bool) → Nat → DRec m)
  | [], st => st
  | (u, v, asc) :: rest, st => dualRunNet rest (dualStepRec u v asc st)

private theorem dualStepRec_eq {I m : Nat} (N u v : Nat) (asc : Bool)
    (hu : u < N) (hv : v < N) (st : (Fin I → Bool) → Nat → DRec m) (x : Fin I → Bool)
    (hdual : ∀ idx < N, drecDual (st x idx)) :
    (∀ idx < N, drecDual (dualStepRec u v asc st x idx)) ∧
    ∀ idx < N, ∀ j < m, (dualStepRec u v asc st x idx).kb j =
      (applySwap u v (swapBit (drecKey (st x u)) (drecKey (st x v)) asc) (st x) idx).kb j ∧
      (dualStepRec u v asc st x idx).nkb j =
      (applySwap u v (swapBit (drecKey (st x u)) (drecKey (st x v)) asc) (st x) idx).nkb j := by
  have hdu := hdual u hu
  have hdv := hdual v hv
  have hsw_val :
      (if asc then dualLt (fun j y => (st y v).kb j) (fun j y => (st y v).nkb j)
        (fun j y => (st y u).kb j) (fun j y => (st y u).nkb j) m x
       else dualLt (fun j y => (st y u).kb j) (fun j y => (st y u).nkb j)
        (fun j y => (st y v).kb j) (fun j y => (st y v).nkb j) m x) =
      swapBit (drecKey (st x u)) (drecKey (st x v)) asc := by
    cases asc with
    | true =>
      have h := (dualLtGe_eval (f := fun j y => (st y v).kb j) (nf := fun j y => (st y v).nkb j)
        (g := fun j y => (st y u).kb j) (ng := fun j y => (st y u).nkb j) x m hdv hdu).1
      simp only [swapBit, drecKey, ↓reduceIte]
      exact h
    | false =>
      have h := (dualLtGe_eval (f := fun j y => (st y u).kb j) (nf := fun j y => (st y u).nkb j)
        (g := fun j y => (st y v).kb j) (ng := fun j y => (st y v).nkb j) x m hdu hdv).1
      simp only [swapBit, drecKey, Bool.false_eq_true, ↓reduceIte]
      exact h
  have hnsw_val :
      (if asc then dualGe (fun j y => (st y v).kb j) (fun j y => (st y v).nkb j)
        (fun j y => (st y u).kb j) (fun j y => (st y u).nkb j) m x
       else dualGe (fun j y => (st y u).kb j) (fun j y => (st y u).nkb j)
        (fun j y => (st y v).kb j) (fun j y => (st y v).nkb j) m x) =
      !(swapBit (drecKey (st x u)) (drecKey (st x v)) asc) := by
    cases asc with
    | true =>
      have h := (dualLtGe_eval (f := fun j y => (st y v).kb j) (nf := fun j y => (st y v).nkb j)
        (g := fun j y => (st y u).kb j) (ng := fun j y => (st y u).nkb j) x m hdv hdu).2
      simp only [swapBit, drecKey, ↓reduceIte]
      rw [h]
      by_cases hlt : bitsVal (st x v).kb m < bitsVal (st x u).kb m
      · simp [hlt, show ¬ bitsVal (st x u).kb m ≤ bitsVal (st x v).kb m by omega]
      · simp [hlt, show bitsVal (st x u).kb m ≤ bitsVal (st x v).kb m by omega]
    | false =>
      have h := (dualLtGe_eval (f := fun j y => (st y u).kb j) (nf := fun j y => (st y u).nkb j)
        (g := fun j y => (st y v).kb j) (ng := fun j y => (st y v).nkb j) x m hdu hdv).2
      simp only [swapBit, drecKey, Bool.false_eq_true, ↓reduceIte]
      rw [h]
      by_cases hlt : bitsVal (st x u).kb m < bitsVal (st x v).kb m
      · simp [hlt, show ¬ bitsVal (st x v).kb m ≤ bitsVal (st x u).kb m by omega]
      · simp [hlt, show bitsVal (st x v).kb m ≤ bitsVal (st x u).kb m by omega]
  have hstep : ∀ idx < N, ∀ j < m,
      (dualStepRec u v asc st x idx).kb j =
        (applySwap u v (swapBit (drecKey (st x u)) (drecKey (st x v)) asc) (st x) idx).kb j ∧
      (dualStepRec u v asc st x idx).nkb j =
        (applySwap u v (swapBit (drecKey (st x u)) (drecKey (st x v)) asc) (st x) idx).nkb j := by
    intro idx _ j _
    simp only [dualStepRec, hsw_val, hnsw_val, applySwap]
    by_cases h1 : idx = u
    · subst h1
      cases swapBit (drecKey (st x idx)) (drecKey (st x v)) asc <;> simp
    · by_cases h2 : idx = v
      · subst h2
        cases swapBit (drecKey (st x u)) (drecKey (st x idx)) asc <;> simp [h1]
      · cases swapBit (drecKey (st x u)) (drecKey (st x v)) asc <;> simp [h1, h2]
  refine ⟨?_, hstep⟩
  intro idx hidx j hj
  rw [(hstep idx hidx j hj).1, (hstep idx hidx j hj).2]
  simp only [applySwap]
  cases swapBit (drecKey (st x u)) (drecKey (st x v)) asc with
  | false => exact hdual idx hidx j hj
  | true =>
    simp only [↓reduceIte]
    by_cases h1 : idx = u
    · simp only [h1, ↓reduceIte]; exact hdv j hj
    · simp only [h1, ↓reduceIte]
      by_cases h2 : idx = v
      · simp only [h2, ↓reduceIte]; exact hdu j hj
      · simp only [h2, ↓reduceIte]; exact hdual idx hidx j hj

private theorem dualRunNet_eq {I m : Nat} (N : Nat) (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N)
    (st : (Fin I → Bool) → Nat → DRec m) (x : Fin I → Bool)
    (hdual : ∀ idx < N, drecDual (st x idx)) :
    ∀ idx < N, ∀ j < m,
      (dualRunNet net st x idx).kb j = (runNet drecKey net (st x) idx).kb j := by
  induction net generalizing st with
  | nil => intro idx _ j _; rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    have hc := hnet (u, v, asc) List.mem_cons_self
    have hstep := dualStepRec_eq N u v asc hc.1 hc.2 st x hdual
    have hih := ih (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc')) (dualStepRec u v asc st) hstep.1
    have hagree : ∀ (net' : List (Nat × Nat × Bool)) (hnet' : ∀ c ∈ net', c.1 < N ∧ c.2.1 < N)
        (a b : Nat → DRec m),
        (∀ idx < N, ∀ j < m, (a idx).kb j = (b idx).kb j) →
        ∀ idx < N, ∀ j < m, (runNet drecKey net' a idx).kb j = (runNet drecKey net' b idx).kb j := by
      intro net'
      induction net' with
      | nil => intro _ a b hab idx hidx j hj; exact hab idx hidx j hj
      | cons c' rest' ih' =>
        rcases c' with ⟨u', v', asc'⟩
        intro hnet' a b hab
        have hc' := hnet' (u', v', asc') List.mem_cons_self
        have hkeq : ∀ idx < N, drecKey (a idx) = drecKey (b idx) := by
          intro idx hidx
          have hbv : ∀ k ≤ m, bitsVal (a idx).kb k = bitsVal (b idx).kb k := by
            intro k
            induction k with
            | zero => intro _; rfl
            | succ k ihk =>
              intro hk; simp only [bitsVal, ihk (by omega), hab idx hidx k (by omega)]
          exact hbv m (le_refl m)
        have hsw : swapBit (drecKey (a u')) (drecKey (a v')) asc' =
            swapBit (drecKey (b u')) (drecKey (b v')) asc' := by
          rw [hkeq u' hc'.1, hkeq v' hc'.2]
        apply ih' (fun c'' hc'' => hnet' c'' (List.mem_cons_of_mem _ hc''))
        intro idx hidx j hj
        simp only [applySwap, hsw]
        cases swapBit (drecKey (b u')) (drecKey (b v')) asc' with
        | false => exact hab idx hidx j hj
        | true =>
          simp only [↓reduceIte]
          by_cases h1 : idx = u'
          · simp only [h1, ↓reduceIte]; exact hab v' hc'.2 j hj
          · simp only [h1, ↓reduceIte]
            by_cases h2 : idx = v'
            · simp only [h2, ↓reduceIte]; exact hab u' hc'.1 j hj
            · simp only [h2, ↓reduceIte]; exact hab idx hidx j hj
    intro idx hidx j hj
    rw [dualRunNet, hih idx hidx j hj]
    exact hagree rest (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc')) _ _
      (fun k hk l hl => (hstep.2 k hk l hl).1) idx hidx j hj

private theorem dualNetCircuit {I m : Nat} {A : Set (Sig I)} (N : Nat)
    (net : List (Nat × Nat × Bool))
    (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N)
    (st0 : (Fin I → Bool) → Nat → DRec m)
    (hK : ∀ idx < N, ∀ j < m, (fun x => (st0 x idx).kb j) ∈ A)
    (hNK : ∀ idx < N, ∀ j < m, (fun x => (st0 x idx).nkb j) ∈ A)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    BuildN A
      ({f | ∃ idx < N, ∃ j < m, f = fun x => (dualRunNet net st0 x idx).kb j} ∪
       {f | ∃ idx < N, ∃ j < m, f = fun x => (dualRunNet net st0 x idx).nkb j})
      (net.length * (20 * m)) 0 := by
  induction net generalizing st0 A with
  | nil =>
    refine relax (idle ?_) le_rfl le_rfl (by simp) le_rfl
    rintro f (⟨idx, hidx, j, hj, rfl⟩ | ⟨idx, hidx, j, hj, rfl⟩)
    · exact hK idx hidx j hj
    · exact hNK idx hidx j hj
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    have hc := hnet (u, v, asc) List.mem_cons_self
    let swSig : Sig I := if asc then dualLt (fun j y => (st0 y v).kb j) (fun j y => (st0 y v).nkb j)
      (fun j y => (st0 y u).kb j) (fun j y => (st0 y u).nkb j) m
      else dualLt (fun j y => (st0 y u).kb j) (fun j y => (st0 y u).nkb j)
      (fun j y => (st0 y v).kb j) (fun j y => (st0 y v).nkb j) m
    let nswSig : Sig I := if asc then dualGe (fun j y => (st0 y v).kb j) (fun j y => (st0 y v).nkb j)
      (fun j y => (st0 y u).kb j) (fun j y => (st0 y u).nkb j) m
      else dualGe (fun j y => (st0 y u).kb j) (fun j y => (st0 y u).nkb j)
      (fun j y => (st0 y v).kb j) (fun j y => (st0 y v).nkb j) m
    have Hcmp : BuildN A ({swSig} ∪ {nswSig}) (8 * m) 0 := by
      cases asc with
      | true =>
        exact dualLtGeG (fun j y => (st0 y v).kb j) (fun j y => (st0 y v).nkb j)
          (fun j y => (st0 y u).kb j) (fun j y => (st0 y u).nkb j) m
          (fun j hj => hK v hc.2 j hj) (fun j hj => hNK v hc.2 j hj)
          (fun j hj => hK u hc.1 j hj) (fun j hj => hNK u hc.1 j hj) hfalse htrue
      | false =>
        exact dualLtGeG (fun j y => (st0 y u).kb j) (fun j y => (st0 y u).nkb j)
          (fun j y => (st0 y v).kb j) (fun j y => (st0 y v).nkb j) m
          (fun j hj => hK u hc.1 j hj) (fun j hj => hNK u hc.1 j hj)
          (fun j hj => hK v hc.2 j hj) (fun j hj => hNK v hc.2 j hj) hfalse htrue
    let st1 := dualStepRec u v asc st0
    let A1 := A ∪ ({swSig} ∪ {nswSig})
    have hsw1 : swSig ∈ A1 := Or.inr (Or.inl rfl)
    have hnsw1 : nswSig ∈ A1 := Or.inr (Or.inr rfl)
    let Ku : Fin m → Sig I := fun j x => (st1 x u).kb j.val
    let Kv : Fin m → Sig I := fun j x => (st1 x v).kb j.val
    let NKu : Fin m → Sig I := fun j x => (st1 x u).nkb j.val
    let NKv : Fin m → Sig I := fun j x => (st1 x v).nkb j.val
    have HKu : BuildN A1 (Set.range Ku) (m * 3) 0 := finG Ku 3 0 fun j => by
      have he : Ku j = bor (ban swSig (fun x => (st0 x v).kb j.val)) (ban nswSig (fun x => (st0 x u).kb j.val)) := by
        funext x; simp only [Ku, st1, dualStepRec, ↓reduceIte, bor, ban, swSig, nswSig]; cases asc <;> rfl
      rw [he]; exact muxG hsw1 hnsw1 (Or.inl (hK v hc.2 j.val j.isLt)) (Or.inl (hK u hc.1 j.val j.isLt))
    have HKv : BuildN (A1 ∪ Set.range Ku) (Set.range Kv) (m * 3) 0 := finG Kv 3 0 fun j => by
      by_cases huv : v = u
      · subst huv
        have he : Kv j = Ku j := rfl
        rw [he]
        exact relax (idle (Set.singleton_subset_iff.mpr (Or.inr ⟨j, rfl⟩))) le_rfl le_rfl (by omega) le_rfl
      · have he : Kv j = bor (ban swSig (fun x => (st0 x u).kb j.val)) (ban nswSig (fun x => (st0 x v).kb j.val)) := by
          funext x; simp only [Kv, st1, dualStepRec, huv, ↓reduceIte, bor, ban, swSig, nswSig]; cases asc <;> rfl
        rw [he]; exact muxG (Or.inl hsw1) (Or.inl hnsw1)
          (Or.inl (Or.inl (hK u hc.1 j.val j.isLt))) (Or.inl (Or.inl (hK v hc.2 j.val j.isLt)))
    have HNKu : BuildN (A1 ∪ (Set.range Ku ∪ Set.range Kv)) (Set.range NKu) (m * 3) 0 := finG NKu 3 0 fun j => by
      have he : NKu j = bor (ban swSig (fun x => (st0 x v).nkb j.val)) (ban nswSig (fun x => (st0 x u).nkb j.val)) := by
        funext x; simp only [NKu, st1, dualStepRec, ↓reduceIte, bor, ban, swSig, nswSig]; cases asc <;> rfl
      rw [he]; exact muxG (Or.inl hsw1) (Or.inl hnsw1)
        (Or.inl (Or.inl (hNK v hc.2 j.val j.isLt))) (Or.inl (Or.inl (hNK u hc.1 j.val j.isLt)))
    have HNKv : BuildN (A1 ∪ ((Set.range Ku ∪ Set.range Kv) ∪ Set.range NKu)) (Set.range NKv) (m * 3) 0 := finG NKv 3 0 fun j => by
      by_cases huv : v = u
      · subst huv
        have he : NKv j = NKu j := rfl
        rw [he]
        exact relax (idle (Set.singleton_subset_iff.mpr (Or.inr (Or.inr ⟨j, rfl⟩)))) le_rfl le_rfl (by omega) le_rfl
      · have he : NKv j = bor (ban swSig (fun x => (st0 x u).nkb j.val)) (ban nswSig (fun x => (st0 x v).nkb j.val)) := by
          funext x; simp only [NKv, st1, dualStepRec, huv, ↓reduceIte, bor, ban, swSig, nswSig]; cases asc <;> rfl
        rw [he]; exact muxG (Or.inl hsw1) (Or.inl hnsw1)
          (Or.inl (Or.inl (hNK u hc.1 j.val j.isLt))) (Or.inl (Or.inl (hNK v hc.2 j.val j.isLt)))
    let B1 := ({swSig} ∪ {nswSig}) ∪ (((Set.range Ku ∪ Set.range Kv) ∪ Set.range NKu) ∪ Set.range NKv)
    have Hstep : BuildN A B1 (20 * m) 0 :=
      relax (seq Hcmp (seq (seq (seq HKu HKv) HNKu) HNKv)) le_rfl le_rfl (by omega) le_rfl
    have hK1 : ∀ idx < N, ∀ j < m, (fun x => (st1 x idx).kb j) ∈ A ∪ B1 := by
      intro idx hidx j hj
      by_cases hu : idx = u
      · subst hu; exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl ⟨⟨j, hj⟩, rfl⟩))))
      · by_cases hv : idx = v
        · subst hv; exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr ⟨⟨j, hj⟩, rfl⟩))))
        · have he : (fun x => (st1 x idx).kb j) = (fun x => (st0 x idx).kb j) := by
            funext x; simp only [st1, dualStepRec, hu, hv, ↓reduceIte]
          rw [he]; exact Or.inl (hK idx hidx j hj)
    have hNK1 : ∀ idx < N, ∀ j < m, (fun x => (st1 x idx).nkb j) ∈ A ∪ B1 := by
      intro idx hidx j hj
      by_cases hu : idx = u
      · subst hu; exact Or.inr (Or.inr (Or.inl (Or.inr ⟨⟨j, hj⟩, rfl⟩)))
      · by_cases hv : idx = v
        · subst hv; exact Or.inr (Or.inr (Or.inr ⟨⟨j, hj⟩, rfl⟩))
        · have he : (fun x => (st1 x idx).nkb j) = (fun x => (st0 x idx).nkb j) := by
            funext x; simp only [st1, dualStepRec, hu, hv, ↓reduceIte]
          rw [he]; exact Or.inl (hNK idx hidx j hj)
    have Hrest := ih (fun c' hc' => hnet c' (List.mem_cons_of_mem _ hc')) st1 hK1 hNK1
      (Or.inl hfalse) (Or.inl htrue)
    refine relax (seq Hstep Hrest) le_rfl ?_ ?_ le_rfl
    · rintro f (⟨idx, hidx, j, hj, rfl⟩ | ⟨idx, hidx, j, hj, rfl⟩)
      · exact Or.inr (Or.inl ⟨idx, hidx, j, hj, rfl⟩)
      · exact Or.inr (Or.inr ⟨idx, hidx, j, hj, rfl⟩)
    · simp only [List.length_cons]
      rw [Nat.succ_mul rest.length, Nat.add_comm]

private theorem replaySwaps_card_eq {α : Type*} (N : Nat) (sws : List (Nat × Nat × Bool))
    (hsws : ∀ c ∈ sws, c.1 < N ∧ c.2.1 < N) (st : Nat → α) (P : α → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (Fin N)).filter (fun i => P (replaySwaps sws st i.val))).card =
    ((Finset.univ : Finset (Fin N)).filter (fun i => P (st i.val))).card := by
  induction sws generalizing st with
  | nil => rfl
  | cons c rest ih =>
    rcases c with ⟨u, v, sw⟩
    have hc := hsws (u, v, sw) List.mem_cons_self
    have hih := ih (fun c' hc' => hsws c' (List.mem_cons_of_mem _ hc')) (applySwap u v sw st)
    refine Eq.trans hih ?_
    cases sw with
    | false => rfl
    | true =>
      let swapFin (i : Fin N) : Fin N :=
        if i.val = u then ⟨v, hc.2⟩ else if i.val = v then ⟨u, hc.1⟩ else i
      refine Finset.card_bij (fun i _ => swapFin i) ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, applySwap, ↓reduceIte] at hi ⊢
        by_cases h1 : i.val = u
        · simp only [h1, ↓reduceIte, swapFin] at hi ⊢; exact hi
        · simp only [h1, ↓reduceIte, swapFin] at hi ⊢
          by_cases h2 : i.val = v
          · simp only [h2, ↓reduceIte] at hi ⊢; exact hi
          · simp only [h2, ↓reduceIte] at hi ⊢; exact hi
      · intro i1 _ i2 _ heq
        have hinv : ∀ i : Fin N, swapFin (swapFin i) = i := by
          intro i; apply Fin.ext
          by_cases h1 : i.val = u
          · dsimp only [swapFin]; simp only [h1, ↓reduceIte]
            by_cases huv : v = u
            · simp [huv, h1]
            · simp [huv, h1]
          · dsimp only [swapFin]; simp only [h1, ↓reduceIte]
            by_cases h2 : i.val = v
            · simp [h2]
            · simp [h1, h2]
        rw [← hinv i1, ← hinv i2, heq]
      · intro j hj
        let i := swapFin j
        have hinv : swapFin i = j := by
          apply Fin.ext
          by_cases h1 : j.val = u
          · dsimp only [i, swapFin]; simp only [h1, ↓reduceIte]
            by_cases huv : v = u
            · simp [huv, h1]
            · simp [huv, h1]
          · dsimp only [i, swapFin]; simp only [h1, ↓reduceIte]
            by_cases h2 : j.val = v
            · simp [h2]
            · simp [h1, h2]
        refine ⟨i, ?_, hinv⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, applySwap, ↓reduceIte] at hj ⊢
        by_cases h1 : j.val = u
        · dsimp only [i, swapFin]; simp only [h1, ↓reduceIte]
          by_cases huv : v = u
          · simp [huv, h1] at hj ⊢; exact hj
          · simp [huv, h1] at hj ⊢; exact hj
        · dsimp only [i, swapFin]; simp only [h1, ↓reduceIte]
          by_cases h2 : j.val = v
          · simp [h2] at hj ⊢; exact hj
          · simp [h1, h2] at hj ⊢; exact hj

private theorem netSwaps_mem {α : Type*} (key : α → Nat) (N : Nat)
    (net : List (Nat × Nat × Bool)) (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N) (st : Nat → α) :
    ∀ c ∈ netSwaps key net st, c.1 < N ∧ c.2.1 < N := by
  induction net generalizing st with
  | nil => intro c hc; simp [netSwaps] at hc
  | cons c rest ih =>
    rcases c with ⟨u, v, asc⟩
    intro c' hc'
    simp only [netSwaps, List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact hnet (u, v, asc) List.mem_cons_self
    · exact ih (fun d hd => hnet d (List.mem_cons_of_mem _ hd)) _ c' hc'

private theorem runNet_card_eq {α : Type*} (key : α → Nat) (N : Nat)
    (net : List (Nat × Nat × Bool)) (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N)
    (st : Nat → α) (P : α → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (Fin N)).filter (fun i => P (runNet key net st i.val))).card =
    ((Finset.univ : Finset (Fin N)).filter (fun i => P (st i.val))).card := by
  rw [runNet_eq_replay]
  exact replaySwaps_card_eq N (netSwaps key net st) (netSwaps_mem key N net hnet st) st P

private theorem runNet_mem_exists {α : Type*} (key : α → Nat) (N : Nat)
    (net : List (Nat × Nat × Bool)) (hnet : ∀ c ∈ net, c.1 < N ∧ c.2.1 < N)
    (st : Nat → α) (i : Fin N) :
    ∃ j : Fin N, runNet key net st i.val = st j.val := by
  classical
  have h1 := runNet_card_eq key N net hnet st (fun a => a = runNet key net st i.val)
  have hpos : 0 < ((Finset.univ : Finset (Fin N)).filter (fun k => runNet key net st k.val = runNet key net st i.val)).card :=
    Finset.card_pos.mpr ⟨i, by simp⟩
  rw [h1] at hpos
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact ⟨j, hj.symm⟩

private theorem sorted_desc_bool_iff (N : Nat) (g : Nat → Bool)
    (hsort : IsSortedBool 0 N false g) :
    ∀ k : Fin N, g k.val = true ↔ k.val < ((Finset.univ : Finset (Fin N)).filter (fun i => g i.val = true)).card := by
  intro k
  let S := (Finset.univ : Finset (Fin N)).filter (fun i => g i.val = true)
  constructor
  · intro hk
    have hsub : (Finset.univ : Finset (Fin N)).filter (fun i => i.val ≤ k.val) ⊆ S := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hi ⊢
      have := hsort i.val k.val hi k.isLt
      simp only [Nat.zero_add, Bool.false_eq_true, ↓reduceIte] at this
      exact this hk
    have hcard_le : ((Finset.univ : Finset (Fin N)).filter (fun i => i.val ≤ k.val)).card = k.val + 1 := by
      have hbij : ((Finset.univ : Finset (Fin N)).filter (fun i => i.val ≤ k.val)).card = (Finset.range (k.val + 1)).card := by
        refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
        · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; simp; omega
        · intro i1 _ i2 _ heq; exact Fin.ext heq
        · intro m hm; simp only [Finset.mem_range] at hm
          exact ⟨⟨m, by have := k.isLt; omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, rfl⟩
      rw [hbij, Finset.card_range]
    have := Finset.card_le_card hsub
    dsimp only [S] at this
    omega
  · intro hlt
    by_contra hne
    have hkf : g k.val = false := Bool.eq_false_iff.mpr hne
    have hsub : S ⊆ (Finset.univ : Finset (Fin N)).filter (fun i => i.val < k.val) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hi ⊢
      by_contra hge
      have := hsort k.val i.val (by omega) i.isLt
      simp only [Nat.zero_add, Bool.false_eq_true, ↓reduceIte] at this
      rw [hkf] at this
      cases this hi
    have hcard_lt : ((Finset.univ : Finset (Fin N)).filter (fun i => i.val < k.val)).card = k.val := by
      have hbij : ((Finset.univ : Finset (Fin N)).filter (fun i => i.val < k.val)).card = (Finset.range k.val).card := by
        refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
        · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; simp [hi]
        · intro i1 _ i2 _ heq; exact Fin.ext heq
        · intro m hm; simp only [Finset.mem_range] at hm
          exact ⟨⟨m, by have := k.isLt; omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hm, rfl⟩
      rw [hbij, Finset.card_range]
    have := Finset.card_le_card hsub
    dsimp only [S] at this
    omega

private theorem flatten_ofFn_eq {n m : Nat} (f : Fin n → Fin m → Bool) :
    (List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin m => f i j))).flatten =
    List.ofFn (fun a : Fin (n * m) =>
      f ⟨a.val / m, (Nat.div_lt_iff_lt_mul (by
          by_contra hm
          have hm0 : m = 0 := by omega
          subst hm0; simp at a; exact Fin.elim0 a)).mpr a.isLt⟩
        ⟨a.val % m, Nat.mod_lt a.val (by
          by_contra hm
          have hm0 : m = 0 := by omega
          subst hm0; simp at a; exact Fin.elim0 a)⟩) := by
  by_cases hm0 : m = 0
  · subst hm0
    have h1 : (List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin 0 => f i j))).flatten = [] := by
      rw [List.flatten_eq_nil_iff]
      intro l hl
      rcases List.mem_ofFn.mp hl with ⟨i, rfl⟩
      simp
    rw [h1]
    simp
  · have hm : 0 < m := by omega
    apply List.ext_getElem
    · simp only [List.length_flatten, List.length_ofFn, List.map_ofFn, Function.comp_def, List.sum_ofFn,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    · intro k h1 h2
      simp only [List.length_ofFn] at h2
      have hk_div : k / m < n := (Nat.div_lt_iff_lt_mul hm).mpr h2
      have hk_mod : k % m < m := Nat.mod_lt k hm
      rw [List.getElem_ofFn]
      have hgen : ∀ (r : Nat) (g : Fin r → Fin m → Bool) (idx : Nat) (hidx : idx < r * m),
          (List.ofFn (fun i : Fin r => List.ofFn (fun j : Fin m => g i j))).flatten[idx]'(by
            simp only [List.length_flatten, List.map_ofFn, Function.comp_def, List.length_ofFn,
              List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; exact hidx) =
          g ⟨idx / m, (Nat.div_lt_iff_lt_mul hm).mpr hidx⟩ ⟨idx % m, Nat.mod_lt idx hm⟩ := by
        intro r
        induction r with
        | zero => intro _ idx hidx; simp at hidx
        | succ r ih =>
          intro g idx hidx
          simp only [List.ofFn_succ, List.flatten_cons]
          by_cases hlt : idx < m
          · rw [List.getElem_append_left (by simp [hlt]), List.getElem_ofFn]
            congr 1
            · apply Fin.ext; simp [Nat.div_eq_of_lt hlt]
            · apply Fin.ext; simp [Nat.mod_eq_of_lt hlt]
          · rw [List.getElem_append_right (by simp; omega)]
            simp only [List.length_ofFn]
            have hidx' : idx - m < r * m := by rw [Nat.succ_mul] at hidx; omega
            rw [ih (fun i => g i.succ) (idx - m) hidx']
            congr 1
            · apply Fin.ext; simp only [Fin.val_succ]
              have e : idx = (idx - m) + m := by omega
              conv_rhs => rw [e]
              rw [Nat.add_div_right _ hm]
            · apply Fin.ext; dsimp only
              have e : idx = (idx - m) + m := by omega
              conv_rhs => rw [e]
              rw [Nat.add_mod_right]
      exact hgen n f k h2

private theorem solve_068 (n w : Nat) (hn : 0 < n) (q : Fin (2 ^ n)) :
    let Q := 2 ^ n
    let I := n * 2 ^ (w + 1)
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
      (valid : Fin (Q - q.val) → Fin (I + C.size))
      (outBit : Fin (Q - q.val) → Fin n → Fin (I + C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧ C.output < I + C.size ∧
      C.size ≤ 32 * (n + 1) ^ 3 * Q ∧
      PEqualNP.NotBracket.notCount C ≤ Nat.clog 2 (Q - q.val) ∧
      ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
        let inputs := (List.ofFn (fun i : Fin n => List.ofFn (fun pat : Fin (2 ^ (w + 1)) =>
          table i (fun j => pat.val.testBit j.val)))).flatten
        let sols := (Finset.univ : Finset (Fin Q)).filter (fun z => ∀ i : Fin n,
          table i (fun j => z.val.testBit (n - 1 - ((i.val + j.val) % n))) = true)
        (C.eval inputs = true ↔ sols.Nonempty) ∧
        ∀ slot, let rank := q.val + slot.val
          ((C.wires inputs).getD (valid slot).val false = true ↔ rank < sols.card) ∧
          (rank < sols.card → ∃ z ∈ sols, (sols.filter (fun y => y.val < z.val)).card = rank ∧
            ∀ pos : Fin n, (C.wires inputs).getD (outBit slot pos).val false =
              z.val.testBit (n - 1 - pos.val)) := by
  intro Q I
  let B := 2 ^ (w + 1)
  have hB_pos : 0 < B := by dsimp [B]; positivity
  have hQ_pos : 0 < Q := by dsimp [Q]; positivity
  let patIdx (z : Fin Q) (i : Fin n) : Nat :=
    bitsVal (fun j => z.val.testBit (n - 1 - ((i.val + j) % n))) (w + 1)
  have hpatIdx_lt (z : Fin Q) (i : Fin n) : patIdx z i < B :=
    bitsVal_lt _ (w + 1)
  let inWire (z : Fin Q) (i : Fin n) : Fin I :=
    ⟨i.val * B + patIdx z i, by
      have h1 : (i.val + 1) * B ≤ n * B := Nat.mul_le_mul_right B i.isLt
      rw [Nat.succ_mul] at h1
      have h2 := hpatIdx_lt z i
      dsimp only [I, B] at h1 h2 ⊢; omega⟩
  let inpSig (a : Fin I) : Sig I := fun x => x a
  let A0 : Set (Sig I) := Set.range inpSig
  have Hstart : GateBridgeN.Scheduled I id 0 0 A0 := GateBridgeN.start inpSig (fun _ _ => rfl)
  let cF : Sig I := fun _ => false
  let cT : Sig I := fun _ => true
  have Hconst : BuildN A0 ({cF} ∪ {cT}) 2 0 :=
    relax (seq (constG false) (constG true)) le_rfl le_rfl (by omega) le_rfl
  let A1 := A0 ∪ ({cF} ∪ {cT})
  let viab : Fin Q → Sig I := fun z x =>
    (List.finRange n).all (fun i => x (inWire z i))
  have Hviab : BuildN A1 (Set.range viab) (Q * n) 0 := finG viab n 0 fun z => by
    let xs : List (Sig I) := (List.finRange n).map (fun i => inpSig (inWire z i))
    have hlen : xs.length = n := by simp [xs]
    have hxs : ∀ f ∈ xs, f ∈ A1 := by
      intro f hf
      rcases List.mem_map.mp hf with ⟨i, _, rfl⟩
      exact Or.inl ⟨inWire z i, rfl⟩
    have hbuild := andListG xs hxs (Or.inr (Or.inr rfl))
    have he : (fun x => xs.all (fun f => f x)) = viab z := by
      funext x; simp [xs, viab, inpSig, List.all_map]; rfl
    rw [he, hlen] at hbuild
    exact hbuild
  let A2 := A1 ∪ Set.range viab
  let vArr : Nat → Sig I := fun k => if hk : k < Q then viab ⟨k, hk⟩ else cF
  have hvArr_mem : ∀ k < Q, vArr k ∈ A2 := fun k hk => by
    simp only [vArr, hk, ↓reduceDIte]; exact Or.inr ⟨⟨k, hk⟩, rfl⟩
  let netDesc := bitonicSort 0 n false
  have hnetDesc_mem : ∀ c ∈ netDesc, c.1 < Q ∧ c.2.1 < Q := by
    intro c hc; have h := bitonicSort_mem 0 n false c hc; dsimp [Q]; omega
  have hnetDesc_len : 4 * netDesc.length = n * (n + 1) * Q := bitonicSort_length 0 n false
  let P_prom (x : Fin I → Bool) : Prop :=
    q.val < ((Finset.univ : Finset (Fin Q)).filter (fun z => viab z x = true)).card
  obtain ⟨revMap, Hsort1, Hrev1, hrev1_spec⟩ := boolNetFwd_rev Q netDesc hnetDesc_mem vArr hvArr_mem P_prom
  let sArr : Nat → Sig I := boolNetFwd netDesc vArr
  let A3 := A2 ∪ {f | ∃ i < Q, f = sArr i}
  let Ltail := Q - q.val - 1
  let uTail : Fin Ltail → Sig I := fun j => sArr (q.val + 1 + j.val)
  have huTail_mem : ∀ j : Fin Ltail, uTail j ∈ A3 := fun j =>
    Or.inr ⟨q.val + 1 + j.val, by dsimp [Ltail] at j; omega, rfl⟩
  obtain ⟨nuTail, Hmarkov, hmarkov_spec⟩ := markovInvert Ltail uTail huTail_mem (Or.inl (Or.inl (Or.inr (Or.inl rfl))))
  let A4 := A3 ∪ Set.range nuTail
  let nsArr : Nat → Sig I := fun k =>
    if hle : k ≤ q.val then cF
    else if hlt : k < Q then nuTail ⟨k - (q.val + 1), by dsimp [Ltail]; omega⟩
    else cF
  have hnsArr_mem : ∀ k < Q, nsArr k ∈ A4 := fun k hk => by
    dsimp only [nsArr]
    by_cases hle : k ≤ q.val
    · simp only [hle, ↓reduceDIte]; exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl))))
    · simp only [hle, hk, ↓reduceDIte]; exact Or.inr ⟨⟨k - (q.val + 1), by dsimp [Ltail]; omega⟩, rfl⟩
  have hrev_built := Hrev1 (B := A2 ∪ Set.range nuTail) nsArr
    (fun i hi => Or.inl (hvArr_mem i hi))
    (fun i hi => by
      dsimp only [nsArr]
      by_cases hle : i ≤ q.val
      · simp only [hle, ↓reduceDIte]; exact Or.inl (Or.inl (Or.inr (Or.inl rfl)))
      · simp only [hle, hi, ↓reduceDIte]; exact Or.inr ⟨⟨i - (q.val + 1), by dsimp [Ltail]; omega⟩, rfl⟩)
  have hrev_A4 : BuildN A4 {f | ∃ i < Q, f = revMap nsArr i} (6 * netDesc.length) 0 :=
    relax hrev_built (by
      rintro f ((hf | hf) | hf)
      · exact Or.inl (Or.inl hf)
      · exact Or.inr hf
      · exact Or.inl (Or.inr hf)) le_rfl le_rfl le_rfl
  let nvArr : Nat → Sig I := revMap nsArr
  let A5 := A4 ∪ {f | ∃ i < Q, f = nvArr i}
  let initRec : (Fin I → Bool) → Nat → DRec (n + 1) := fun x idx =>
    if hidx : idx < Q then
      ⟨fun j => if j < n then idx.testBit j else nvArr idx x,
       fun j => if j < n then !(idx.testBit j) else vArr idx x⟩
    else ⟨fun _ => false, fun _ => true⟩
  have hinitK : ∀ idx < Q, ∀ j < n + 1, (fun x => (initRec x idx).kb j) ∈ A5 := by
    intro idx hidx j hj
    dsimp only [initRec]
    simp only [hidx, ↓reduceDIte]
    by_cases hjn : j < n
    · simp only [hjn, ↓reduceIte]
      cases idx.testBit j
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl)))))
    · simp only [hjn, ↓reduceIte]
      exact Or.inr ⟨idx, hidx, rfl⟩
  have hinitNK : ∀ idx < Q, ∀ j < n + 1, (fun x => (initRec x idx).nkb j) ∈ A5 := by
    intro idx hidx j hj
    dsimp only [initRec]
    simp only [hidx, ↓reduceDIte]
    by_cases hjn : j < n
    · simp only [hjn, ↓reduceIte]
      cases !(idx.testBit j)
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl)))))
    · simp only [hjn, ↓reduceIte]
      exact Or.inl (Or.inl (Or.inl (hvArr_mem idx hidx)))
  let netAsc := bitonicSort 0 n true
  have hnetAsc_mem : ∀ c ∈ netAsc, c.1 < Q ∧ c.2.1 < Q := by
    intro c hc; have h := bitonicSort_mem 0 n true c hc; dsimp [Q]; omega
  have hnetAsc_len : 4 * netAsc.length = n * (n + 1) * Q := bitonicSort_length 0 n true
  have Hsort2 := dualNetCircuit Q netAsc hnetAsc_mem initRec hinitK hinitNK
    (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl))))))
    (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl))))))
  have H01 := seq Hconst Hviab
  have H012 := seq H01 (relax Hsort1 (by intro s hs; rcases hs with (hs | hs) | hs; exact Or.inl hs; exact Or.inr (Or.inl hs); exact Or.inr (Or.inr hs)) le_rfl le_rfl le_rfl)
  have H0123 := seq H012 (relax Hmarkov (by
    intro s hs; rcases hs with ((hs | hs) | hs) | hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl (Or.inl hs))
    · exact Or.inr (Or.inl (Or.inr hs))
    · exact Or.inr (Or.inr hs)) le_rfl le_rfl le_rfl)
  have H01234 := seq H0123 (relax hrev_A4 (by
    intro s hs; rcases hs with (((hs | hs) | hs) | hs) | hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl (Or.inl (Or.inl hs)))
    · exact Or.inr (Or.inl (Or.inl (Or.inr hs)))
    · exact Or.inr (Or.inl (Or.inr hs))
    · exact Or.inr (Or.inr hs)) le_rfl le_rfl le_rfl)
  have H012345 := seq H01234 (relax Hsort2 (by
    intro s hs; rcases hs with ((((hs | hs) | hs) | hs) | hs) | hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl hs))))
    · exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr hs))))
    · exact Or.inr (Or.inl (Or.inl (Or.inr hs)))
    · exact Or.inr (Or.inl (Or.inr hs))
    · exact Or.inr (Or.inr hs)) le_rfl le_rfl le_rfl)
  obtain ⟨cSize, hcSize, cNots, hcNots, Hsched⟩ := H012345.run Hstart le_rfl
  obtain ⟨gs, hgs_len, hgs_not, hgs_rb, hgs_f2, hgs_wires⟩ := Hsched
  have hQ_ge2 : 2 ≤ Q := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    simpa [Q] using this
  have hnot_bound : cNots ≤ Nat.clog 2 (Q - q.val) := by
    have h1 : markovNotCount Ltail ≤ Nat.clog 2 (Ltail + 1) := markovNotCount_le_clog Ltail
    have h2 : Ltail + 1 = Q - q.val := by dsimp [Ltail]; omega
    rw [h2] at h1
    omega
  have hsize_bound : cSize ≤ 32 * (n + 1) ^ 3 * Q := by
    have hnd : netDesc.length ≤ n * (n + 1) * Q := by omega
    have hna : netAsc.length * (20 * (n + 1)) = 5 * n * (n + 1) ^ 2 * Q := by
      have e1 : 4 * (netAsc.length * (20 * (n + 1))) = 4 * (5 * n * (n + 1) ^ 2 * Q) := by
        calc 4 * (netAsc.length * (20 * (n + 1)))
            = (4 * netAsc.length) * (20 * (n + 1)) := by ring
          _ = (n * (n + 1) * Q) * (20 * (n + 1)) := by rw [hnetAsc_len]
          _ = 4 * (5 * n * (n + 1) ^ 2 * Q) := by ring
      omega
    have hltail : Ltail ≤ Q := by dsimp [Ltail]; omega
    have hb1 : 2 + Q * n + 2 * netDesc.length + 5 * Ltail + 6 * netDesc.length +
        netAsc.length * (20 * (n + 1)) ≤
        (7 + n + 8 * n * (n + 1) + 5 * n * (n + 1) ^ 2) * Q := by
      have : (7 + n + 8 * n * (n + 1) + 5 * n * (n + 1) ^ 2) * Q =
          7 * Q + Q * n + 8 * (n * (n + 1) * Q) + 5 * n * (n + 1) ^ 2 * Q := by ring
      omega
    have hb2 : 7 + n + 8 * n * (n + 1) + 5 * n * (n + 1) ^ 2 ≤ 32 * (n + 1) ^ 3 := by
      have e : 32 * (n + 1) ^ 3 = 32 * n ^ 3 + 96 * n ^ 2 + 96 * n + 32 := by ring
      have e2 : 7 + n + 8 * n * (n + 1) + 5 * n * (n + 1) ^ 2 =
          5 * n ^ 3 + 18 * n ^ 2 + 14 * n + 7 := by ring
      omega
    have hb3 : (7 + n + 8 * n * (n + 1) + 5 * n * (n + 1) ^ 2) * Q ≤ 32 * (n + 1) ^ 3 * Q :=
      Nat.mul_le_mul_right Q hb2
    omega
  have hs_mem : ∀ k < Q, sArr k ∈ A0 ∪ (((((({cF} ∪ {cT}) ∪ Set.range viab) ∪ {f | ∃ i < Q, f = sArr i}) ∪ Set.range nuTail) ∪ {f | ∃ i < Q, f = nvArr i}) ∪ ({f | ∃ idx < Q, ∃ j < n + 1, f = fun x => (dualRunNet netAsc initRec x idx).kb j} ∪ {f | ∃ idx < Q, ∃ j < n + 1, f = fun x => (dualRunNet netAsc initRec x idx).nkb j})) :=
    fun k hk => Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, rfl⟩))))
  have hout_mem : ∀ idx < Q, ∀ j < n + 1, (fun x => (dualRunNet netAsc initRec x idx).kb j) ∈ A0 ∪ (((((({cF} ∪ {cT}) ∪ Set.range viab) ∪ {f | ∃ i < Q, f = sArr i}) ∪ Set.range nuTail) ∪ {f | ∃ i < Q, f = nvArr i}) ∪ ({f | ∃ idx < Q, ∃ j < n + 1, f = fun x => (dualRunNet netAsc initRec x idx).kb j} ∪ {f | ∃ idx < Q, ∃ j < n + 1, f = fun x => (dualRunNet netAsc initRec x idx).nkb j})) :=
    fun idx hidx j hj => Or.inr (Or.inr (Or.inl ⟨idx, hidx, j, hj, rfl⟩))
  obtain ⟨outW, houtW_lt, houtW_val⟩ := hgs_wires (sArr 0) (hs_mem 0 hQ_pos)
  have hval_ex : ∀ slot : Fin (Q - q.val), ∃ wIdx : Fin (I + gs.length),
      ∀ x : Fin I → Bool, ((Circuit.mk gs outW).wires (List.ofFn x)).getD wIdx.val false = sArr (q.val + slot.val) x := by
    intro slot
    obtain ⟨wi, hwi_lt, hwi_val⟩ := hgs_wires (sArr (q.val + slot.val)) (hs_mem (q.val + slot.val) (by omega))
    exact ⟨⟨wi, by omega⟩, hwi_val⟩
  have hout_ex : ∀ (slot : Fin (Q - q.val)) (pos : Fin n), ∃ wIdx : Fin (I + gs.length),
      ∀ x : Fin I → Bool, ((Circuit.mk gs outW).wires (List.ofFn x)).getD wIdx.val false =
        (dualRunNet netAsc initRec x (q.val + slot.val)).kb (n - 1 - pos.val) := by
    intro slot pos
    obtain ⟨wi, hwi_lt, hwi_val⟩ := hgs_wires
      (fun x => (dualRunNet netAsc initRec x (q.val + slot.val)).kb (n - 1 - pos.val))
      (hout_mem (q.val + slot.val) (by omega) (n - 1 - pos.val) (by omega))
    exact ⟨⟨wi, by omega⟩, hwi_val⟩
  choose valid hvalid using hval_ex
  choose outBit houtBit using hout_ex
  let C : Circuit := ⟨gs, outW⟩
  refine ⟨C, valid, outBit, hgs_f2, hgs_rb, by change outW < I + gs.length; omega,
    by change gs.length ≤ _; omega, by change notCount ⟨gs, 0⟩ ≤ _; omega, ?_⟩
  intro table inputs sols
  let x : Fin I → Bool := fun a =>
    table ⟨a.val / B, (Nat.div_lt_iff_lt_mul hB_pos).mpr a.isLt⟩
      (fun j => (a.val % B).testBit j.val)
  have hinputs : inputs = List.ofFn x := by
    dsimp only [inputs, x]
    exact flatten_ofFn_eq (fun i pat => table i (fun j => pat.val.testBit j.val))
  have hviab_iff : ∀ z : Fin Q, viab z x = true ↔ z ∈ sols := by
    intro z
    simp only [viab, List.all_eq_true, List.mem_finRange, true_implies, sols, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h i
      have hi := h i
      dsimp only [x, inWire] at hi
      have hdiv : (i.val * B + patIdx z i) / B = i.val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB_pos, Nat.div_eq_of_lt (hpatIdx_lt z i), Nat.zero_add]
      have hmod : (i.val * B + patIdx z i) % B = patIdx z i := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (hpatIdx_lt z i)]
      have htb : (fun j : Fin (w + 1) => ((i.val * B + patIdx z i) % B).testBit j.val) =
          (fun j : Fin (w + 1) => z.val.testBit (n - 1 - ((i.val + j.val) % n))) := by
        funext j; rw [hmod]; exact bitsVal_testBit _ (w + 1) j.val j.isLt
      have hfi : (⟨(i.val * B + patIdx z i) / B, (Nat.div_lt_iff_lt_mul hB_pos).mpr (inWire z i).isLt⟩ : Fin n) = i :=
        Fin.ext hdiv
      rw [hfi, htb] at hi
      exact hi
    · intro h i
      dsimp only [x, inWire]
      have hdiv : (i.val * B + patIdx z i) / B = i.val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB_pos, Nat.div_eq_of_lt (hpatIdx_lt z i), Nat.zero_add]
      have hmod : (i.val * B + patIdx z i) % B = patIdx z i := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (hpatIdx_lt z i)]
      have htb : (fun j : Fin (w + 1) => ((i.val * B + patIdx z i) % B).testBit j.val) =
          (fun j : Fin (w + 1) => z.val.testBit (n - 1 - ((i.val + j.val) % n))) := by
        funext j; rw [hmod]; exact bitsVal_testBit _ (w + 1) j.val j.isLt
      have hfi : (⟨(i.val * B + patIdx z i) / B, (Nat.div_lt_iff_lt_mul hB_pos).mpr (inWire z i).isLt⟩ : Fin n) = i :=
        Fin.ext hdiv
      rw [hfi, htb]
      exact h i
  have hs_sort : IsSortedBool 0 Q false (fun k => sArr k x) :=
    bitonicSort_sorted_bool 0 n false (fun k => vArr k x)
  have hs_count : ((Finset.univ : Finset (Fin Q)).filter (fun i => sArr i.val x = true)).card = sols.card := by
    have h1 := runNet_card_eq (fun b : Bool => b.toNat) Q netDesc hnetDesc_mem (fun k => vArr k x) (fun b => b = true)
    change ((Finset.univ : Finset (Fin Q)).filter (fun i => runNet (fun b : Bool => b.toNat) netDesc (fun k => vArr k x) i.val = true)).card = sols.card
    rw [h1]
    congr 1; ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, vArr, z.isLt, ↓reduceDIte]
    exact hviab_iff z
  have hs_iff : ∀ k : Fin Q, sArr k.val x = true ↔ k.val < sols.card := by
    intro k
    rw [sorted_desc_bool_iff Q (fun idx => sArr idx x) hs_sort k, hs_count]
  constructor
  · change (C.wires inputs).getD outW false = true ↔ sols.Nonempty
    rw [hinputs]
    have hev : (C.wires (List.ofFn x)).getD outW false = sArr 0 x := houtW_val x
    rw [hev, hs_iff ⟨0, hQ_pos⟩, Finset.card_pos]
  · intro slot rank
    have hrank_lt : rank < Q := by dsimp [rank]; omega
    constructor
    · rw [hinputs, hvalid slot x, hs_iff ⟨rank, hrank_lt⟩]
    · intro hrank_sols
      have hq_sols : q.val < sols.card := by dsimp [rank] at hrank_sols; omega
      have hu_sort : isDecSorted Ltail uTail x := by
        intro i j hij hj_true
        have hjlt : j.val < Ltail := j.isLt
        have := hs_sort (q.val + 1 + i.val) (q.val + 1 + j.val) (by omega) (by dsimp [Ltail] at hjlt; omega)
        simp only [Nat.zero_add, Bool.false_eq_true, ↓reduceIte] at this
        exact this hj_true
      have hns_exact : ∀ k < Q, nsArr k x = !(sArr k x) := by
        intro k hk
        dsimp only [nsArr]
        by_cases hle : k ≤ q.val
        · simp only [hle, ↓reduceDIte, cF]
          have hst : sArr k x = true := (hs_iff ⟨k, hk⟩).mpr (by dsimp; omega)
          rw [hst]; rfl
        · simp only [hle, hk, ↓reduceDIte]
          have hm := hmarkov_spec x hu_sort ⟨k - (q.val + 1), by dsimp [Ltail]; omega⟩
          have he : q.val + 1 + (k - (q.val + 1)) = k := by omega
          simpa [uTail, he] using hm
      have hnv_exact : ∀ k < Q, nvArr k x = !(vArr k x) :=
        hrev1_spec nsArr x hns_exact
      have hinit_dual : ∀ idx < Q, drecDual (initRec x idx) := by
        intro idx hidx j hj
        dsimp only [initRec]
        simp only [hidx, ↓reduceDIte]
        by_cases hjn : j < n
        · simp only [hjn, ↓reduceIte]
        · simp only [hjn, ↓reduceIte, hnv_exact idx hidx, Bool.not_not]
      have hdual_eq := dualRunNet_eq Q netAsc hnetAsc_mem initRec x hinit_dual
      have hkey_formula : ∀ idx : Fin Q, drecKey (initRec x idx.val) =
          (if idx ∈ sols then 0 else Q) + idx.val := by
        intro idx
        have hbv_n : bitsVal (initRec x idx.val).kb n = idx.val := by
          have hlt_idx : idx.val < 2 ^ n := idx.isLt
          have hlt_bv : bitsVal (initRec x idx.val).kb n < 2 ^ n := bitsVal_lt _ n
          apply Nat.eq_of_testBit_eq
          intro b
          by_cases hbn : b < n
          · rw [bitsVal_testBit _ n b hbn]
            simp [initRec, idx.isLt, hbn]
          · rw [Nat.testBit_lt_two_pow (by calc bitsVal (initRec x idx.val).kb n < 2 ^ n := hlt_bv
              _ ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)),
              Nat.testBit_lt_two_pow (by calc idx.val < 2 ^ n := hlt_idx
              _ ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega))]
        simp only [drecKey, bitsVal, hbv_n]
        have htop : (initRec x idx.val).kb n = !(decide (idx ∈ sols)) := by
          simp only [initRec, idx.isLt, ↓reduceDIte, Nat.lt_irrefl, ↓reduceIte, hnv_exact idx.val idx.isLt,
            vArr]
          cases hv : viab idx x with
          | true =>
            have hmem : idx ∈ sols := (hviab_iff idx).mp hv
            simp [hmem]
          | false =>
            have hnot : idx ∉ sols := fun hm => by rw [(hviab_iff idx).mpr hm] at hv; cases hv
            simp [hnot]
        rw [htop]
        by_cases hmem : idx ∈ sols
        · simp [hmem]
        · simp [hmem, Q, Nat.add_comm]
      let sortedRec := runNet drecKey netAsc (initRec x)
      obtain ⟨z, hz_eq⟩ := runNet_mem_exists drecKey Q netAsc hnetAsc_mem (initRec x) ⟨rank, hrank_lt⟩
      change sortedRec rank = initRec x z.val at hz_eq
      have hsorted_asc : ∀ i j, i ≤ j → j < Q → drecKey (sortedRec i) ≤ drecKey (sortedRec j) :=
        bitonicSort_sorted drecKey n (initRec x)
      have hkey_inj : ∀ a b : Fin Q, drecKey (initRec x a.val) = drecKey (initRec x b.val) → a = b := by
        intro a b heq
        rw [hkey_formula a, hkey_formula b] at heq
        apply Fin.ext
        by_cases ha : a ∈ sols <;> by_cases hb : b ∈ sols <;> simp only [ha, hb, ↓reduceIte, Nat.zero_add] at heq
        · exact heq
        · have := a.isLt; omega
        · have := b.isLt; omega
        · omega
      have hstrict : ∀ i j : Fin Q, i.val < j.val → drecKey (sortedRec i.val) < drecKey (sortedRec j.val) := by
        intro i j hij
        have hle := hsorted_asc i.val j.val (by omega) j.isLt
        by_contra hnotlt
        have heq : drecKey (sortedRec i.val) = drecKey (sortedRec j.val) := by omega
        have hcnt_le : ((Finset.univ : Finset (Fin Q)).filter (fun k => drecKey (sortedRec k.val) = drecKey (sortedRec i.val))).card ≥ 2 := by
          have hsub : ({i, j} : Finset (Fin Q)) ⊆ (Finset.univ : Finset (Fin Q)).filter (fun k => drecKey (sortedRec k.val) = drecKey (sortedRec i.val)) := by
            intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
            rcases hk with rfl | rfl <;> simp [heq]
          have hne : i ≠ j := fun h => by subst h; omega
          have := Finset.card_le_card hsub
          rw [Finset.card_pair hne] at this; exact this
        have hcnt_eq := runNet_card_eq drecKey Q netAsc hnetAsc_mem (initRec x) (fun r => drecKey r = drecKey (sortedRec i.val))
        rw [hcnt_eq] at hcnt_le
        obtain ⟨a0, ha0⟩ := runNet_mem_exists drecKey Q netAsc hnetAsc_mem (initRec x) i
        change sortedRec i.val = initRec x a0.val at ha0
        have hsub1 : (Finset.univ : Finset (Fin Q)).filter (fun k => drecKey (initRec x k.val) = drecKey (sortedRec i.val)) ⊆ {a0} := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rw [ha0] at hk
          simp [hkey_inj k a0 hk]
        have := Finset.card_le_card hsub1
        simp at this
        omega
      have hlt_card : ((Finset.univ : Finset (Fin Q)).filter (fun y => drecKey (initRec x y.val) < drecKey (initRec x z.val))).card = rank := by
        have h1 := runNet_card_eq drecKey Q netAsc hnetAsc_mem (initRec x) (fun r => drecKey r < drecKey (initRec x z.val))
        rw [← h1]
        have heq_set : (Finset.univ : Finset (Fin Q)).filter (fun i => drecKey (sortedRec i.val) < drecKey (initRec x z.val)) =
            (Finset.univ : Finset (Fin Q)).filter (fun i => i.val < rank) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hz_eq]
          constructor
          · intro hlt
            by_contra hge
            have hle := hsorted_asc rank i.val (by omega) i.isLt
            omega
          · intro hlt
            exact hstrict i ⟨rank, hrank_lt⟩ hlt
        rw [heq_set]
        have hbij : ((Finset.univ : Finset (Fin Q)).filter (fun i => i.val < rank)).card = (Finset.range rank).card := by
          refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
          · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; simp [hi]
          · intro i1 _ i2 _ heq; exact Fin.ext heq
          · intro m hm; simp only [Finset.mem_range] at hm
            exact ⟨⟨m, by omega⟩, by simp [hm], rfl⟩
        rw [hbij, Finset.card_range]
      have hz_mem : z ∈ sols := by
        by_contra hnot
        have hsub : sols ⊆ (Finset.univ : Finset (Fin Q)).filter (fun y => drecKey (initRec x y.val) < drecKey (initRec x z.val)) := by
          intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hkey_formula y, hkey_formula z]
          simp only [hy, hnot, ↓reduceIte, Nat.zero_add]
          have := y.isLt; omega
        have := Finset.card_le_card hsub
        omega
      have hsols_lt : (sols.filter (fun y => y.val < z.val)).card = rank := by
        rw [← hlt_card]
        congr 1; ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hkey_formula y, hkey_formula z]
        simp only [hz_mem, ↓reduceIte, Nat.zero_add]
        by_cases hy : y ∈ sols
        · simp [hy]
        · simp only [hy, ↓reduceIte, false_and, false_iff]
          have := z.isLt; omega
      refine ⟨z, hz_mem, hsols_lt, ?_⟩
      intro pos
      rw [hinputs, houtBit slot pos x, hdual_eq rank hrank_lt (n - 1 - pos.val) (by omega)]
      change (sortedRec rank).kb (n - 1 - pos.val) = z.val.testBit (n - 1 - pos.val)
      rw [hz_eq]
      simp only [initRec, z.isLt, ↓reduceDIte, show n - 1 - pos.val < n by omega, ↓reduceIte]

end Circuit068

end PEqualNP.Outside.L_clb_068_aux

theorem PEqualNP.Outside.L_clb_068 : ∀ (n w : ℕ) (hn : 0 < n) (q : Fin (2 ^ n)),
  let Q := 2 ^ n
  let I := n * 2 ^ (w + 1)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
    (valid : Fin (Q - q.val) → Fin (I + C.size))
    (outBit : Fin (Q - q.val) → Fin n → Fin (I + C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧ C.output < I + C.size ∧
    C.size ≤ 32 * (n + 1) ^ 3 * Q ∧
    PEqualNP.NotBracket.notCount C ≤ Nat.clog 2 (Q - q.val) ∧
    ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := (List.ofFn (fun i : Fin n => List.ofFn (fun pat : Fin (2 ^ (w + 1)) =>
        table i (fun j => pat.val.testBit j.val)))).flatten
      let sols := (Finset.univ : Finset (Fin Q)).filter (fun z => ∀ i : Fin n,
        table i (fun j => z.val.testBit (n - 1 - ((i.val + j.val) % n))) = true)
      (C.eval inputs = true ↔ sols.Nonempty) ∧
      ∀ slot, let rank := q.val + slot.val
        ((C.wires inputs).getD (valid slot).val false = true ↔ rank < sols.card) ∧
        (rank < sols.card → ∃ z ∈ sols, (sols.filter (fun y => y.val < z.val)).card = rank ∧
          ∀ pos : Fin n, (C.wires inputs).getD (outBit slot pos).val false =
            z.val.testBit (n - 1 - pos.val)) := by
  intro n w hn q
  exact PEqualNP.Outside.L_clb_068_aux.Circuit068.solve_068 n w hn q
