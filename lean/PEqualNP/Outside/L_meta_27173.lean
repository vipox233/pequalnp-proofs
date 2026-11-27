import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27173
open Finset
abbrev Cell (N : ℕ) := Fin N × Fin N
abbrev Grid (N : ℕ) := Fin N → Fin N → Bool
abbrev Match (N q : ℕ) := Fin q → Equiv.Perm (Fin N)

def edits {N : ℕ} (B H : Grid N) : Finset (Cell N) :=
  univ.filter fun z => H z.1 z.2 ≠ B z.1 z.2

def score {N q : ℕ} (B : Grid N) (f : Match N q) (H : Grid N) (D : Finset (Fin q)) : ℕ :=
  (univ.filter fun z : Cell N => H z.1 z.2 ≠
    xor (B z.1 z.2) (decide (z.2 ∈ D.image (fun j => f j z.1)))).card

@[simp] theorem score_zero {N q} (B : Grid N) (f : Match N q) (H : Grid N) :
    score B f H ∅ = (edits B H).card := by simp [score, edits]

def matching {N q} (f : Match N q) (j : Fin q) : Finset (Cell N) :=
  univ.image fun x => (x, f j x)

@[simp] theorem mem_matching {N q} {f : Match N q} {j : Fin q} {z : Cell N} :
    z ∈ matching f j ↔ f j z.1 = z.2 := by
  rcases z with ⟨x,y⟩
  simp [matching]

@[simp] theorem matching_card {N q} (f : Match N q) (j : Fin q) :
    (matching f j).card = N := by
  rw [matching, card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
  simp

theorem matches_disjoint {N q} (f : Match N q) (hf : ∀ x, Function.Injective fun j => f j x)
    {i j : Fin q} (hne : i ≠ j) : Disjoint (matching f i) (matching f j) := by
  apply disjoint_left.mpr
  intro z hi hj
  exact hne (hf z.1 ((mem_matching.mp hi).trans (mem_matching.mp hj).symm))

theorem counted {N q} (f : Match N q) (hf : ∀ x, Function.Injective fun j => f j x)
    (A : Finset (Cell N)) (D : Finset (Fin q)) :
    (A ∩ D.biUnion (matching f)).card = ∑ j ∈ D, (A ∩ matching f j).card := by
  rw [inter_biUnion, card_biUnion]
  intro i _ j _ hij
  exact (matches_disjoint f hf hij).mono inter_subset_right inter_subset_right

theorem score_eq {N q} (B : Grid N) (f : Match N q)
    (hf : ∀ x, Function.Injective fun j => f j x) (H : Grid N) (D : Finset (Fin q)) :
    score B f H D + 2 * (∑ j ∈ D, (edits B H ∩ matching f j).card) =
      (edits B H).card + N * D.card := by
  classical
  let A := edits B H
  let U := D.biUnion (matching f)
  have memU (z : Cell N) : z ∈ U ↔ z.2 ∈ D.image (fun j => f j z.1) := by
    simp [U]
  have cU : U.card = N * D.card := by
    unfold U
    rw [card_biUnion]
    · simp [Nat.mul_comm]
    · intro i _ j _ hij
      exact matches_disjoint f hf hij
  have hs : score B f H D = ((A \ U) ∪ (U \ A)).card := by
    unfold score
    congr 1
    ext z
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_sdiff, A, edits]
    simp only [memU]
    by_cases hz : z.2 ∈ D.image (fun j => f j z.1) <;>
      cases h : H z.1 z.2 <;> cases b : B z.1 z.2 <;> simp [hz]
  have hd : Disjoint (A \ U) (U \ A) := by
    apply disjoint_left.mpr
    exact fun _ hx hy => (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).1
  have ha := card_sdiff_add_card_inter A U
  have hu := card_sdiff_add_card_inter U A
  rw [inter_comm U A] at hu
  rw [hs,card_union_of_disjoint hd,← counted f hf]
  change (A \ U).card + (U \ A).card + 2*(A ∩ U).card = A.card + N * D.card
  omega

theorem aggregate_score {N q m} (B : Grid N) (f : Match N q)
    (hf : ∀ x, Function.Injective fun j => f j x) (H : Fin m → Grid N) (D : Finset (Fin q)) :
    (∑ s, score B f (H s) D) + 2*(∑ j ∈ D, ∑ s, (edits B (H s) ∩ matching f j).card) =
      (∑ s, (edits B (H s)).card) + m*N*D.card := by
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin m))) rfl
    (fun s _ => score_eq B f hf (H s) D)
  simp only [sum_add_distrib, ←mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have swap : (∑ j ∈ D, ∑ s, (edits B (H s) ∩ matching f j).card) =
      ∑ s, ∑ j ∈ D, (edits B (H s) ∩ matching f j).card := sum_comm
  rw [swap]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem aggregate_bounded {N q m} (B : Grid N) (f : Match N q)
    (hf : ∀ x, Function.Injective fun j => f j x) (H : Fin m → Grid N) :
    (∑ j, ∑ s, (edits B (H s) ∩ matching f j).card) ≤ ∑ s, (edits B (H s)).card := by
  rw [sum_comm]
  apply sum_le_sum
  intro s _
  rw [←counted f hf]
  exact card_le_card inter_subset_left

end PEqualNP.Outside.L_meta_27173

namespace PEqualNP.Outside.L_meta_27173
open Finset

theorem balanced_plan {q t M : ℕ} (hq : 0 < q) (ht : t ≤ q) :
    let gain := (2*t-q)*(M/q)+(M%q-2*(q-t))
    ∃ c : Fin q → ℕ, (∑ j, c j) ≤ M ∧
      (∀ D : Finset (Fin q), D.card = t →
        (∑ j, c j) + gain ≤ 2*(∑ j ∈ D, c j)) ∧
      ∃ D : Finset (Fin q), D.card = t ∧
        (∑ j, c j) + gain = 2*(∑ j ∈ D, c j) := by
  classical
  dsimp only
  let a := M / q
  let b := M % q
  have splitM : b + q*a = M := Nat.mod_add_div M q
  have hb : b < q := Nat.mod_lt M hq
  change ∃ c : Fin q → ℕ, (∑ j, c j) ≤ M ∧
      (∀ D : Finset (Fin q), D.card = t →
        (∑ j, c j) + ((2*t-q)*a+(b-2*(q-t))) ≤ 2*(∑ j ∈ D, c j)) ∧
      ∃ D : Finset (Fin q), D.card = t ∧
        (∑ j, c j) + ((2*t-q)*a+(b-2*(q-t))) = 2*(∑ j ∈ D, c j)
  have choose_set {n : ℕ} (h : n ≤ q) : ∃ D : Finset (Fin q), D.card = n := by
    obtain ⟨D, _, hc⟩ := exists_subset_card_eq (s := (univ : Finset (Fin q))) (by simpa using h)
    exact ⟨D,hc⟩
  obtain ⟨T,hT⟩ := choose_set ht
  by_cases half : 2*t ≤ q
  · have h1 : 2*t-q=0 := by omega
    have h2 : b-2*(q-t)=0 := by omega
    exact ⟨fun _ => 0, by simp, by simp [h1,h2], T,hT,by simp [h1,h2]⟩
  have baseEq : (2*t-q)*a + q*a = 2*(t*a) := by
    rw [←Nat.add_mul, Nat.sub_add_cancel (by omega : q ≤ 2*t), Nat.mul_assoc]
  by_cases small : b ≤ 2*(q-t)
  · have h2 : b-2*(q-t)=0 := by omega
    refine ⟨fun _ => a, ?_, ?_, T,hT,?_⟩
    · simpa using (show q*a ≤ M by omega)
    · intro D hD
      simp [hD, h2]
      omega
    · simp [hT,h2]
      omega
  obtain ⟨B,hB⟩ := choose_set (Nat.le_of_lt hb)
  let c : Fin q → ℕ := fun j => a + if j ∈ B then 1 else 0
  have wc (D : Finset (Fin q)) : ∑ j ∈ D, c j = D.card*a + (D ∩ B).card := by
    simp [c, Finset.sum_add_distrib]
  have total : ∑ j, c j = q*a+b := by
    simpa [hB] using wc univ
  have lower (D : Finset (Fin q)) (hD : D.card = t) : b-(q-t) ≤ (D ∩ B).card := by
    have hs : B \ D ⊆ univ \ D := sdiff_subset_sdiff_left D (subset_univ B)
    have hh := card_le_card hs
    have eqC : ((univ : Finset (Fin q)) \ D).card = q-t := by
      rw [card_sdiff_of_subset (subset_univ D), hD, card_fin]
    rw [eqC] at hh
    have eqB := card_sdiff_add_card_inter B D
    rw [inter_comm B D,hB] at eqB
    omega
  have hground : q*a + b + ((2*t-q)*a+(b-2*(q-t))) = 2*(t*a+(b-(q-t))) := by omega
  refine ⟨c, by rw [total]; omega, ?_, ?_⟩
  · intro D hD
    rw [total,hground,wc,hD]
    have := lower D hD
    omega
  obtain ⟨O,hOB,hO⟩ := exists_subset_card_eq (s:=B) (show q-t ≤ B.card by rw [hB]; omega)
  let D : Finset (Fin q) := univ \ O
  have hD : D.card = t := by
    simp [D,card_sdiff_of_subset (subset_univ O),hO]; omega
  have hDB : (D ∩ B).card = b-(q-t) := by
    have hs : D ∩ B = B \ O := by ext x; simp [D, and_comm]
    rw [hs,card_sdiff_of_subset hOB,hB,hO]
  refine ⟨D,hD,?_⟩
  rw [total,hground,wc,hD,hDB]

end PEqualNP.Outside.L_meta_27173

namespace PEqualNP.Outside.L_meta_27173

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def Legal (N : Nat) (C : Circuit) : Prop :=
  ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
       (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))

def Table {N : Nat} (C : Circuit) (x y : Fin N) : Bool :=
  C.eval (Represents.oneEach x y)

def push (N : Nat) (C : Circuit) (g : Gate) : Circuit :=
  ⟨C.gates ++ [g], N+N+C.size⟩

theorem pushSize (N : Nat) (C : Circuit) (g : Gate) : (push N C g).size = C.size + 1 := by
  simp [push,Circuit.size]

theorem pushPrefix (N : Nat) (C : Circuit) (g : Gate) : C.gates <+: (push N C g).gates :=
  ⟨[g],rfl⟩

theorem pushLegal {N : Nat} {C : Circuit} (hc : Legal N C) (g : Gate)
    (hinputs : ∀ i ∈ g.inputs, i < N+N+C.size)
    (hop : g.inputs.length ≤ 2 ∧ (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))) :
    Legal N (push N C g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (C.gates ++ [g]).length at hj
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at hj
    by_cases hj' : j < C.gates.length
    · have hg : gateAt (push N C g) j = gateAt C j := by
        simp [gateAt, push, List.getD_eq_getElem?_getD, List.getElem?_append_left hj']
      rw [hg] at hi
      exact hc.1 j hj' i hi
    · have he : j = C.gates.length := by omega
      subst j
      have hg : gateAt (push N C g) C.gates.length = g := by
        simp [gateAt, push, List.getD_eq_getElem?_getD]
      exact hinputs i (hg ▸ hi)
  · rw [pushSize]
    change N+N+C.size < N+N+(C.size+1)
    omega
  · intro h hh
    change h ∈ C.gates ++ [g] at hh
    rcases List.mem_append.mp hh with h1|h2
    · exact hc.2.2 h h1
    · simpa using (List.mem_singleton.mp h2 ▸ hop : h.inputs.length ≤ 2 ∧ _)

def stepVals (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem valsPrefix (gs : List Gate) (w : List Bool) :
    ∃ u, gs.foldl stepVals w = w ++ u ∧ u.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons g gs ih =>
    obtain ⟨u,hu,hl⟩ := ih (stepVals w g)
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: u,
      by rw [List.foldl_cons,hu]; simp [stepVals],by simp [hl]⟩

theorem wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.size := by
  obtain ⟨u,hu,hl⟩ := valsPrefix C.gates w
  change (C.gates.foldl stepVals w).length = _
  rw [hu,List.length_append,hl]
  rfl

theorem rawWire (C : Circuit) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (C.wires w).getD i false = w.getD i false := by
  obtain ⟨u,hu,_⟩ := valsPrefix C.gates w
  change (C.gates.foldl stepVals w).getD i false = _
  rw [hu,List.getD_append _ _ _ _ hi]

theorem pushWires (N : Nat) (C : Circuit) (g : Gate) (w : List Bool) :
    (push N C g).wires w = stepVals (C.wires w) g := by
  change (C.gates ++ [g]).foldl stepVals w = stepVals (C.gates.foldl stepVals w) g
  simp [List.foldl_append]

theorem pushEval {N : Nat} (C : Circuit) (g : Gate) {w : List Bool} (hlen : w.length = N+N) :
    (push N C g).eval w = g.op.eval (g.inputs.map fun i => (C.wires w).getD i false) := by
  have hlen' := wireLength C w
  rw [hlen] at hlen'
  change ((push N C g).wires w).getD (N+N+C.size) false = _
  rw [pushWires,← hlen']
  simp [stepVals,List.getD_eq_getElem?_getD]

theorem oldWire {N : Nat} (C : Circuit) (g : Gate) {w : List Bool} (hlen : w.length = N+N)
    (i : Nat) (hi : i < N+N+C.size) :
    ((push N C g).wires w).getD i false = (C.wires w).getD i false := by
  have h := wireLength C w
  rw [hlen] at h
  rw [pushWires,stepVals,List.getD_append _ _ _ _ (h ▸ hi)]

theorem oneLen {N : Nat} (x y : Fin N) : (Represents.oneEach x y).length = N+N := by
  simp [Represents.oneEach]

theorem leftRaw {N : Nat} (C : Circuit) (x y i : Fin N) :
    (C.wires (Represents.oneEach x y)).getD i.val false = decide (i=x) := by
  rw [rawWire _ _ _ (by rw [oneLen]; omega)]
  have hi : i.val < (List.ofFn (fun p : Fin N => decide (p=x))).length := by simp
  unfold Represents.oneEach
  rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

theorem rightRaw {N : Nat} (C : Circuit) (x y j : Fin N) :
    (C.wires (Represents.oneEach x y)).getD (N+j.val) false = decide (j=y) := by
  rw [rawWire _ _ _ (by rw [oneLen]; omega)]
  simp [Represents.oneEach, List.getD_eq_getElem?_getD]

def invert {N : Nat} (C : Circuit) : Circuit := push N C ⟨.not,[C.output]⟩

theorem invertLegal {N : Nat} {C : Circuit} (hc : Legal N C) : Legal N (invert (N:=N) C) := by
  apply pushLegal hc
  · simpa using hc.2.1
  · simp

theorem invertTable {N : Nat} (C : Circuit) (x y : Fin N) :
    Table (invert (N:=N) C) x y = !(Table C x y) := by
  unfold Table invert
  rw [pushEval _ _ (oneLen x y)]
  rfl

def mark {N : Nat} (C : Circuit) (z : Fin N × Fin N) : Circuit :=
  let g := push N C ⟨.and,[z.1.val,N+z.2.val]⟩
  push N g ⟨.or,[C.output,g.output]⟩

theorem markLegal {N : Nat} {C : Circuit} (hc : Legal N C) (z : Fin N × Fin N) :
    Legal N (mark C z) := by
  let g : Gate := ⟨.and,[z.1.val,N+z.2.val]⟩
  have hga : Legal N (push N C g) := by
    apply pushLegal hc
    · intro i hi
      change i ∈ [z.1.val,N+z.2.val] at hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl <;> have := z.1.isLt <;> have := z.2.isLt <;> omega
    · simp [g]
  apply pushLegal hga
  · intro i hi
    change i ∈ [C.output,(push N C g).output] at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl
    · rw [pushSize]; have := hc.2.1; omega
    · exact hga.2.1
  · simp

theorem markTable {N : Nat} {C : Circuit} (hc : Legal N C) (z : Fin N × Fin N) (x y : Fin N) :
    Table (mark C z) x y = (Table C x y || decide ((x,y)=z)) := by
  let g : Gate := ⟨.and,[z.1.val,N+z.2.val]⟩
  let w := Represents.oneEach x y
  have hl : w.length = N+N := oneLen x y
  have hPair : (push N C g).eval w = (decide (z.1=x) && decide (z.2=y)) := by
    rw [pushEval _ _ hl]
    change ((C.wires w).getD z.1.val false && ((C.wires w).getD (N+z.2.val) false && true)) = _
    rw [leftRaw,rightRaw,Bool.and_true]
  change (push N (push N C g) ⟨.or,[C.output,(push N C g).output]⟩).eval w = _
  rw [pushEval _ _ hl]
  change (((push N C g).wires w).getD C.output false || ((push N C g).eval w || false)) = _
  rw [oldWire C g hl C.output hc.2.1,hPair,Bool.or_false]
  change (Table C x y || _) = (Table C x y || _)
  congr 1
  cases z with
  | mk a b => by_cases hx : a = x <;> by_cases hy : b = y <;> simp [Prod.mk.injEq,eq_comm,hx,hy]

theorem markSet {N : Nat} (C : Circuit) (hc : Legal N C) (S : Finset (Fin N × Fin N)) :
    ∃ D : Circuit, Legal N D ∧ C.gates <+: D.gates ∧ D.size = C.size + 2*S.card ∧
      ∀ x y : Fin N, Table D x y = (Table C x y || decide ((x,y) ∈ S)) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨C,hc,List.prefix_refl _,by simp,by simp⟩
  | @insert z s hzs ih =>
    obtain ⟨D,hd,hpref,hsz,ht⟩ := ih
    have hp : D.gates <+: (mark D z).gates :=
      (pushPrefix N D _).trans (pushPrefix N _ _)
    refine ⟨mark D z,markLegal hd z,hpref.trans hp,?_,?_⟩
    · unfold mark
      rw [pushSize,pushSize,hsz,Finset.card_insert_of_notMem hzs]
      omega
    · intro x y
      rw [markTable hd z x y,ht x y]
      by_cases he : (x,y)=z <;> by_cases hm : (x,y) ∈ s <;> simp [he,hm]

theorem correct {N : Nat} (base : Circuit) (hbase : Legal N base) (H : Fin N → Fin N → Bool) :
    ∃ C : Circuit, Legal N C ∧ C.gates.take base.size = base.gates ∧
      C.size ≤ base.size + 2*((Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => H z.1 z.2 ≠ Table base z.1 z.2)).card + 3 ∧ Table C = H := by
  classical
  let bad := (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 ≠ Table base z.1 z.2)
  let add := bad.filter (fun z => H z.1 z.2 = true)
  let sub := bad.filter (fun z => ¬ H z.1 z.2 = true)
  have hcard : add.card + sub.card = bad.card :=
    Finset.card_filter_add_card_filter_not (s:=bad) (fun z => H z.1 z.2 = true)
  let first := invert (N:=N) base
  obtain ⟨D,hd,hpref,hsize,ht⟩ := markSet first (invertLegal hbase) sub
  let second := invert (N:=N) D
  obtain ⟨F,hf,hpref',hsize',ht'⟩ := markSet second (invertLegal hd) add
  have hp1 : base.gates <+: first.gates := pushPrefix _ _ _
  have hp2 : D.gates <+: second.gates := pushPrefix _ _ _
  refine ⟨F,hf,(List.prefix_iff_eq_take.mp ((hp1.trans hpref).trans (hp2.trans hpref'))).symm,?_,?_⟩
  · have h1 : first.size = base.size + 1 := pushSize _ _ _
    have h2 : second.size = D.size + 1 := pushSize _ _ _
    change F.size ≤ base.size + 2*bad.card + 3
    omega
  · funext x y
    rw [ht' x y]
    rw [show Table second x y = !(Table D x y) from invertTable D x y, ht x y]
    rw [show Table first x y = !(Table base x y) from invertTable base x y]
    cases h : H x y <;> cases b : Table base x y <;> simp [add,sub,bad,h,b]

end PEqualNP.Outside.L_meta_27173

namespace PEqualNP.Outside.L_meta_27173

private theorem smallestCounts {q : ℕ} (c : Fin q → ℕ) (t : ℕ) (ht : t ≤ q) :
    ∃ (D : Finset (Fin q)) (k : ℕ), D.card = t ∧
      (∀ j ∈ D, c j ≤ k) ∧ ∀ j ∉ D, k ≤ c j := by
  classical
  induction t with
  | zero => exact ⟨∅, 0, rfl, by simp, by simp⟩
  | succ t ih =>
    obtain ⟨D, k, hd, hin, hout⟩ := ih (by omega)
    have hne : Dᶜ.Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_compl, Fintype.card_fin, hd]
      omega)
    obtain ⟨j, hj, hmin⟩ := Dᶜ.exists_min_image c hne
    have hj' : j ∉ D := Finset.mem_compl.mp hj
    refine ⟨insert j D, c j, by simp [hj', hd], ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact le_rfl
      · exact (hin i hi).trans (hout j hj')
    · intro i hi
      exact hmin i (Finset.mem_compl.mpr fun hi' => hi (Finset.mem_insert_of_mem hi'))

theorem chooseCounts {q t H M : ℕ} (_hq : 0 < q) (ht : t ≤ q)
    (c : Fin q → ℕ) (hc : ∑ j, c j ≤ H) (hM : H ≤ M) :
    ∃ D : Finset (Fin q), D.card = t ∧
      2 * (∑ j ∈ D, c j) ≤ H + ((2*t-q)*(M/q) + (M%q-2*(q-t))) := by
  classical
  obtain ⟨D, k, hd, hin, hout⟩ := smallestCounts c t ht
  refine ⟨D, hd, ?_⟩
  have hD : ∑ j ∈ D, c j ≤ t * k := by
    simpa [hd] using Finset.sum_le_sum hin
  have hrest : ∀ n ≤ k, (q-t)*n ≤ ∑ j ∈ Dᶜ, c j := by
    intro n hn
    have h := Finset.sum_le_sum (s := Dᶜ) (f := fun _ => n) (g := c)
      fun j hj => hn.trans (hout j (Finset.mem_compl.mp hj))
    simpa [Finset.card_compl, hd] using h
  have htotal := Finset.sum_add_sum_compl D c
  by_cases hk : k ≤ M/q
  · have ht' : t ≤ (q-t) + (2*t-q) := by omega
    have hm := Nat.mul_le_mul_right k ht'
    rw [Nat.add_mul] at hm
    have ha := Nat.mul_le_mul_left (2*t-q) hk
    have ho := hrest k le_rfl
    omega
  · have ho := hrest (M/q+1) (by omega)
    rw [Nat.mul_add, Nat.mul_one] at ho
    have hq' : q ≤ 2*(q-t) + (2*t-q) := by omega
    have hs := Nat.mul_le_mul_right (M/q) hq'
    rw [Nat.add_mul, Nat.mul_assoc] at hs
    have hm := Nat.mod_add_div M q
    omega

end PEqualNP.Outside.L_meta_27173

namespace PEqualNP.Outside.L_meta_27173
open Finset
theorem distributeCounts {N q m E : ℕ} (B : Grid N) (f : Match N q)
    (hf : ∀ x, Function.Injective fun j => f j x) (hEN : E ≤ N)
    (c : Fin q → ℕ) (hc : ∑ j, c j ≤ m*E) :
    ∃ H : Fin m → Grid N, (∀ s, (edits B (H s)).card ≤ E) ∧
      (∀ j, (∑ s, (edits B (H s) ∩ matching f j).card) = c j) ∧
      (∑ s, (edits B (H s)).card) = ∑ j, c j := by
  classical
  let T := (j : Fin q) × Fin (c j)
  have hslots : Fintype.card T ≤ Fintype.card (Fin m × Fin E) := by
    simpa [T, Fintype.card_sigma, Fintype.card_prod] using hc
  obtain ⟨slot⟩ := Function.Embedding.nonempty_of_card_le hslots
  let seed (a : T) := (slot a).1
  let row (a : T) : Fin N := Fin.castLE hEN (slot a).2
  let cell (a : T) : Cell N := (row a, f a.1 (row a))
  let pool (s : Fin m) : Finset T := univ.filter fun a => seed a = s
  let batch (j : Fin q) : Finset T := univ.filter fun a => a.1 = j
  let A (s : Fin m) := (pool s).image cell
  let H (s : Fin m) (x y : Fin N) := if (x,y) ∈ A s then !(B x y) else B x y
  have hedits (s : Fin m) : edits B (H s) = A s := by
    ext z
    rcases z with ⟨x,y⟩
    by_cases h : (x,y) ∈ A s <;> simp [edits, H, h]
  have hp {s : Fin m} {a : T} : a ∈ pool s ↔ seed a = s := by simp [pool]
  have hb {j : Fin q} {a : T} : a ∈ batch j ↔ a.1 = j := by simp [batch]
  have hslotinj (s : Fin m) : Set.InjOn (fun a : T => (slot a).2) (pool s) := by
    intro a ha b hb' he
    exact slot.injective (Prod.ext ((hp.mp ha).trans (hp.mp hb').symm) he)
  have hcellinj (s : Fin m) : Set.InjOn cell (pool s) := by
    intro a ha b hb' he
    apply hslotinj s ha hb'
    exact Fin.ext (congrArg (fun z : Cell N => z.1.val) he)
  have hsize (s : Fin m) : (edits B (H s)).card = (pool s).card := by
    rw [hedits]
    exact card_image_of_injOn (hcellinj s)
  have hmatch (a : T) (j : Fin q) : cell a ∈ matching f j ↔ a.1 = j := by
    change (row a, f a.1 (row a)) ∈ matching f j ↔ a.1 = j
    rw [mem_matching]
    exact ⟨fun h => (hf (row a) h).symm, fun h => by rw [h]⟩
  have hpart (s : Fin m) (j : Fin q) :
      (edits B (H s) ∩ matching f j).card = ((batch j).filter fun a => seed a = s).card := by
    have heq : A s ∩ matching f j = (((batch j).filter fun a => seed a = s).image cell) := by
      ext z
      constructor
      · intro h
        obtain ⟨a, ha, rfl⟩ := mem_image.mp (mem_inter.mp h).1
        exact mem_image.mpr ⟨a, mem_filter.mpr ⟨hb.mpr ((hmatch a j).mp (mem_inter.mp h).2), hp.mp ha⟩, rfl⟩
      · intro h
        obtain ⟨a, ha, rfl⟩ := mem_image.mp h
        obtain ⟨ha₁,ha₂⟩ := mem_filter.mp ha
        exact mem_inter.mpr ⟨mem_image.mpr ⟨a, hp.mpr ha₂, rfl⟩, (hmatch a j).mpr (hb.mp ha₁)⟩
    rw [hedits, heq]
    apply card_image_of_injOn
    exact (hcellinj s).mono fun a ha => hp.mpr (mem_filter.mp ha).2
  have hbatch (j : Fin q) : (batch j).card = c j := by
    have heq : batch j = univ.image (@Sigma.mk (Fin q) (fun i => Fin (c i)) j) := by
      ext a
      rcases a with ⟨i,k⟩
      constructor
      · intro h
        have h' : i = j := hb.mp h
        subst j
        exact mem_image.mpr ⟨k, mem_univ _, rfl⟩
      · intro h
        obtain ⟨u, _, he⟩ := mem_image.mp h
        exact hb.mpr (congrArg Sigma.fst he).symm
    rw [heq, card_image_of_injective _ sigma_mk_injective]
    simp
  refine ⟨H, ?_, ?_, ?_⟩
  · intro s
    rw [hsize]
    have h := card_le_card_of_injOn (t := (univ : Finset (Fin E)))
      (fun a : T => (slot a).2) (fun _ _ => mem_univ _) (hslotinj s)
    simpa using h
  · intro j
    simp only [hpart]
    simpa [hbatch] using sum_card_fiberwise_eq_card_filter (batch j) univ seed
  · simp only [hsize]
    simpa [pool, T, Fintype.card_sigma] using
      sum_card_fiberwise_eq_card_filter (univ : Finset T) univ seed
end PEqualNP.Outside.L_meta_27173

namespace PEqualNP.Outside.L_meta_27173
open Finset PEqualNP.CircuitLowerBounds

def Fits {N q : ℕ} (E : ℕ) (base : Circuit) (f : Match N q) (C : Circuit) : Prop :=
  Legal N C ∧ C.gates.take base.size = base.gates ∧ C.size ≤ base.size+2*E+3 ∧
    score (Table base) f (Table C) ∅ ≤ E

theorem finishData {N q E m t : ℕ} (hq : 0<q) (ht : t≤q)
    (base : Circuit) (hb : Legal N base) (f : Match N q)
    (hf : ∀ x, Function.Injective fun j => f j x)
    (hPlan : ∀ c : Fin q → ℕ, (∑ j, c j) ≤ m*E →
      ∃ H : Fin m → Grid N, (∀ s, (edits (Table base) (H s)).card ≤ E) ∧
        (∀ j, (∑ s, (edits (Table base) (H s) ∩ matching f j).card) = c j) ∧
        (∑ s, (edits (Table base) (H s)).card) = ∑ j, c j) :
    let B : Grid N := Table base
    let gain := (2*t-q)*(m*E/q) + (m*E%q-2*(q-t))
    (∀ H : Grid N, score B f H ∅ ≤ E → ∃ C, Fits E base f C ∧ Table C = H) ∧
    (∀ H : Fin m → Grid N, (∀ s, score B f (H s) ∅ ≤ E) →
      ∃ D : Finset (Fin q), D.card=t ∧ m*N*t ≤ (∑ s, score B f (H s) D)+gain) ∧
    ∃ C : Fin m → Circuit, (∀ s, Fits E base f (C s)) ∧
      (∀ D : Finset (Fin q), D.card=t → (∑ s, score B f (Table (C s)) D)+gain ≤ m*N*t) ∧
      ∃ D : Finset (Fin q), D.card=t ∧ (∑ s, score B f (Table (C s)) D)+gain = m*N*t := by
  classical
  intro B gain
  have build (H : Grid N) (he : score B f H ∅ ≤ E) :
      ∃ C, Fits E base f C ∧ Table C = H := by
    obtain ⟨C,hC,hprefix,hsize,htable⟩ := correct base hb H
    have small : (edits B H).card ≤ E := by simpa only [score_zero] using he
    change C.size ≤ base.size + 2*(edits B H).card + 3 at hsize
    refine ⟨C, ⟨hC,hprefix, by omega,?_⟩,htable⟩
    rw [htable]
    exact he
  refine ⟨build, ?_, ?_⟩
  · intro H hlim
    let c (j : Fin q) := ∑ s, (edits B (H s) ∩ matching f j).card
    let z := ∑ s, (edits B (H s)).card
    have hc : ∑ j, c j ≤ z := aggregate_bounded B f hf H
    have hM : z ≤ m*E := by
      have hsum := sum_le_sum (s := (univ : Finset (Fin m)))
        (g := fun _ => E) (fun s _ => (score_zero B f (H s)) ▸ hlim s)
      simpa [z] using hsum
    obtain ⟨D,hD,hopt⟩ := chooseCounts hq ht c hc hM
    change 2*(∑ j ∈ D, c j) ≤ z+gain at hopt
    have h := aggregate_score B f hf H D
    change (∑ s, score B f (H s) D) + 2*(∑ j ∈ D, c j) = z + m*N*D.card at h
    rw [hD] at h
    exact ⟨D,hD,by omega⟩
  · obtain ⟨c,small,hlow,D,hD,heq⟩ := balanced_plan (M:=m*E) hq ht
    obtain ⟨H,hh,hcol,hsum⟩ := hPlan c small
    choose C hfit heval using fun s => build (H s) (by simpa only [score_zero] using hh s)
    have identity (T : Finset (Fin q)) :
        (∑ s, score B f (Table (C s)) T) + 2*(∑ j ∈ T, c j) =
        (∑ j, c j) + m*N*T.card := by
      have h := aggregate_score B f hf H T
      change (∑ s, (edits B (H s)).card) = ∑ j, c j at hsum
      change ∀ j, (∑ s, (edits B (H s) ∩ matching f j).card) = c j at hcol
      simpa only [heval,hcol,hsum] using h
    refine ⟨C,hfit,?_,D,hD,?_⟩
    · intro T hT
      have h := identity T
      rw [hT] at h
      have hg := hlow T hT
      change (∑ j, c j)+gain ≤ 2*(∑ j ∈ T, c j) at hg
      omega
    · have h := identity D
      rw [hD] at h
      change (∑ j, c j)+gain = 2*(∑ j ∈ D, c j) at heq
      omega
end PEqualNP.Outside.L_meta_27173

theorem PEqualNP.Outside.L_meta_27173 : (∀ (N q E m t : ℕ), 0 < N → 0 < q → E ≤ N → 0 < m → t ≤ q →
  let X := Fin N
  let I := Fin q
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun C : Circ =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))
  let table := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  ∀ (base : Circ), legal base → ∀ f : I → Equiv.Perm X,
    (∀ x : X, Function.Injective (fun j => f j x)) →
    let loss := fun (H : X → X → Bool) (D : Finset I) =>
      ((Finset.univ : Finset (X × X)).filter (fun z => H z.1 z.2 ≠
        xor (table base z.1 z.2) (decide (z.2 ∈ D.image (fun j => f j z.1))))).card
    let fits := fun C : Circ => legal C ∧ C.gates.take base.size = base.gates ∧
      C.size ≤ base.size+2*E+3 ∧ loss (table C) ∅ ≤ E
    let gain := (2*t-q)*(m*E/q) + (m*E % q-2*(q-t))
    (∀ H : X → X → Bool, loss H ∅ ≤ E → ∃ C, fits C ∧ table C = H) ∧
    (∀ H : Fin m → X → X → Bool, (∀ s, loss (H s) ∅ ≤ E) →
      ∃ D : Finset I, D.card = t ∧ m*N*t ≤ (∑ s : Fin m, loss (H s) D)+gain) ∧
    ∃ C : Fin m → Circ, (∀ s, fits (C s)) ∧
      (∀ D : Finset I, D.card = t → (∑ s : Fin m, loss (table (C s)) D)+gain ≤ m*N*t) ∧
      ∃ D : Finset I, D.card = t ∧ (∑ s : Fin m, loss (table (C s)) D)+gain = m*N*t) := by
  intro N q E m t _ hq hEN _ ht
  dsimp only
  intro base hb f hf
  exact PEqualNP.Outside.L_meta_27173.finishData hq ht base hb f hf
    (PEqualNP.Outside.L_meta_27173.distributeCounts (PEqualNP.Outside.L_meta_27173.Table base) f hf hEN)
