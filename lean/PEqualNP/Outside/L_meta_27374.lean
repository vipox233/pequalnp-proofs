import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27374
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

end PEqualNP.Outside.L_meta_27374
namespace PEqualNP.Outside.L_meta_27374

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

end PEqualNP.Outside.L_meta_27374

namespace PEqualNP.Outside.L_meta_27374
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
end PEqualNP.Outside.L_meta_27374

namespace PEqualNP.Outside.L_meta_27374
open Finset PEqualNP.CircuitLowerBounds

def Count {N q} (B : Grid N) (f : Match N q) (H : Grid N) (j : Fin q) : ℕ :=
  (edits B H ∩ matching f j).card

def Budget {N} (B H : Grid N) := (edits B H).card

def Mixed {N q n} (w : Fin n → ℝ) (B : Grid N) (f : Match N q) (H : Fin n → Grid N)
    (D : Finset (Fin q)) : ℝ := ∑ s, w s * (score B f (H s) D : ℝ)

def Ideal (N q E t : ℕ) : ℕ := q*N*t-(2*t-q)*E

def Fits {N q : ℕ} (E : ℕ) (base : Circuit) (f : Match N q) (C : Circuit) : Prop :=
  Legal N C ∧ C.gates.take base.size = base.gates ∧ C.size ≤ base.size+2*E+3 ∧
    score (Table base) f (Table C) ∅ ≤ E

theorem fullCount {N q} (B : Grid N) (f : Match N q)
    (hf : ∀ x, Function.Injective fun j => f j x) (H : Grid N) :
    ∑ j, Count B f H j ≤ Budget B H := by
  unfold Count Budget
  rw [←counted f hf]
  exact card_le_card inter_subset_left

theorem fitTable {N q E} (base : Circuit) (hb : Legal N base) (f : Match N q)
    (H : Grid N) (he : Budget (Table base) H ≤ E) :
    ∃ C, Fits E base f C ∧ Table C = H := by
  obtain ⟨C,hC,hprefix,hsize,htable⟩ := correct base hb H
  change C.size ≤ base.size+2*Budget (Table base) H+3 at hsize
  exact ⟨C,⟨hC,hprefix,by omega,by simpa only [htable,score_zero,Budget] using he⟩,htable⟩

theorem ideal_nat {N q E t : ℕ} (hEN : E ≤ N) (htq : t < q) (hqt : q < 2*t) :
    Ideal N q E t + (2*t-q)*E = q*N*t := by
  have h₁ : (2*t-q)*E ≤ t*N := Nat.mul_le_mul (by omega) hEN
  have h₂ : t*N ≤ q*N*t := by
    have h := Nat.mul_le_mul_right (N*t) (show 1 ≤ q by omega)
    simpa only [Nat.one_mul,Nat.mul_assoc,Nat.mul_comm t N] using h
  exact Nat.sub_add_cancel (h₁.trans h₂)

theorem ideal_real {N q E t : ℕ} (hEN : E ≤ N) (htq : t < q) (hqt : q < 2*t) :
    (Ideal N q E t : ℝ) = (q:ℝ)*N*t - (2*(t:ℝ)-q)*E := by
  have h := ideal_nat hEN htq hqt
  have hr := congrArg (fun z : ℕ => (z:ℝ)) h
  push_cast [Nat.cast_sub (by omega : q≤2*t)] at hr
  linarith

theorem weighted_identity {N q t n} (B : Grid N) (f : Match N q)
    (hf : ∀ x, Function.Injective fun j => f j x) (w : Fin n → ℝ)
    (hw : ∑ s, w s = 1) (H : Fin n → Grid N) (D : Finset (Fin q)) (hD : D.card=t) :
    Mixed w B f H D + 2*(∑ j ∈ D, ∑ s, w s*(Count B f (H s) j : ℝ)) =
     (∑ s, w s*(Budget B (H s) : ℝ)) + (N:ℝ)*t := by
  have unit (s : Fin n) : (score B f (H s) D : ℝ) + 2*∑ j ∈ D, (Count B f (H s) j : ℝ) =
      (Budget B (H s):ℝ) + (N:ℝ)*t := by
    have h := score_eq B f hf (H s) D
    rw [hD] at h
    exact_mod_cast h
  have h (s : Fin n) :
      w s*(score B f (H s) D : ℝ) + 2*(∑ j ∈ D, w s*(Count B f (H s) j : ℝ)) =
      w s*(Budget B (H s):ℝ) + w s*((N:ℝ)*t) := by
    rw [←mul_sum, show 2*(w s*∑ j ∈ D, (Count B f (H s) j:ℝ)) =
        w s*(2*∑ j ∈ D, (Count B f (H s) j:ℝ)) by ring, ←mul_add,unit,mul_add]
  have hsum := sum_congr (s₁:=(univ : Finset (Fin n))) rfl (fun s _ => h s)
  simp only [sum_add_distrib, ←mul_sum,←sum_mul,hw,one_mul] at hsum
  unfold Mixed
  have swap : (∑ j ∈ D, ∑ s, w s * (Count B f (H s) j:ℝ)) =
      ∑ s, ∑ j ∈ D, w s * (Count B f (H s) j:ℝ) := sum_comm
  rw [swap]
  simpa only [←mul_sum] using hsum
end PEqualNP.Outside.L_meta_27374

namespace PEqualNP.Outside.L_meta_27374
open Finset

private theorem smallestReal {q : ℕ} (hq : 0 < q) (x : Fin q → ℝ) (t : ℕ) (ht : t ≤ q) :
    ∃ (D : Finset (Fin q)) (k : ℝ), D.card = t ∧
      (∀ j ∈ D, x j ≤ k) ∧ ∀ j ∉ D, k ≤ x j := by
  classical
  induction t with
  | zero =>
    have hn : (univ : Finset (Fin q)).Nonempty := ⟨⟨0, hq⟩, mem_univ _⟩
    obtain ⟨a, _, hmin⟩ := univ.exists_min_image x hn
    exact ⟨∅, x a, rfl, by simp, fun j _ => hmin j (mem_univ _)⟩
  | succ t ih =>
    obtain ⟨D, k, hd, hin, hout⟩ := ih (by omega)
    have hn : Dᶜ.Nonempty := card_pos.mp (by
      rw [card_compl, Fintype.card_fin, hd]
      omega)
    obtain ⟨a, ha, hmin⟩ := Dᶜ.exists_min_image x hn
    have ha' := mem_compl.mp ha
    refine ⟨insert a D, x a, by simp [ha', hd], ?_, ?_⟩
    · intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · exact le_rfl
      · exact (hin j hj).trans (hout a ha')
    · intro j hj
      exact hmin j (mem_compl.mpr fun h => hj (mem_insert_of_mem h))

private theorem minSlice {q t : ℕ} (ht : 0 < t) (htq : t < q) (x : Fin q → ℝ) :
    ∃ D : Finset (Fin q), D.card = t ∧
      (q:ℝ)*(∑ j ∈ D, x j) ≤ (t:ℝ)*(∑ j, x j) ∧
      ((q:ℝ)*(∑ j ∈ D, x j) = (t:ℝ)*(∑ j, x j) → ∀ i, (q:ℝ)*x i = ∑ j, x j) := by
  classical
  obtain ⟨D, k, hd, hin, hout⟩ := smallestReal (ht.trans htq) x t htq.le
  have hp : (0:ℝ) < t := by exact_mod_cast ht
  have hg : 0 < (q:ℝ) - t := sub_pos.mpr (by exact_mod_cast htq)
  let U : ℝ := ∑ j ∈ D, x j
  let V : ℝ := ∑ j ∈ Dᶜ, x j
  have hs : U + V = ∑ j, x j := sum_add_sum_compl D x
  have hu : U ≤ (t:ℝ)*k := by simpa [U, hd] using sum_le_sum hin
  have hcomp (j : Fin q) (hj : j ∈ Dᶜ) := hout j (mem_compl.mp hj)
  have hv : ((q:ℝ)-t)*k ≤ V := by
    simpa [V, card_compl, hd, Nat.cast_sub htq.le] using sum_le_sum hcomp
  have hu' := mul_le_mul_of_nonneg_left hu hg.le
  have hv' := mul_le_mul_of_nonneg_left hv hp.le
  have hm : (q:ℝ)*U ≤ (t:ℝ)*(∑ j, x j) := by
    rw [← hs]
    linarith only [hu', hv']
  refine ⟨D, hd, hm, ?_⟩
  intro h i
  change (q:ℝ)*U = (t:ℝ)*(∑ j, x j) at h
  rw [← hs] at h
  have hueq : U = (t:ℝ)*k := by
    apply mul_left_cancel₀ hg.ne'
    exact le_antisymm hu' (by linarith only [h, hv'])
  have hveq : ((q:ℝ)-t)*k = V := by
    apply mul_left_cancel₀ hp.ne'
    exact le_antisymm hv' (by linarith only [h, hu'])
  have hin' : ∀ j ∈ D, x j = k := (sum_eq_sum_iff_of_le hin).mp (by
    simpa [U, hd] using hueq)
  have hout' : ∀ j ∈ Dᶜ, k = x j := (sum_eq_sum_iff_of_le hcomp).mp (by
    simpa [V, card_compl, hd, Nat.cast_sub htq.le] using hveq)
  have hk (j : Fin q) : x j = k := by
    by_cases hj : j ∈ D
    · exact hin' j hj
    · exact (hout' j (mem_compl.mpr hj)).symm
  simp [hk]

theorem sliceBound {q t : ℕ} (hqt : q < 2*t) (htq : t < q)
    (x : Fin q → ℝ) (A E : ℝ) (hS : ∑ j, x j ≤ A) (hE : A ≤ E) :
    (∃ D : Finset (Fin q), D.card=t ∧
      2*(q:ℝ)*(∑ j ∈ D, x j) ≤ (q:ℝ)*A+(2*(t:ℝ)-q)*E) ∧
    ((∀ D : Finset (Fin q), D.card=t →
      (q:ℝ)*A+(2*(t:ℝ)-q)*E ≤ 2*(q:ℝ)*(∑ j ∈ D, x j)) →
      A=E ∧ (∑ j,x j)=A ∧ ∀ j, (q:ℝ)*x j=E) := by
  have ht : 0 < t := by omega
  have hp : (0:ℝ) < t := by exact_mod_cast ht
  have hdif : 0 < 2*(t:ℝ)-q := sub_pos.mpr (by exact_mod_cast hqt)
  obtain ⟨D, hd, hmean, heq⟩ := minSlice ht htq x
  have hsa := mul_le_mul_of_nonneg_left hS hp.le
  have he := mul_le_mul_of_nonneg_left hE hdif.le
  refine ⟨⟨D, hd, by linarith only [hmean, hsa, he]⟩, ?_⟩
  intro h
  have hlo := h D hd
  have hfull : A=E := by
    by_contra hne
    have hlt := mul_lt_mul_of_pos_left (lt_of_le_of_ne hE hne) hdif
    linarith only [hlo, hmean, hsa, hlt]
  subst E
  have hsum : (∑ j, x j)=A := by
    by_contra hne
    have hlt := mul_lt_mul_of_pos_left (lt_of_le_of_ne hS hne) hp
    linarith only [hlo, hmean, hlt]
  refine ⟨rfl, hsum, fun j => (heq (le_antisymm hmean ?_) j).trans hsum⟩
  rw [hsum]
  linarith only [hlo]

theorem weightedFull {n : ℕ} (w b : Fin n → ℝ) (E : ℝ)
    (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1) (hb : ∀ s, b s ≤ E)
    (hs : ∑ s, w s*b s = E) (s : Fin n) (hpos : 0 < w s) : b s = E := by
  have ht : (∑ j, w j*b j) = ∑ j, w j*E := by rw [← sum_mul, hw1, one_mul, hs]
  have h := (sum_eq_sum_iff_of_le fun j (_ : j ∈ (univ : Finset (Fin n))) =>
    mul_le_mul_of_nonneg_left (hb j) (hw j)).mp ht s (mem_univ _)
  exact mul_left_cancel₀ hpos.ne' h

end PEqualNP.Outside.L_meta_27374

namespace PEqualNP.Outside.L_meta_27374
open Finset

theorem weightedCriteria {N q E t n : ℕ} (hEN : E ≤ N) (htq : t < q) (hqt : q < 2*t)
    (B : Grid N) (f : Match N q) (hf : ∀ x, Function.Injective fun j => f j x)
    (w : Fin n → ℝ) (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1)
    (H : Fin n → Grid N) (hH : ∀ s, Budget B (H s) ≤ E) :
    (∃ D : Finset (Fin q), D.card=t ∧ (Ideal N q E t:ℝ) ≤ (q:ℝ)*Mixed w B f H D) ∧
    ((∀ D : Finset (Fin q), D.card=t → (q:ℝ)*Mixed w B f H D ≤ (Ideal N q E t:ℝ)) →
      ∀ j, (q:ℝ)*(∑ s, w s*(Count B f (H s) j:ℝ)) = E) := by
  classical
  let x (j : Fin q) := ∑ s, w s*(Count B f (H s) j:ℝ)
  let A := ∑ s, w s*(Budget B (H s) : ℝ)
  have hS : ∑ j, x j ≤ A := by
    unfold x A
    rw [sum_comm]
    apply sum_le_sum
    intro s _
    rw [←mul_sum]
    apply mul_le_mul_of_nonneg_left _ (hw s)
    exact_mod_cast fullCount B f hf (H s)
  have hE : A ≤ E := by
    calc
      A ≤ ∑ s, w s*(E:ℝ) := sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left (by exact_mod_cast hH s) (hw s)
      _ = E := by rw [←sum_mul,hw1,one_mul]
  obtain ⟨⟨D,hD,hlo⟩,hrigid⟩ := sliceBound hqt htq x A E hS hE
  have identity (T : Finset (Fin q)) (hT : T.card=t) :
      (q:ℝ)*Mixed w B f H T + 2*q*(∑ j ∈ T,x j) = q*A+(q:ℝ)*N*t := by
    have h := weighted_identity B f hf w hw1 H T hT
    change Mixed w B f H T + 2*(∑ j ∈ T, x j) = A+(N:ℝ)*t at h
    have hs := congrArg (fun z : ℝ => (q:ℝ)*z) h
    linarith
  constructor
  · refine ⟨D,hD,?_⟩
    rw [ideal_real hEN htq hqt]
    linarith [identity D hD]
  · intro hb
    have hh (T : Finset (Fin q)) (hT : T.card=t) :
        (q:ℝ)*A + (2*(t:ℝ)-q)*E ≤ 2*q*(∑ j ∈ T,x j) := by
      have h := hb T hT
      rw [ideal_real hEN htq hqt] at h
      linarith [identity T hT]
    exact (hrigid hh).2.2

theorem weightedRigidity {N q E t n : ℕ} (hEN : E ≤ N) (htq : t < q) (hqt : q < 2*t)
    (B : Grid N) (f : Match N q) (hf : ∀ x, Function.Injective fun j => f j x)
    (w : Fin n → ℝ) (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1)
    (H : Fin n → Grid N) (hH : ∀ s, Budget B (H s) ≤ E)
    (hbest : ∀ D : Finset (Fin q), D.card=t →
      (q:ℝ)*Mixed w B f H D ≤ (Ideal N q E t:ℝ)) :
    ∀ j, (q:ℝ)*(∑ s, w s*(Count B f (H s) j:ℝ)) = E :=
  (weightedCriteria hEN htq hqt B f hf w hw hw1 H hH).2 hbest

end PEqualNP.Outside.L_meta_27374

namespace PEqualNP.Outside.L_meta_27374

theorem maskMass {q : ℕ} (S : Finset (Fin q)) (k : ℕ) :
    (∑ j : Fin q, if j ∈ S then k else 0) = S.card*k := by
  classical
  rw [← Finset.sum_filter]
  simp

theorem hasPositive {q E : ℕ} (hE : 0 < E) (x : Fin q → ℕ) (hs : (∑ j, x j) = E) :
    ∃ i, 0 < x i := by
  by_contra! hn
  have hz (j : Fin q) : x j = 0 := by have := hn j; omega
  simp [hz] at hs
  omega

theorem twoCounts_iff {q E : ℕ} (hE : 0 < E) (hEq : E < q) :
    (∃ (x y : Fin q → ℕ) (p : ℝ), (∑ j, x j) = E ∧ (∑ j, y j) = E ∧
      0 ≤ p ∧ p ≤ 1 ∧ ∀ j, p*(x j : ℝ)+(1-p)*(y j : ℝ) = (E : ℝ)/q) ↔
      ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u+v=q ∧ u ∣ E ∧ v ∣ E := by
  classical
  have hqN : 0 < q := by omega
  have hq : (0:ℝ) < q := by exact_mod_cast hqN
  have hl : (0:ℝ) < E / (q:ℝ) := by positivity
  have hh : (E:ℝ) / q < 1 := (div_lt_one hq).mpr (by exact_mod_cast hEq)
  constructor
  · rintro ⟨x,y,p,sx,sy,hp0,hp1,havg⟩
    have hsep (j : Fin q) (hx : 0 < x j) (hy : 0 < y j) : False := by
      have hx' : (1:ℝ) ≤ x j := by exact_mod_cast hx
      have hy' : (1:ℝ) ≤ y j := by exact_mod_cast hy
      have hbig := add_le_add (mul_le_mul_of_nonneg_left hx' hp0)
        (mul_le_mul_of_nonneg_left hy' (sub_nonneg.mpr hp1))
      rw [havg j] at hbig
      linarith
    obtain ⟨i,hi⟩ := hasPositive hE x sx
    obtain ⟨k,hk⟩ := hasPositive hE y sy
    have yi : y i = 0 := by by_contra! hn; exact hsep i hi (by omega)
    have xk : x k = 0 := by by_contra! hn; exact hsep k (by omega) hk
    have pi : p*(x i : ℝ) = (E:ℝ)/q := by simpa [yi] using havg i
    have pk : (1-p)*(y k : ℝ) = (E:ℝ)/q := by simpa [xk] using havg k
    have p0 : p ≠ 0 := by intro h; rw [h,zero_mul] at pi; linarith
    have p1 : 1-p ≠ 0 := by intro h; rw [h,zero_mul] at pk; linarith
    let S := Finset.univ.filter (fun j : Fin q => 0 < x j)
    have hs (j : Fin q) : j ∈ S ↔ 0 < x j := by simp [S]
    have xPiece (j : Fin q) : x j = if j ∈ S then x i else 0 := by
      by_cases hm : j ∈ S
      · rw [ite_eq_left hm]
        have zy : y j = 0 := by by_contra! hn; exact hsep j ((hs _).mp hm) (by omega)
        have hxj : p*(x j : ℝ) = (E:ℝ)/q := by simpa [zy] using havg j
        exact_mod_cast (mul_left_cancel₀ p0 (hxj.trans pi.symm))
      · rw [ite_eq_right hm]; have := mt (hs _).mpr hm; omega
    have yPiece (j : Fin q) : y j = if j ∈ Sᶜ then y k else 0 := by
      by_cases hm : j ∈ S
      · simp only [Finset.mem_compl,hm,not_true_eq_false,ite_false]
        by_contra! hn; exact hsep j ((hs _).mp hm) (by omega)
      · simp only [Finset.mem_compl,hm,not_false_eq_true,ite_true]
        have zx : x j = 0 := by have := mt (hs _).mpr hm; omega
        have hyj : (1-p)*(y j : ℝ) = (E:ℝ)/q := by simpa [zx] using havg j
        exact_mod_cast (mul_left_cancel₀ p1 (hyj.trans pk.symm))
    have hspos : 0 < S.card := Finset.card_pos.mpr ⟨i,(hs _).mpr hi⟩
    have hcpos : 0 < Sᶜ.card := Finset.card_pos.mpr ⟨k, by simp [hs,xk]⟩
    refine ⟨S.card,Sᶜ.card,hspos,hcpos,by simp,?_,?_⟩
    · exact ⟨x i, sx.symm.trans ((Finset.sum_congr rfl (fun j _ => xPiece j)).trans (maskMass S (x i)))⟩
    · exact ⟨y k, sy.symm.trans ((Finset.sum_congr rfl (fun j _ => yPiece j)).trans (maskMass Sᶜ (y k)))⟩
  · rintro ⟨u,v,hu,hv,huv,⟨a,ha⟩,⟨b,hb⟩⟩
    have hus : u ≤ (Finset.univ : Finset (Fin q)).card := by simp; omega
    obtain ⟨S,_,hS⟩ := Finset.exists_subset_card_eq hus
    have hSc : Sᶜ.card = v := by
      have := S.card_add_card_compl
      simp only [Fintype.card_fin,hS] at this
      omega
    have huv' : (u:ℝ)+(v:ℝ) = q := by exact_mod_cast huv
    have ha' : (E:ℝ) = (u:ℝ)*(a:ℝ) := by exact_mod_cast ha
    have hb' : (E:ℝ) = (v:ℝ)*(b:ℝ) := by exact_mod_cast hb
    refine ⟨fun j => if j ∈ S then a else 0, fun j => if j ∈ Sᶜ then b else 0,
      (u:ℝ)/q, by rw [maskMass,hS,←ha],by rw [maskMass,hSc,←hb],by positivity,
      (div_le_one hq).mpr (by exact_mod_cast (show u ≤ q by omega)),?_⟩
    intro j
    by_cases hj : j ∈ S
    · simp [hj]; field_simp; linarith
    · simp [hj]; field_simp; nlinarith

theorem fullBudgets {q E : ℕ} (hE : 0 < E) (hEq : E < q) (x y : Fin q → ℕ) (p : ℝ)
    (sx : (∑ j, x j) ≤ E) (sy : (∑ j, y j) ≤ E) (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (hav : ∀ j, p*(x j : ℝ)+(1-p)*(y j : ℝ) = (E:ℝ)/q) :
    (∑ j, x j) = E ∧ (∑ j, y j) = E := by
  classical
  have hqN : 0 < q := by omega
  have hq : (0:ℝ) < q := by exact_mod_cast hqN
  have hl : (0:ℝ) < E/(q:ℝ) := by positivity
  have hh : (E:ℝ)/q < 1 := (div_lt_one hq).mpr (by exact_mod_cast hEq)
  have nonnat (n : ℕ) : (n : ℝ) ≠ (E : ℝ)/q := by
    intro he
    have a : (0 : ℝ) < n := hl.trans_eq he.symm
    have b : (n : ℝ) < 1 := he.trans_lt hh
    have an : 0 < n := by exact_mod_cast a
    have bn : n < 1 := by exact_mod_cast b
    omega
  let j : Fin q := ⟨0,hqN⟩
  have hleft : 0 < p := lt_of_le_of_ne h0 (by
    rintro rfl
    exact nonnat (y j) (by simpa using hav j))
  have hright : 0 < 1-p := by
    apply sub_pos.mpr
    apply lt_of_le_of_ne h1
    rintro rfl
    exact nonnat (x j) (by simpa using hav j)
  have hsum : p*((∑ j, x j : ℕ) : ℝ)+(1-p)*((∑ j, y j : ℕ) : ℝ) = E := by
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    simp_rw [hav]
    simp [nsmul_eq_mul]
    field_simp
  have xs : ((∑ j, x j : ℕ):ℝ) ≤ E := by exact_mod_cast sx
  have ys : ((∑ j, y j : ℕ):ℝ) ≤ E := by exact_mod_cast sy
  have nz := mul_nonneg (le_of_lt hleft) (sub_nonneg.mpr xs)
  have mz := mul_nonneg (le_of_lt hright) (sub_nonneg.mpr ys)
  have zx : p*((E:ℝ)-(∑ j, x j : ℕ)) = 0 := by nlinarith
  have zy : (1-p)*((E:ℝ)-(∑ j, y j : ℕ)) = 0 := by nlinarith
  have xe := sub_eq_zero.mp ((mul_eq_zero.mp zx).resolve_left hleft.ne')
  have ye := sub_eq_zero.mp ((mul_eq_zero.mp zy).resolve_left hright.ne')
  exact ⟨by exact_mod_cast xe.symm,by exact_mod_cast ye.symm⟩

theorem twoCounts_le_iff {q E : ℕ} (hE : 0 < E) (hEq : E < q) :
    (∃ (x y : Fin q → ℕ) (p : ℝ), (∑ j, x j) ≤ E ∧ (∑ j, y j) ≤ E ∧
      0 ≤ p ∧ p ≤ 1 ∧ ∀ j, p*(x j : ℝ)+(1-p)*(y j : ℝ) = (E : ℝ)/q) ↔
      ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u+v=q ∧ u ∣ E ∧ v ∣ E := by
  constructor
  · rintro ⟨x,y,p,sx,sy,h0,h1,hav⟩
    obtain ⟨xe,ye⟩ := fullBudgets hE hEq x y p sx sy h0 h1 hav
    exact (twoCounts_iff hE hEq).mp ⟨x,y,p,xe,ye,h0,h1,hav⟩
  · intro h
    obtain ⟨x,y,p,sx,sy,h0,h1,hav⟩ := (twoCounts_iff hE hEq).mpr h
    exact ⟨x,y,p,sx.le,sy.le,h0,h1,hav⟩

end PEqualNP.Outside.L_meta_27374

namespace PEqualNP.Outside.L_meta_27374
open Finset PEqualNP.CircuitLowerBounds

theorem realizeOne {N q E : ℕ} (base : Circuit) (hb : Legal N base) (f : Match N q)
    (hf : ∀ x, Function.Injective fun j => f j x) (hEN : E ≤ N)
    (c : Fin q → ℕ) (hs : ∑ j, c j = E) :
    ∃ C, Fits E base f C ∧ Budget (N:=N) (Table base) (Table C) = E ∧
      ∀ j, Count (Table base) f (Table C) j = c j := by
  obtain ⟨H,hbud,hcount,hall⟩ := distributeCounts (m:=1) (Table base) f hf hEN c
    (by simpa using hs.le)
  obtain ⟨C,hc,he⟩ := fitTable base hb f (H 0) (hbud 0)
  refine ⟨C,hc,?_,?_⟩
  · rw [he]
    simpa [Budget,Fin.sum_univ_one,hs] using hall
  · intro j
    rw [he]
    simpa [Count,Fin.sum_univ_one] using hcount j

theorem twoCriterion {N q E t : ℕ} (hE : 0 < E) (hEN : E ≤ N) (hEq : E < q)
    (htq : t < q) (hqt : q < 2*t) (base : Circuit) (hb : Legal N base)
    (f : Match N q) (hf : ∀ x, Function.Injective fun j => f j x)
    (rigid : ∀ (w : Fin 2 → ℝ), (∀ s, 0 ≤ w s) → (∑ s, w s)=1 →
      ∀ H : Fin 2 → Grid N, (∀ s, Budget (N:=N) (Table base) (H s) ≤ E) →
        (∀ D : Finset (Fin q), D.card=t →
          (q:ℝ)*Mixed w (Table base) f H D ≤ (Ideal N q E t:ℝ)) →
        ∀ j, (q:ℝ)*(∑ s, w s*(Count (Table base) f (H s) j:ℝ)) = E) :
    (∃ (A B : Circuit) (p : ℝ), Fits E base f A ∧ Fits E base f B ∧ 0 ≤ p ∧ p ≤ 1 ∧
       ∀ D : Finset (Fin q), D.card=t →
         (q:ℝ)*(p*(score (Table base) f (Table A) D : ℝ)+
           (1-p)*(score (Table base) f (Table B) D : ℝ)) ≤ (Ideal N q E t : ℝ)) ↔
      ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u+v=q ∧ u ∣ E ∧ v ∣ E := by
  classical
  have hqN : 0 < q := by omega
  have hq : (0:ℝ) < q := by exact_mod_cast hqN
  constructor
  · rintro ⟨A,B,p,ha,hbFit,hp0,hp1,hloss⟩
    let w : Fin 2 → ℝ := ![p,1-p]
    let H : Fin 2 → Grid N := ![Table A, Table B]
    have hw (s : Fin 2) : 0 ≤ w s := by
      fin_cases s
      · exact hp0
      · exact sub_nonneg.mpr hp1
    have hw1 : (∑ s, w s) = 1 := by simp [w, Fin.sum_univ_two]
    have haBud : Budget (N:=N) (Table base) (Table A) ≤ E := by
      simpa only [score_zero,Budget] using ha.2.2.2
    have hbBud : Budget (N:=N) (Table base) (Table B) ≤ E := by
      simpa only [score_zero,Budget] using hbFit.2.2.2
    have budgets (s : Fin 2) : Budget (N:=N) (Table base) (H s) ≤ E := by
      fin_cases s
      · exact haBud
      · exact hbBud
    have hbest (D : Finset (Fin q)) (hD : D.card=t) :
        (q:ℝ)*Mixed w (Table base) f H D ≤ (Ideal N q E t : ℝ) := by
      simpa [Mixed, Fin.sum_univ_two, w, H] using hloss D hD
    have hr := rigid w hw hw1 H budgets hbest
    apply (twoCounts_le_iff hE hEq).mp
    refine ⟨Count (Table base) f (Table A), Count (Table base) f (Table B), p,
      (fullCount _ f hf _).trans haBud,(fullCount _ f hf _).trans hbBud,hp0,hp1,?_⟩
    intro j
    rw [eq_div_iff hq.ne']
    rw [mul_comm]
    simpa [w,H,Fin.sum_univ_two] using hr j
  · intro hex
    obtain ⟨x,y,p,hx,hy,hp0,hp1,havg⟩ := (twoCounts_iff hE hEq).mpr hex
    obtain ⟨A,hA,bA,cA⟩ := realizeOne base hb f hf hEN x hx
    obtain ⟨B,hB,bB,cB⟩ := realizeOne base hb f hf hEN y hy
    let w : Fin 2 → ℝ := ![p,1-p]
    let H : Fin 2 → Grid N := ![Table A,Table B]
    have hw : (∑ s, w s) = 1 := by simp [w,Fin.sum_univ_two]
    have hsum (j : Fin q) :
        (∑ s, w s*(Count (Table base) f (H s) j:ℝ)) = (E:ℝ)/q := by
      simpa [w,H,Fin.sum_univ_two,cA,cB] using havg j
    have hbud : (∑ s, w s*(Budget (N:=N) (Table base) (H s) : ℝ)) = E := by
      simp [w,H,Fin.sum_univ_two,bA,bB]
      ring
    refine ⟨A,B,p,hA,hB,hp0,hp1,?_⟩
    intro D hD
    have hid := weighted_identity (Table base) f hf w hw H D hD
    rw [hbud] at hid
    simp_rw [hsum] at hid
    rw [Finset.sum_const,hD,nsmul_eq_mul] at hid
    field_simp [hq.ne'] at hid
    rw [ideal_real hEN htq hqt]
    have hmix : Mixed w (Table base) f H D =
        p*(score (Table base) f (Table A) D : ℝ)+(1-p)*(score (Table base) f (Table B) D : ℝ) := by
      simp [Mixed,w,H,Fin.sum_univ_two]
    rw [←hmix]
    nlinarith only [hid]

end PEqualNP.Outside.L_meta_27374

namespace PEqualNP.Outside.L_meta_27374
open Finset PEqualNP.CircuitLowerBounds

theorem uniformCriterion {N q E t m : ℕ} (hEN : E ≤ N) (htq : t < q)
    (hqt : q < 2*t) (hm : 0 < m) (base : Circuit) (hb : Legal N base)
    (f : Match N q) (hf : ∀ x, Function.Injective fun j => f j x) :
    (∃ C : Fin m → Circuit, (∀ s, Fits E base f (C s)) ∧
      ∀ D : Finset (Fin q), D.card=t →
        q*(∑ s, score (Table base) f (Table (C s)) D) ≤ m*Ideal N q E t) ↔ q ∣ m*E := by
  classical
  constructor
  · rintro ⟨C, hC, hbest⟩
    let H (s : Fin m) : Grid N := Table (C s)
    let w (_ : Fin m) : ℝ := (m:ℝ)⁻¹
    have hmp : (0:ℝ) < m := by exact_mod_cast hm
    have hw (s : Fin m) : 0 ≤ w s := inv_nonneg.mpr hmp.le
    have h1 : ∑ s, w s = 1 := by simp [w, hmp.ne']
    have hBud (s : Fin m) : Budget (Table base) (H s) ≤ E := by
      simpa only [H, Budget, score_zero] using (hC s).2.2.2
    have hmix (D : Finset (Fin q)) (hD : D.card=t) :
        (q:ℝ)*Mixed w (Table base) f H D ≤ (Ideal N q E t : ℝ) := by
      have hn := hbest D hD
      have hr : (q:ℝ)*(∑ s, (score (Table base) f (H s) D:ℝ)) ≤
          (m:ℝ)*(Ideal N q E t : ℝ) := by exact_mod_cast hn
      unfold Mixed
      simp only [w, ←mul_sum]
      rw [show (q:ℝ)*((m:ℝ)⁻¹*(∑ s, (score (Table base) f (H s) D:ℝ))) =
        ((q:ℝ)*(∑ s, (score (Table base) f (H s) D:ℝ)))/m by ring]
      exact (div_le_iff₀ hmp).mpr (by linarith only [hr])
    let j : Fin q := ⟨0, by omega⟩
    have h := weightedRigidity hEN htq hqt (Table base) f hf w hw h1 H hBud hmix j
    simp only [w, ←mul_sum] at h
    have hqsum : (q:ℝ)*(∑ s, (Count (Table base) f (H s) j:ℝ)) = (m:ℝ)*E := by
      calc
        _ = (m:ℝ)*((q:ℝ)*((m:ℝ)⁻¹*(∑ s, (Count (Table base) f (H s) j:ℝ)))) := by
          field_simp
        _ = _ := by rw [h]
    exact ⟨∑ s, Count (Table base) f (H s) j, by exact_mod_cast hqsum.symm⟩
  · rintro ⟨k, hk⟩
    obtain ⟨H, hbudget, hcount, htotal⟩ := distributeCounts (m:=m) (Table base) f hf hEN
      (fun _ => k) (by simp [hk])
    choose C hC htable using fun s => fitTable base hb f (H s) (hbudget s)
    refine ⟨C, hC, ?_⟩
    intro D hD
    simp only [htable]
    have hs := aggregate_score (Table base) f hf H D
    simp only [hcount, htotal, hD, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_id] at hs
    rw [←hk] at hs
    have hi := ideal_nat hEN htq hqt
    have ha := congrArg (fun a : ℕ => q*a) hs
    have hb' := congrArg (fun a : ℕ => m*a) hi
    have hc := congrArg (fun a : ℕ => (2*t)*a) hk
    have hd : (2*t-q)*(m*E) + q*(m*E) = (2*t)*(m*E) := by
      rw [←Nat.add_mul, Nat.sub_add_cancel hqt.le]
    nlinarith only [ha, hb', hc, hd]

end PEqualNP.Outside.L_meta_27374

theorem PEqualNP.Outside.L_meta_27374 : (∀ (N q E t : ℕ), 0 < N → 0 < E → E ≤ N → E < q → q < 2*t → t < q →
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
    let ideal := q*N*t-(2*t-q)*E
    (∀ (n : ℕ) (w : Fin n → ℝ) (H : Fin n → X → X → Bool),
      (∀ s, 0 ≤ w s) → (∑ s, w s) = 1 → (∀ s, loss (H s) ∅ ≤ E) →
      ∃ D : Finset I, D.card = t ∧ (ideal : ℝ) ≤
        (q : ℝ) * ∑ s : Fin n, w s * (loss (H s) D : ℝ)) ∧
    ((∃ (A B : Circ) (p : ℝ), fits A ∧ fits B ∧ 0 ≤ p ∧ p ≤ 1 ∧
      ∀ D : Finset I, D.card = t →
        (q : ℝ)*(p*(loss (table A) D : ℝ)+(1-p)*(loss (table B) D : ℝ)) ≤ (ideal : ℝ)) ↔
      ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u+v = q ∧ u ∣ E ∧ v ∣ E) ∧
    ∀ m : ℕ, 0 < m →
      ((∃ C : Fin m → Circ, (∀ s, fits (C s)) ∧
        ∀ D : Finset I, D.card = t →
          q*(∑ s : Fin m, loss (table (C s)) D) ≤ m*ideal) ↔ q ∣ m*E)) := by
  intro N q E t _ hE hEN hEq hqt htq
  dsimp only
  intro base hb f hf
  refine ⟨?_,?_,?_⟩
  · intro n w H hw hw1 hH
    apply (PEqualNP.Outside.L_meta_27374.weightedCriteria hEN htq hqt (PEqualNP.Outside.L_meta_27374.Table base) f hf w hw hw1 H ?_).1
    intro s
    have h := hH s
    change PEqualNP.Outside.L_meta_27374.score (PEqualNP.Outside.L_meta_27374.Table base) f (H s) ∅ ≤ E at h
    simpa only [PEqualNP.Outside.L_meta_27374.score_zero, PEqualNP.Outside.L_meta_27374.Budget] using h
  · exact PEqualNP.Outside.L_meta_27374.twoCriterion hE hEN hEq htq hqt base hb f hf
      (PEqualNP.Outside.L_meta_27374.weightedRigidity hEN htq hqt (PEqualNP.Outside.L_meta_27374.Table base) f hf)
  · intro m hm
    exact PEqualNP.Outside.L_meta_27374.uniformCriterion hEN htq hqt hm base hb f hf
