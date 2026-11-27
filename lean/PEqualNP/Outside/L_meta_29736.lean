import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29736
namespace Circ

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

private def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

private def depths (width : ℕ) (C : Circuit) : List ℕ :=
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> revert h <;> decide

private theorem zmod2_add_self (t : ZMod 2) : t + t = 0 := by
  revert t
  decide

private theorem zmod2_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t
  decide

private theorem b2z_decide_eq_one (t : ZMod 2) : b2z (decide (t = 1)) = t := by
  revert t
  decide

private theorem gate_eval_one_affine (op : GateOp) :
    ∃ c0 c1 : ZMod 2, ∀ x : Bool, b2z (op.eval [x]) = c0 + c1 * b2z x := by
  refine ⟨b2z (op.eval [false]), b2z (op.eval [true]) + b2z (op.eval [false]), fun x => ?_⟩
  cases x
  · simp [b2z]
  · simp only [b2z, ↓reduceIte, mul_one]
    generalize op.eval [false] = a
    generalize op.eval [true] = b
    cases a <;> cases b <;> decide

private theorem gate_eval_two_poly (op : GateOp) :
    ∃ c0 c1 c2 : ZMod 2, ∀ x y : Bool,
      b2z (op.eval [x, y]) = c0 + c1 * b2z x + c2 * b2z y +
        b2z (xor (xor (op.eval [false, false]) (op.eval [false, true]))
                 (xor (op.eval [true, false]) (op.eval [true, true]))) * (b2z x * b2z y) := by
  refine ⟨b2z (op.eval [false, false]),
    b2z (op.eval [true, false]) + b2z (op.eval [false, false]),
    b2z (op.eval [false, true]) + b2z (op.eval [false, false]), fun x y => ?_⟩
  cases x <;> cases y <;>
  · generalize op.eval [false, false] = a
    generalize op.eval [false, true] = b
    generalize op.eval [true, false] = c
    generalize op.eval [true, true] = d
    cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem foldr_max_le_iff (l : List ℕ) (k : ℕ) :
    l.foldr max 0 ≤ k ↔ ∀ a ∈ l, a ≤ k := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, max_le_iff, List.mem_cons, forall_eq_or_imp, ih]

private theorem mem_le_foldr_max {l : List ℕ} {a : ℕ} (ha : a ∈ l) :
    a ≤ l.foldr max 0 :=
  (foldr_max_le_iff l (l.foldr max 0)).1 (le_refl _) a ha

private def runFold {α : Type} (step : List α → Gate → α) (init : List α) (gs : List Gate) : List α :=
  gs.foldl (fun l g => l ++ [step l g]) init

private theorem runFold_length {α : Type} (step : List α → Gate → α) (init : List α) (gs : List Gate) :
    (runFold step init gs).length = init.length + gs.length := by
  unfold runFold
  induction gs generalizing init with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private theorem runFold_append {α : Type} (step : List α → Gate → α) (init : List α)
    (gs1 gs2 : List Gate) :
    runFold step init (gs1 ++ gs2) = runFold step (runFold step init gs1) gs2 := by
  unfold runFold
  exact List.foldl_append

private theorem getD_append_left {α : Type} (l1 l2 : List α) (i : ℕ) (d0 : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d0 = l1.getD i d0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_of_ge {α : Type} (l : List α) (i : ℕ) (d0 : α) (hi : l.length ≤ i) :
    l.getD i d0 = d0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

private theorem runFold_getD_prefix {α : Type} (step : List α → Gate → α) (init : List α)
    (gs : List Gate) (w : ℕ) (d0 : α) (hw : w < init.length) :
    (runFold step init gs).getD w d0 = init.getD w d0 := by
  unfold runFold
  induction gs generalizing init with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hw' : w < (init ++ [step init g]).length := by
      rw [List.length_append, List.length_singleton]; omega
    rw [ih (init ++ [step init g]) hw', getD_append_left _ _ _ _ hw]

private theorem runFold_getD_gate {α : Type} (step : List α → Gate → α) (init : List α)
    (gs : List Gate) (idx : ℕ) (hidx : idx < gs.length) (d0 : α) :
    (runFold step init gs).getD (init.length + idx) d0 =
      step (runFold step init (gs.take idx)) (gs[idx]) := by
  have hsplit : gs = gs.take idx ++ [gs[idx]] ++ gs.drop (idx + 1) := by
    conv_lhs => rw [← List.take_append_drop idx gs]
    rw [List.append_assoc, List.singleton_append]
    congr 1
    exact (List.cons_getElem_drop_succ (h := hidx)).symm
  conv_lhs => rw [hsplit]
  rw [runFold_append, runFold_append]
  have hlen_take : (runFold step init (gs.take idx)).length = init.length + idx := by
    rw [runFold_length, List.length_take, min_eq_left (le_of_lt hidx)]
  have hlen1 : init.length + idx < (runFold step (runFold step init (gs.take idx)) [gs[idx]]).length := by
    rw [runFold_length, hlen_take, List.length_singleton]; omega
  rw [runFold_getD_prefix step _ (gs.drop (idx + 1)) (init.length + idx) d0 hlen1]
  unfold runFold
  simp only [List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD]
  have heq : init.length + idx = (gs.take idx |>.foldl (fun l g => l ++ [step l g]) init).length :=
    hlen_take.symm
  rw [List.getElem?_append_right (le_of_eq heq.symm), Nat.sub_eq_zero_of_le (le_of_eq heq)]
  rfl

private theorem wires_eq_runFold (C : Circuit) (x : List Bool) :
    C.wires x = runFold (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) x C.gates :=
  rfl

private theorem depths_eq_runFold (width : ℕ) (C : Circuit) :
    depths width C = runFold (fun ds g =>
      (g.inputs.map fun a => ds.getD a 0).foldr max 0 + (nonlinear g).toNat)
      (List.replicate width 0) C.gates :=
  rfl

private theorem oneEach_length {n m : ℕ} (a : Fin n) (b : Fin m) :
    (oneEach a b).length = n + m := by
  simp [oneEach]

private theorem oneEach_getD_left {n m : ℕ} (a : Fin n) (b : Fin m) (w : ℕ) (hw : w < n) :
    (oneEach a b).getD w false = decide ((⟨w, hw⟩ : Fin n) = a) := by
  unfold oneEach
  rw [getD_append_left _ _ _ _ (by simp [hw])]
  simp [List.getD_eq_getElem?_getD, hw]

private theorem oneEach_getD_right {n m : ℕ} (a : Fin n) (b : Fin m) (w : ℕ)
    (hlo : n ≤ w) (hhi : w < n + m) :
    (oneEach a b).getD w false = decide ((⟨w - n, by omega⟩ : Fin m) = b) := by
  unfold oneEach
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [hlo])]
  simp only [List.length_ofFn]
  have hlt : w - n < m := by omega
  simp [hlt]

private theorem gateAt_eq_getElem (C : Circuit) (idx : ℕ) (hidx : idx < C.gates.length) :
    gateAt C idx = C.gates[idx] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hidx]

private theorem wires_getD_gate {n m : ℕ} (C : Circuit) (hRB : ReadsBack (n + m) C)
    (a : Fin n) (b : Fin m) (idx : ℕ) (hidx : idx < C.gates.length) :
    (C.wires (oneEach a b)).getD (n + m + idx) false =
      C.gates[idx].op.eval (C.gates[idx].inputs.map fun i => (C.wires (oneEach a b)).getD i false) := by
  rw [wires_eq_runFold]
  have hlen : (oneEach a b).length = n + m := oneEach_length a b
  have h1 := runFold_getD_gate (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    (oneEach a b) C.gates idx hidx false
  rw [hlen] at h1
  rw [h1]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hlt : i < n + m + idx := by
    have hrb := hRB idx hidx i
    rw [gateAt_eq_getElem C idx hidx] at hrb
    exact hrb hi
  have htake : C.gates = C.gates.take idx ++ C.gates.drop idx := (List.take_append_drop idx C.gates).symm
  conv_rhs => rw [htake, runFold_append]
  have hlt2 : i < (runFold (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
      (oneEach a b) (C.gates.take idx)).length := by
    rw [runFold_length, hlen, List.length_take, min_eq_left (le_of_lt hidx)]
    exact hlt
  exact (runFold_getD_prefix _ _ (C.gates.drop idx) i false hlt2).symm

private theorem depths_getD_gate {n m : ℕ} (C : Circuit) (hRB : ReadsBack (n + m) C)
    (idx : ℕ) (hidx : idx < C.gates.length) :
    (depths (n + m) C).getD (n + m + idx) 0 =
      (C.gates[idx].inputs.map fun i => (depths (n + m) C).getD i 0).foldr max 0 +
        (nonlinear C.gates[idx]).toNat := by
  rw [depths_eq_runFold]
  have hlen : (List.replicate (n + m) 0).length = n + m := List.length_replicate
  have h1 := runFold_getD_gate (fun ds g =>
      (g.inputs.map fun a => ds.getD a 0).foldr max 0 + (nonlinear g).toNat)
    (List.replicate (n + m) 0) C.gates idx hidx 0
  rw [hlen] at h1
  rw [h1]
  congr 2
  refine List.map_congr_left fun i hi => ?_
  have hlt : i < n + m + idx := by
    have hrb := hRB idx hidx i
    rw [gateAt_eq_getElem C idx hidx] at hrb
    exact hrb hi
  have htake : C.gates = C.gates.take idx ++ C.gates.drop idx := (List.take_append_drop idx C.gates).symm
  conv_rhs => rw [htake, runFold_append]
  have hlt2 : i < (runFold (fun ds g =>
      (g.inputs.map fun a => ds.getD a 0).foldr max 0 + (nonlinear g).toNat)
      (List.replicate (n + m) 0) (C.gates.take idx)).length := by
    rw [runFold_length, hlen, List.length_take, min_eq_left (le_of_lt hidx)]
    exact hlt
  exact (runFold_getD_prefix _ _ (C.gates.drop idx) i 0 hlt2).symm

private theorem depths_getD_input (width : ℕ) (C : Circuit) (w : ℕ) (hw : w < width) :
    (depths width C).getD w 0 = 0 := by
  rw [depths_eq_runFold, runFold_getD_prefix _ _ _ w 0 (by simp [hw])]
  simp [List.getD_eq_getElem?_getD, hw]

private theorem depths_getD_oob (width : ℕ) (C : Circuit) (w : ℕ) (hw : width + C.gates.length ≤ w) :
    (depths width C).getD w 0 = 0 := by
  rw [depths_eq_runFold, getD_of_ge _ w 0]
  rw [runFold_length, List.length_replicate]
  exact hw

private theorem matrix_rank_zero {n m : ℕ} :
    (0 : Matrix (Fin n) (Fin m) (ZMod 2)).rank = 0 := by
  simp [Matrix.rank]

private theorem matrix_rank_add_le {n m : ℕ} (A B : Matrix (Fin n) (Fin m) (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro y ⟨x, rfl⟩
    have hsum : (A + B).mulVecLin x = A.mulVecLin x + B.mulVecLin x := by simp
    rw [hsum]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  have hmono : Module.finrank (ZMod 2) (LinearMap.range (A + B).mulVecLin) ≤
      Module.finrank (ZMod 2) ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
    Submodule.finrank_mono hle
  omega

private theorem matrix_rank_sum_le {ι : Type} [DecidableEq ι] {n m : ℕ}
    (S : Finset ι) (f : ι → Matrix (Fin n) (Fin m) (ZMod 2)) :
    (∑ i ∈ S, f i).rank ≤ ∑ i ∈ S, (f i).rank := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (matrix_rank_add_le _ _) (Nat.add_le_add_left ih _)

private theorem matrix_rank_decomp {n m : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod 2)) :
    ∃ (a : Fin B.rank → Fin n → ZMod 2) (b : Fin B.rank → Fin m → ZMod 2),
      B = ∑ k : Fin B.rank, Matrix.vecMulVec (a k) (b k) := by
  let bas := Module.finBasis (ZMod 2) (LinearMap.range B.mulVecLin)
  let a : Fin B.rank → Fin n → ZMod 2 := fun k => (bas k).1
  let b : Fin B.rank → Fin m → ZMod 2 := fun k j =>
    bas.repr ⟨B.mulVecLin (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩ k
  refine ⟨a, b, ?_⟩
  ext i j
  have hcol : B.mulVecLin (Pi.single j 1) = ∑ k : Fin B.rank, (b k j) • (a k) := by
    have h1 := bas.sum_repr ⟨B.mulVecLin (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩
    have h2 := congrArg Subtype.val h1
    rw [Submodule.coe_sum] at h2
    exact h2.symm
  have hi := congrFun hcol i
  have hlhs : B.mulVecLin (Pi.single j 1) i = B i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hlhs] at hi
  rw [hi, Matrix.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.vecMulVec_apply, mul_comm]

private def anchor {n m : ℕ} (u : Fin n) (v : Fin m)
    (M : Matrix (Fin n) (Fin m) (ZMod 2)) : Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun a b => M a b + M a v + M u b + M u v

private theorem anchor_zero {n m : ℕ} (u : Fin n) (v : Fin m) :
    anchor u v (0 : Matrix (Fin n) (Fin m) (ZMod 2)) = 0 := by
  ext a b; simp [anchor]

private theorem anchor_add {n m : ℕ} (u : Fin n) (v : Fin m)
    (A B : Matrix (Fin n) (Fin m) (ZMod 2)) :
    anchor u v (A + B) = anchor u v A + anchor u v B := by
  ext a b; simp only [anchor, Matrix.add_apply]; ring

private theorem anchor_smul {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2)
    (A : Matrix (Fin n) (Fin m) (ZMod 2)) :
    anchor u v (c • A) = c • anchor u v A := by
  ext a b; simp only [anchor, Matrix.smul_apply, smul_eq_mul]; ring

private def IsSep {n m : ℕ} (M : Matrix (Fin n) (Fin m) (ZMod 2)) : Prop :=
  ∃ (α : Fin n → ZMod 2) (β : Fin m → ZMod 2), ∀ a b, M a b = α a + β b

private theorem anchor_of_isSep {n m : ℕ} (u : Fin n) (v : Fin m)
    {M : Matrix (Fin n) (Fin m) (ZMod 2)} (hM : IsSep M) :
    anchor u v M = 0 := by
  obtain ⟨α, β, h⟩ := hM
  ext a b
  simp only [anchor, h, Matrix.zero_apply]
  calc α a + β b + (α a + β v) + (α u + β b) + (α u + β v)
      = (α a + α a) + (α u + α u) + (β b + β b) + (β v + β v) := by ring
    _ = 0 := by simp [zmod2_add_self]

private theorem isSep_const {n m : ℕ} (c : ZMod 2) :
    IsSep (Matrix.of (fun (_ : Fin n) (_ : Fin m) => c)) :=
  ⟨fun _ => c, fun _ => 0, fun _ _ => by simp⟩

private theorem isSep_add {n m : ℕ} {A B : Matrix (Fin n) (Fin m) (ZMod 2)}
    (hA : IsSep A) (hB : IsSep B) : IsSep (A + B) := by
  obtain ⟨α1, β1, h1⟩ := hA
  obtain ⟨α2, β2, h2⟩ := hB
  refine ⟨fun a => α1 a + α2 a, fun b => β1 b + β2 b, fun a b => ?_⟩
  simp only [Matrix.add_apply, h1, h2]
  ring

private theorem isSep_smul {n m : ℕ} (c : ZMod 2) {A : Matrix (Fin n) (Fin m) (ZMod 2)}
    (hA : IsSep A) : IsSep (c • A) := by
  obtain ⟨α, β, h⟩ := hA
  refine ⟨fun a => c * α a, fun b => c * β b, fun a b => ?_⟩
  simp only [Matrix.smul_apply, smul_eq_mul, h]
  ring

private theorem anchor_vecMulVec_rank_le_one {n m : ℕ} (u : Fin n) (v : Fin m)
    (α : Fin n → ZMod 2) (β : Fin m → ZMod 2) :
    (anchor u v (Matrix.vecMulVec α β)).rank ≤ 1 := by
  have heq : anchor u v (Matrix.vecMulVec α β) =
      Matrix.vecMulVec (fun a => α a + α u) (fun b => β b + β v) := by
    ext a b
    simp only [anchor, Matrix.vecMulVec_apply]
    ring
  rw [heq]
  exact Matrix.rank_vecMulVec_le _ _

private theorem countP_eq_card_filter {α : Type} (p : α → Bool) (l : List α) :
    l.countP p = ((Finset.univ : Finset (Fin l.length)).filter (fun idx => p l[idx.val] = true)).card := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.countP_cons, ih, Finset.card_filter, Finset.card_filter]
    have hs : ∑ idx : Fin (xs.length + 1), (if p (x :: xs)[idx.val] = true then 1 else 0) =
        (if p x = true then 1 else 0) + ∑ idx : Fin xs.length, (if p xs[idx.val] = true then 1 else 0) :=
      Fin.sum_univ_succ (fun idx : Fin (xs.length + 1) => if p (x :: xs)[idx.val] = true then 1 else 0)
    change (∑ idx : Fin xs.length, if p xs[idx.val] = true then 1 else 0) +
        (if p x = true then 1 else 0) =
      ∑ idx : Fin (xs.length + 1), if p (x :: xs)[idx.val] = true then 1 else 0
    rw [hs, Nat.add_comm]

private theorem forward_aux {n m q : ℕ} (G : Fin q → Fin n → Fin m → Bool)
    (u : Fin n) (v : Fin m) (t : ℕ)
    (C : Circuit) (tap : Fin q → ℕ)
    (hRB : ReadsBack (n + m) C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcnt : C.gates.countP nonlinear ≤ t)
    (htap : ∀ j : Fin q, (depths (n + m) C).getD (tap j) 0 ≤ 1 ∧ Represents (G j) ⟨C.gates, tap j⟩) :
    let F := ZMod 2
    let Mask := Fin q → F
    let Mat := Matrix (Fin n) (Fin m) F
    let entry := fun j a b => if G j a b then (1 : F) else 0
    let anchored : Fin q → Mat := fun j a b =>
      entry j a b + entry j a v + entry j u b + entry j u v
    ∃ blocks : Mask → Mat,
      (∀ j : Fin q, anchored j = ∑ h : Mask, (h j) • blocks h) ∧
      (∑ h : Mask, ((blocks h).rank + 1) / 2) ≤ t := by
  intro F Mask Mat entry anchored
  let N := C.gates.length
  let val : ℕ → Mat := fun w a b => b2z ((C.wires (oneEach a b)).getD w false)
  let dep : ℕ → ℕ := fun w => (depths (n + m) C).getD w 0
  have hval_in_left : ∀ w < n, IsSep (val w) := by
    intro w hw
    refine ⟨fun a => b2z (decide ((⟨w, hw⟩ : Fin n) = a)), fun _ => 0, fun a b => ?_⟩
    simp only [val, wires_eq_runFold]
    rw [runFold_getD_prefix _ _ _ w false (by rw [oneEach_length]; omega),
      oneEach_getD_left a b w hw, add_zero]
  have hval_in_right : ∀ w, n ≤ w → w < n + m → IsSep (val w) := by
    intro w hlo hhi
    refine ⟨fun _ => 0, fun b => b2z (decide ((⟨w - n, by omega⟩ : Fin m) = b)), fun a b => ?_⟩
    simp only [val, wires_eq_runFold]
    rw [runFold_getD_prefix _ _ _ w false (by rw [oneEach_length]; omega),
      oneEach_getD_right a b w hlo hhi, zero_add]
  have hval_oob : ∀ w, n + m + N ≤ w → val w = 0 := by
    intro w hw
    ext a b
    simp only [val, wires_eq_runFold]
    rw [getD_of_ge _ w false (by rw [runFold_length, oneEach_length]; exact hw)]
    rfl
  have hdep0_sep : ∀ w : ℕ, dep w = 0 → IsSep (val w) := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hdep0
      by_cases hlt1 : w < n
      · exact hval_in_left w hlt1
      · by_cases hlt2 : w < n + m
        · exact hval_in_right w (by omega) hlt2
        · by_cases hlt3 : w < n + m + N
          · let idx := w - (n + m)
            have hidx : idx < C.gates.length := by omega
            have hw_eq : w = n + m + idx := by omega
            set g := C.gates[idx]
            have hdep_g : dep w = (g.inputs.map dep).foldr max 0 + (nonlinear g).toNat := by
              rw [hw_eq]
              exact depths_getD_gate C hRB idx hidx
            rw [hdep0] at hdep_g
            have hnl0 : (nonlinear g).toNat = 0 := by omega
            have hnl_false : nonlinear g = false := by
              cases h : nonlinear g
              · rfl
              · simp [h] at hnl0
            have hmax0 : (g.inputs.map dep).foldr max 0 = 0 := by omega
            have hin_dep0 : ∀ i ∈ g.inputs, dep i = 0 := by
              intro i hi
              have hle : dep i ≤ 0 := by
                rw [← hmax0]
                exact mem_le_foldr_max (List.mem_map_of_mem hi)
              exact Nat.eq_zero_of_le_zero hle
            have hin_lt : ∀ i ∈ g.inputs, i < w := by
              intro i hi
              have hrb := hRB idx hidx i
              rw [gateAt_eq_getElem C idx hidx] at hrb
              have := hrb hi
              omega
            have hglen : g.inputs.length ≤ 2 := hfan g (List.getElem_mem hidx)
            have hval_g : ∀ a b, val w a b =
                b2z (g.op.eval (g.inputs.map fun i => (C.wires (oneEach a b)).getD i false)) := by
              intro a b
              simp only [val]
              rw [hw_eq, wires_getD_gate C hRB a b idx hidx]
            rcases hlist : g.inputs with _ | ⟨i1, _ | ⟨i2, rest⟩⟩
            · refine ⟨fun _ => b2z (g.op.eval []), fun _ => 0, fun a b => ?_⟩
              rw [hval_g a b, hlist]; simp
            · obtain ⟨c0, c1, haff⟩ := gate_eval_one_affine g.op
              have hi1_sep : IsSep (val i1) :=
                ih i1 (hin_lt i1 (by simp [hlist])) (hin_dep0 i1 (by simp [hlist]))
              have hcomb : val w = Matrix.of (fun (_ : Fin n) (_ : Fin m) => c0) + c1 • val i1 := by
                ext a b
                rw [hval_g a b, hlist]
                exact haff ((C.wires (oneEach a b)).getD i1 false)
              rw [hcomb]
              exact isSep_add (isSep_const c0) (isSep_smul c1 hi1_sep)
            · have hrest : rest = [] := by
                rw [hlist] at hglen
                cases rest with
                | nil => rfl
                | cons _ _ => simp at hglen
              subst hrest
              obtain ⟨c0, c1, c2, hpoly⟩ := gate_eval_two_poly g.op
              have hxor_false : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                  (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
                unfold nonlinear at hnl_false
                rw [hlist] at hnl_false
                simpa using hnl_false
              have hi1_sep : IsSep (val i1) :=
                ih i1 (hin_lt i1 (by simp [hlist])) (hin_dep0 i1 (by simp [hlist]))
              have hi2_sep : IsSep (val i2) :=
                ih i2 (hin_lt i2 (by simp [hlist])) (hin_dep0 i2 (by simp [hlist]))
              have hcomb : val w = Matrix.of (fun (_ : Fin n) (_ : Fin m) => c0) + c1 • val i1 + c2 • val i2 := by
                ext a b
                rw [hval_g a b, hlist]
                have hp := hpoly ((C.wires (oneEach a b)).getD i1 false)
                  ((C.wires (oneEach a b)).getD i2 false)
                rw [hxor_false] at hp
                simp only [b2z, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero] at hp
                exact hp
              rw [hcomb]
              exact isSep_add (isSep_add (isSep_const c0) (isSep_smul c1 hi1_sep)) (isSep_smul c2 hi2_sep)
          · rw [hval_oob w (by omega)]
            exact isSep_const 0
  let NL1 : Finset (Fin N) :=
    Finset.univ.filter (fun idx => nonlinear C.gates[idx.val] = true ∧ dep (n + m + idx.val) = 1)
  have hNL1_le : NL1.card ≤ t := by
    have hsub : NL1 ⊆ Finset.univ.filter (fun idx : Fin N => nonlinear C.gates[idx.val] = true) := by
      intro idx hidx
      simp only [NL1, Finset.mem_filter, Finset.mem_univ, true_and] at hidx ⊢
      exact hidx.1
    calc NL1.card
        ≤ (Finset.univ.filter (fun idx : Fin N => nonlinear C.gates[idx.val] = true)).card :=
          Finset.card_le_card hsub
      _ = C.gates.countP nonlinear := (countP_eq_card_filter nonlinear C.gates).symm
      _ ≤ t := hcnt
  let Mgate : Fin N → Mat := fun idx => anchor u v (val (n + m + idx.val))
  have hMgate_rank : ∀ idx ∈ NL1, (Mgate idx).rank ≤ 2 := by
    intro idx hidx
    simp only [NL1, Finset.mem_filter, Finset.mem_univ, true_and] at hidx
    obtain ⟨hnl, hdep1⟩ := hidx
    set g := C.gates[idx.val]
    have hlen2 : g.inputs.length = 2 := by
      unfold nonlinear at hnl
      simp only [Bool.and_eq_true, beq_iff_eq] at hnl
      exact hnl.1
    have hxor_true : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
      unfold nonlinear at hnl
      simp only [Bool.and_eq_true, beq_iff_eq] at hnl
      exact hnl.2
    rcases hlist : g.inputs with _ | ⟨i1, _ | ⟨i2, _ | ⟨_, _⟩⟩⟩
    · simp [hlist] at hlen2
    · simp [hlist] at hlen2
    · have hdep_g : dep (n + m + idx.val) = (g.inputs.map dep).foldr max 0 + (nonlinear g).toNat :=
        depths_getD_gate C hRB idx.val idx.isLt
      rw [hdep1, hnl, hlist] at hdep_g
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_true] at hdep_g
      have hdi1 : dep i1 = 0 := by omega
      have hdi2 : dep i2 = 0 := by omega
      obtain ⟨α1, β1, h1⟩ := hdep0_sep i1 hdi1
      obtain ⟨α2, β2, h2⟩ := hdep0_sep i2 hdi2
      obtain ⟨c0, c1, c2, hpoly⟩ := gate_eval_two_poly g.op
      have hdecomp : Mgate idx =
          anchor u v (Matrix.vecMulVec α1 β2) + anchor u v (Matrix.vecMulVec α2 β1) := by
        have hsep_part : IsSep (Matrix.of fun (a : Fin n) (b : Fin m) =>
            c0 + c1 * (α1 a + β1 b) + c2 * (α2 a + β2 b) + (α1 a * α2 a + β1 b * β2 b)) := by
          refine ⟨fun a => c0 + c1 * α1 a + c2 * α2 a + α1 a * α2 a,
            fun b => c1 * β1 b + c2 * β2 b + β1 b * β2 b, fun a b => ?_⟩
          simp only [Matrix.of_apply]
          ring
        have hval_eq : val (n + m + idx.val) =
            (Matrix.vecMulVec α1 β2 + Matrix.vecMulVec α2 β1) +
            (Matrix.of fun (a : Fin n) (b : Fin m) =>
              c0 + c1 * (α1 a + β1 b) + c2 * (α2 a + β2 b) + (α1 a * α2 a + β1 b * β2 b)) := by
          ext a b
          have hw := wires_getD_gate C hRB a b idx.val idx.isLt
          have hp := hpoly ((C.wires (oneEach a b)).getD i1 false)
            ((C.wires (oneEach a b)).getD i2 false)
          rw [hxor_true] at hp
          have hv1 : b2z ((C.wires (oneEach a b)).getD i1 false) = α1 a + β1 b := h1 a b
          have hv2 : b2z ((C.wires (oneEach a b)).getD i2 false) = α2 a + β2 b := h2 a b
          change b2z ((C.wires (oneEach a b)).getD (n + m + idx.val) false) = _
          rw [hw, show C.gates[idx.val] = g from rfl, hlist]
          simp only [List.map_cons, List.map_nil]
          rw [hp, hv1, hv2]
          simp only [b2z, ↓reduceIte, one_mul, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.of_apply]
          ring
        change anchor u v (val (n + m + idx.val)) = _
        rw [hval_eq, anchor_add, anchor_add, anchor_of_isSep u v hsep_part, add_zero]
      rw [hdecomp]
      calc (anchor u v (Matrix.vecMulVec α1 β2) + anchor u v (Matrix.vecMulVec α2 β1)).rank
          ≤ (anchor u v (Matrix.vecMulVec α1 β2)).rank + (anchor u v (Matrix.vecMulVec α2 β1)).rank :=
            matrix_rank_add_le _ _
        _ ≤ 1 + 1 := Nat.add_le_add (anchor_vecMulVec_rank_le_one u v α1 β2)
            (anchor_vecMulVec_rank_le_one u v α2 β1)
        _ = 2 := rfl
    · simp [hlist] at hlen2
  have hdep1_span : ∀ w : ℕ, dep w ≤ 1 →
      ∃ coeff : Fin N → F, anchor u v (val w) = ∑ idx ∈ NL1, coeff idx • Mgate idx := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hdw
      by_cases h0 : dep w = 0
      · refine ⟨0, ?_⟩
        rw [anchor_of_isSep u v (hdep0_sep w h0)]
        simp
      · have hdw1 : dep w = 1 := by omega
        have hge : n + m ≤ w := by
          by_contra hlt
          have := depths_getD_input (n + m) C w (by omega)
          exact h0 this
        have hlt : w < n + m + N := by
          by_contra hge2
          have := depths_getD_oob (n + m) C w (by omega)
          exact h0 this
        let idx : Fin N := ⟨w - (n + m), by omega⟩
        have hw_eq : w = n + m + idx.val := by simp [idx]; omega
        set g := C.gates[idx.val]
        by_cases hnl : nonlinear g = true
        · have hmem : idx ∈ NL1 := by
            simp only [NL1, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hnl, by rw [← hw_eq]; exact hdw1⟩
          refine ⟨fun k => if k = idx then 1 else 0, ?_⟩
          rw [Finset.sum_eq_single idx]
          · simp [Mgate, hw_eq]
          · intro k _ hne; simp [hne]
          · intro hnot; exact False.elim (hnot hmem)
        · have hnl_false : nonlinear g = false := Bool.eq_false_iff.2 hnl
          have hdep_g : dep w = (g.inputs.map dep).foldr max 0 + (nonlinear g).toNat := by
            rw [hw_eq]; exact depths_getD_gate C hRB idx.val idx.isLt
          have hin_le1 : ∀ i ∈ g.inputs, dep i ≤ 1 := by
            intro i hi
            have hle := mem_le_foldr_max (List.mem_map_of_mem (f := dep) hi)
            omega
          have hin_lt : ∀ i ∈ g.inputs, i < w := by
            intro i hi
            have hrb := hRB idx.val idx.isLt i
            rw [gateAt_eq_getElem C idx.val idx.isLt] at hrb
            have := hrb hi
            omega
          have hglen : g.inputs.length ≤ 2 := hfan g (List.getElem_mem idx.isLt)
          have hval_g : ∀ a b, val w a b =
              b2z (g.op.eval (g.inputs.map fun i => (C.wires (oneEach a b)).getD i false)) := by
            intro a b
            simp only [val]
            rw [hw_eq, wires_getD_gate C hRB a b idx.val idx.isLt]
          rcases hlist : g.inputs with _ | ⟨i1, _ | ⟨i2, rest⟩⟩
          · refine ⟨0, ?_⟩
            have hsep : IsSep (val w) := ⟨fun _ => b2z (g.op.eval []), fun _ => 0, fun a b => by
              rw [hval_g a b, hlist]; simp⟩
            rw [anchor_of_isSep u v hsep]; simp
          · obtain ⟨c0, c1, haff⟩ := gate_eval_one_affine g.op
            obtain ⟨cf1, hcf1⟩ := ih i1 (hin_lt i1 (by simp [hlist])) (hin_le1 i1 (by simp [hlist]))
            refine ⟨fun k => c1 * cf1 k, ?_⟩
            have hcomb : val w = Matrix.of (fun (_ : Fin n) (_ : Fin m) => c0) + c1 • val i1 := by
              ext a b; rw [hval_g a b, hlist]
              exact haff ((C.wires (oneEach a b)).getD i1 false)
            rw [hcomb, anchor_add, anchor_of_isSep u v (isSep_const c0), zero_add,
              anchor_smul, hcf1, Finset.smul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [smul_smul]
          · have hrest : rest = [] := by
              rw [hlist] at hglen
              cases rest with
              | nil => rfl
              | cons _ _ => simp at hglen
            subst hrest
            obtain ⟨c0, c1, c2, hpoly⟩ := gate_eval_two_poly g.op
            have hxor_false : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              unfold nonlinear at hnl_false
              rw [hlist] at hnl_false
              simpa using hnl_false
            obtain ⟨cf1, hcf1⟩ := ih i1 (hin_lt i1 (by simp [hlist])) (hin_le1 i1 (by simp [hlist]))
            obtain ⟨cf2, hcf2⟩ := ih i2 (hin_lt i2 (by simp [hlist])) (hin_le1 i2 (by simp [hlist]))
            refine ⟨fun k => c1 * cf1 k + c2 * cf2 k, ?_⟩
            have hcomb : val w = Matrix.of (fun (_ : Fin n) (_ : Fin m) => c0) + c1 • val i1 + c2 • val i2 := by
              ext a b; rw [hval_g a b, hlist]
              have hp := hpoly ((C.wires (oneEach a b)).getD i1 false)
                ((C.wires (oneEach a b)).getD i2 false)
              rw [hxor_false] at hp
              simp only [b2z, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero] at hp
              exact hp
            rw [hcomb, anchor_add, anchor_add, anchor_of_isSep u v (isSep_const c0), zero_add,
              anchor_smul, anchor_smul, hcf1, hcf2, Finset.smul_sum, Finset.smul_sum,
              ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [add_smul, smul_smul, smul_smul]
  have hrep_j : ∀ j : Fin q, ∃ coeff : Fin N → F,
      anchored j = ∑ idx ∈ NL1, coeff idx • Mgate idx := by
    intro j
    obtain ⟨hdep_j, hrepr_j⟩ := htap j
    obtain ⟨coeff, hcoeff⟩ := hdep1_span (tap j) hdep_j
    refine ⟨coeff, ?_⟩
    have hval_j : val (tap j) = entry j := by
      ext a b
      have hr := hrepr_j a b
      change (C.wires (oneEach a b)).getD (tap j) false = G j a b at hr
      simp only [val, entry, b2z, hr]
    change anchor u v (entry j) = _
    rw [← hval_j]
    exact hcoeff
  choose coeff hcoeff using hrep_j
  let maskOf : Fin N → Mask := fun idx j => coeff j idx
  let blocks : Mask → Mat := fun h => ∑ idx ∈ NL1.filter (fun idx => maskOf idx = h), Mgate idx
  refine ⟨blocks, ?_, ?_⟩
  · intro j
    rw [hcoeff j]
    have hpart : ∀ idx ∈ NL1, coeff j idx • Mgate idx = (maskOf idx j) • Mgate idx := fun _ _ => rfl
    calc ∑ idx ∈ NL1, coeff j idx • Mgate idx
        = ∑ h : Mask, ∑ idx ∈ NL1.filter (fun idx => maskOf idx = h), coeff j idx • Mgate idx := by
          rw [Finset.sum_fiberwise_of_maps_to (fun idx _ => Finset.mem_univ (maskOf idx))]
      _ = ∑ h : Mask, (h j) • blocks h := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun idx hidx => ?_
          have hm : maskOf idx = h := (Finset.mem_filter.1 hidx).2
          rw [← hm]
  · have hstep : ∀ h : Mask, ((blocks h).rank + 1) / 2 ≤
        (NL1.filter (fun idx => maskOf idx = h)).card := by
      intro h
      let Sh := NL1.filter (fun idx => maskOf idx = h)
      have hrank_le : (blocks h).rank ≤ 2 * Sh.card := by
        calc (blocks h).rank
            ≤ ∑ idx ∈ Sh, (Mgate idx).rank := matrix_rank_sum_le Sh Mgate
          _ ≤ ∑ _idx ∈ Sh, 2 := Finset.sum_le_sum fun idx hidx =>
              hMgate_rank idx (Finset.mem_filter.1 hidx).1
          _ = 2 * Sh.card := by simp [Nat.mul_comm]
      change ((blocks h).rank + 1) / 2 ≤ Sh.card
      omega
    calc ∑ h : Mask, ((blocks h).rank + 1) / 2
        ≤ ∑ h : Mask, (NL1.filter (fun idx => maskOf idx = h)).card :=
          Finset.sum_le_sum fun h _ => hstep h
      _ = NL1.card := by
          rw [← Finset.card_eq_sum_card_fiberwise (f := maskOf) (t := Finset.univ)
            (fun idx _ => Finset.mem_univ (maskOf idx))]
      _ ≤ t := hNL1_le

private def GoodCirc (n m : ℕ) (gs : List Gate) : Prop :=
  ReadsBack (n + m) ⟨gs, 0⟩ ∧ ∀ g ∈ gs, g.inputs.length ≤ 2

private def valOf {n m : ℕ} (gs : List Gate) (w : ℕ) (a : Fin n) (b : Fin m) : ZMod 2 :=
  b2z (((Circuit.mk gs 0).wires (oneEach a b)).getD w false)

private def depOf (n m : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  (depths (n + m) ⟨gs, 0⟩).getD w 0

private theorem valOf_append_prefix {n m : ℕ} (gs1 gs2 : List Gate) (w : ℕ)
    (hw : w < n + m + gs1.length) (a : Fin n) (b : Fin m) :
    valOf (gs1 ++ gs2) w a b = valOf gs1 w a b := by
  simp only [valOf, wires_eq_runFold]
  rw [runFold_append]
  have hlen : w < (runFold (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
      (oneEach a b) gs1).length := by
    rw [runFold_length, oneEach_length]; exact hw
  rw [runFold_getD_prefix _ _ gs2 w false hlen]

private theorem depOf_append_prefix (n m : ℕ) (gs1 gs2 : List Gate) (w : ℕ)
    (hw : w < n + m + gs1.length) :
    depOf n m (gs1 ++ gs2) w = depOf n m gs1 w := by
  simp only [depOf, depths_eq_runFold]
  rw [runFold_append]
  have hlen : w < (runFold (fun ds g =>
      (g.inputs.map fun a => ds.getD a 0).foldr max 0 + (nonlinear g).toNat)
      (List.replicate (n + m) 0) gs1).length := by
    rw [runFold_length, List.length_replicate]; exact hw
  rw [runFold_getD_prefix _ _ gs2 w 0 hlen]

private theorem goodCirc_append_gate {n m : ℕ} (gs : List Gate) (hgs : GoodCirc n m gs)
    (g : Gate) (hlen : g.inputs.length ≤ 2) (hin : ∀ i ∈ g.inputs, i < n + m + gs.length) :
    GoodCirc n m (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    rw [gateAt_eq_getElem ⟨gs ++ [g], 0⟩ j hj] at hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [List.getElem_append_left hlt] at hi
      have hrb := hgs.1 j hlt i
      rw [gateAt_eq_getElem ⟨gs, 0⟩ j hlt] at hrb
      exact hrb hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [List.getElem_append_right (le_refl _)] at hi
      simp only [Nat.sub_self, List.getElem_cons_zero] at hi
      exact hin i hi
  · intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h2
    · exact hgs.2 g' h1
    · simp only [List.mem_singleton] at h2
      rw [h2]; exact hlen

private theorem append_gate_eval {n m : ℕ} (gs : List Gate) (hgs : GoodCirc n m gs)
    (g : Gate) (hlen : g.inputs.length ≤ 2) (hin : ∀ i ∈ g.inputs, i < n + m + gs.length) :
    let gs' := gs ++ [g]
    let w := n + m + gs.length
    GoodCirc n m gs' ∧
    w < n + m + gs'.length ∧
    gs'.countP nonlinear = gs.countP nonlinear + (nonlinear g).toNat ∧
    depOf n m gs' w = (g.inputs.map (depOf n m gs)).foldr max 0 + (nonlinear g).toNat ∧
    ∀ (a : Fin n) (b : Fin m),
      valOf gs' w a b = b2z (g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires (oneEach a b)).getD i false)) := by
  intro gs' w
  have hgood' : GoodCirc n m gs' := goodCirc_append_gate gs hgs g hlen hin
  have hidx : gs.length < gs'.length := by simp [gs']
  have hget : gs'[gs.length] = g := by simp [gs']
  refine ⟨hgood', by simp [w, gs'], ?_, ?_, ?_⟩
  · simp only [gs', List.countP_append, List.countP_cons, List.countP_nil]
    cases nonlinear g <;> simp
  · have hd := depths_getD_gate ⟨gs', 0⟩ hgood'.1 gs.length hidx
    change (depths (n + m) ⟨gs', 0⟩).getD (n + m + gs.length) 0 = _
    rw [hd, hget]
    congr 2
    refine List.map_congr_left fun i hi => ?_
    exact depOf_append_prefix n m gs [g] i (hin i hi)
  · intro a b
    have hw := wires_getD_gate ⟨gs', 0⟩ hgood'.1 a b gs.length hidx
    change b2z (((Circuit.mk gs' 0).wires (oneEach a b)).getD w false) = _
    rw [hw, hget]
    congr 2
    refine List.map_congr_left fun i hi => ?_
    have hpre := valOf_append_prefix gs [g] i (hin i hi) a b
    exact b2z_inj hpre

private theorem buildConst0 {n m : ℕ} (gs : List Gate) (hgs : GoodCirc n m gs) :
    ∃ (extra : List Gate) (w : ℕ),
      let gs' := gs ++ extra
      GoodCirc n m gs' ∧ w < n + m + gs'.length ∧
      gs'.countP nonlinear = gs.countP nonlinear ∧
      depOf n m gs' w = 0 ∧
      ∀ (a : Fin n) (b : Fin m), valOf gs' w a b = 0 := by
  let g : Gate := ⟨GateOp.or, []⟩
  have hnl : nonlinear g = false := by decide
  obtain ⟨hgood', hwlt, hcnt, hdep, hval⟩ := append_gate_eval gs hgs g (by decide) (by simp [g])
  refine ⟨[g], n + m + gs.length, hgood', hwlt, ?_, ?_, ?_⟩
  · rw [hcnt, hnl]; simp
  · rw [hdep, hnl]; simp [g]
  · intro a b; rw [hval a b]; rfl

private theorem buildXor {n m : ℕ} (gs : List Gate) (hgs : GoodCirc n m gs)
    (x y : ℕ) (hx : x < n + m + gs.length) (hy : y < n + m + gs.length) :
    ∃ (extra : List Gate) (w : ℕ),
      let gs' := gs ++ extra
      GoodCirc n m gs' ∧ w < n + m + gs'.length ∧
      gs'.countP nonlinear = gs.countP nonlinear ∧
      depOf n m gs' w = max (depOf n m gs x) (depOf n m gs y) ∧
      ∀ (a : Fin n) (b : Fin m), valOf gs' w a b = valOf gs x a b + valOf gs y a b := by
  let g1 : Gate := ⟨GateOp.mod 2, [x, y]⟩
  have hnl1 : nonlinear g1 = false := rfl
  obtain ⟨hgood1, hw1lt, hcnt1, hdep1, hval1⟩ := append_gate_eval gs hgs g1 (by simp [g1]) (by
    intro i hi; simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption)
  set gs1 := gs ++ [g1]
  set w1 := n + m + gs.length
  let g2 : Gate := ⟨GateOp.not, [w1]⟩
  have hnl2 : nonlinear g2 = false := rfl
  obtain ⟨hgood2, hw2lt, hcnt2, hdep2, hval2⟩ := append_gate_eval gs1 hgood1 g2 (by simp [g2]) (by
    intro i hi; simp only [g2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [hi]; exact hw1lt)
  refine ⟨[g1, g2], n + m + gs1.length, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [gs1, List.append_assoc] using hgood2
  · simp [gs1]
  · have hEq : gs ++ [g1, g2] = gs1 ++ [g2] := by simp [gs1, List.append_assoc]
    rw [hEq, hcnt2, hcnt1, hnl1, hnl2]; simp
  · have hEq : gs ++ [g1, g2] = gs1 ++ [g2] := by simp [gs1, List.append_assoc]
    rw [hEq, hdep2, hnl2]
    simp only [g2, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false,
      Nat.max_zero, add_zero]
    rw [hdep1, hnl1]
    simp [g1]
  · intro a b
    have hEq : gs ++ [g1, g2] = gs1 ++ [g2] := by simp [gs1, List.append_assoc]
    rw [hEq, hval2 a b]
    have hv1 := hval1 a b
    have hbit1 : ((Circuit.mk gs1 0).wires (oneEach a b)).getD w1 false =
        g1.op.eval [((Circuit.mk gs 0).wires (oneEach a b)).getD x false,
                    ((Circuit.mk gs 0).wires (oneEach a b)).getD y false] :=
      b2z_inj hv1
    simp only [g1, g2, List.map_cons, List.map_nil, hbit1, valOf]
    generalize ((Circuit.mk gs 0).wires (oneEach a b)).getD x false = bx
    generalize ((Circuit.mk gs 0).wires (oneEach a b)).getD y false = by_
    cases bx <;> cases by_ <;> decide

private theorem buildAnd {n m : ℕ} (gs : List Gate) (hgs : GoodCirc n m gs)
    (x y : ℕ) (hx : x < n + m + gs.length) (hy : y < n + m + gs.length) :
    ∃ (extra : List Gate) (w : ℕ),
      let gs' := gs ++ extra
      GoodCirc n m gs' ∧ w < n + m + gs'.length ∧
      gs'.countP nonlinear = gs.countP nonlinear + 1 ∧
      depOf n m gs' w = max (depOf n m gs x) (depOf n m gs y) + 1 ∧
      ∀ (a : Fin n) (b : Fin m), valOf gs' w a b = valOf gs x a b * valOf gs y a b := by
  let g : Gate := ⟨GateOp.and, [x, y]⟩
  have hnl : nonlinear g = true := rfl
  obtain ⟨hgood', hwlt, hcnt, hdep, hval⟩ := append_gate_eval gs hgs g (by simp [g]) (by
    intro i hi; simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption)
  refine ⟨[g], n + m + gs.length, hgood', hwlt, ?_, ?_, ?_⟩
  · rw [hcnt, hnl]; simp
  · rw [hdep, hnl]; simp [g]
  · intro a b
    rw [hval a b]
    simp only [g, List.map_cons, List.map_nil, valOf]
    generalize ((Circuit.mk gs 0).wires (oneEach a b)).getD x false = bx
    generalize ((Circuit.mk gs 0).wires (oneEach a b)).getD y false = by_
    cases bx <;> cases by_ <;> decide

private theorem buildXorList {n m : ℕ} (ws : List ℕ) (dmax : ℕ) :
    ∀ (gs : List Gate), GoodCirc n m gs →
      (∀ i ∈ ws, i < n + m + gs.length ∧ depOf n m gs i ≤ dmax) →
      ∃ (extra : List Gate) (w : ℕ),
        let gs' := gs ++ extra
        GoodCirc n m gs' ∧ w < n + m + gs'.length ∧
        gs'.countP nonlinear = gs.countP nonlinear ∧
        depOf n m gs' w ≤ dmax ∧
        ∀ (a : Fin n) (b : Fin m), valOf gs' w a b = (ws.map (fun i => valOf gs i a b)).sum := by
  induction ws with
  | nil =>
    intro gs hgs _
    obtain ⟨extra, w, hgood', hwlt, hcnt, hdep, hval⟩ := buildConst0 gs hgs
    exact ⟨extra, w, hgood', hwlt, hcnt, by omega, fun a b => by simpa using hval a b⟩
  | cons x rest ih =>
    intro gs hgs hws
    obtain ⟨hx_lt, hx_dep⟩ := hws x (by simp)
    obtain ⟨extra1, w1, hgood1, hw1lt, hcnt1, hdep1, hval1⟩ :=
      ih gs hgs (fun i hi => hws i (by simp [hi]))
    set gs1 := gs ++ extra1
    have hx_lt1 : x < n + m + gs1.length := by
      simp only [gs1, List.length_append]; omega
    obtain ⟨extra2, w2, hgood2, hw2lt, hcnt2, hdep2, hval2⟩ :=
      buildXor gs1 hgood1 x w1 hx_lt1 hw1lt
    refine ⟨extra1 ++ extra2, w2, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [gs1, List.append_assoc] using hgood2
    · simpa [gs1, List.append_assoc] using hw2lt
    · rw [← List.append_assoc, hcnt2, hcnt1]
    · rw [← List.append_assoc, hdep2, depOf_append_prefix n m gs extra1 x hx_lt]
      exact max_le hx_dep hdep1
    · intro a b
      rw [← List.append_assoc, hval2 a b, valOf_append_prefix gs extra1 x hx_lt a b, hval1 a b]
      rfl

private theorem buildSep {n m : ℕ} (gs : List Gate) (hgs : GoodCirc n m gs)
    (α : Fin n → ZMod 2) (β : Fin m → ZMod 2) :
    ∃ (extra : List Gate) (w : ℕ),
      let gs' := gs ++ extra
      GoodCirc n m gs' ∧ w < n + m + gs'.length ∧
      gs'.countP nonlinear = gs.countP nonlinear ∧
      depOf n m gs' w = 0 ∧
      ∀ (a : Fin n) (b : Fin m), valOf gs' w a b = α a + β b := by
  let wsL : List ℕ := ((List.finRange n).filter (fun i => decide (α i = 1))).map Fin.val
  let wsR : List ℕ := ((List.finRange m).filter (fun j => decide (β j = 1))).map (fun j => n + j.val)
  let ws : List ℕ := wsL ++ wsR
  have hws : ∀ i ∈ ws, i < n + m + gs.length ∧ depOf n m gs i ≤ 0 := by
    intro i hi
    rcases List.mem_append.1 hi with hL | hR
    · obtain ⟨k, _, rfl⟩ := List.mem_map.1 hL
      exact ⟨by omega, by rw [depOf, depths_getD_input (n + m) ⟨gs, 0⟩ k.val (by omega)]⟩
    · obtain ⟨k, _, rfl⟩ := List.mem_map.1 hR
      exact ⟨by omega, by rw [depOf, depths_getD_input (n + m) ⟨gs, 0⟩ (n + k.val) (by omega)]⟩
  obtain ⟨extra, w, hgood', hwlt, hcnt, hdep, hval⟩ := buildXorList ws 0 gs hgs hws
  refine ⟨extra, w, hgood', hwlt, hcnt, Nat.eq_zero_of_le_zero hdep, fun a b => ?_⟩
  rw [hval a b]
  simp only [ws, List.map_append, List.sum_append]
  have hLsum : (wsL.map (fun i => valOf gs i a b)).sum = α a := by
    have hmap : wsL.map (fun i => valOf gs i a b) =
        ((List.finRange n).filter (fun i => decide (α i = 1))).map
          (fun i => b2z (decide (i = a))) := by
      simp only [wsL, List.map_map]
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, valOf, wires_eq_runFold]
      rw [runFold_getD_prefix _ _ _ i.val false (by rw [oneEach_length]; omega),
        oneEach_getD_left a b i.val i.isLt]
    rw [hmap]
    have hnodup : ((List.finRange n).filter (fun i => decide (α i = 1))).Nodup :=
      (List.nodup_finRange n).filter _
    have hsum_fin : (((List.finRange n).filter (fun i => decide (α i = 1))).map
        (fun i => b2z (decide (i = a)))).sum =
        ∑ i ∈ ((List.finRange n).filter (fun i => decide (α i = 1))).toFinset,
          b2z (decide (i = a)) := by
      rw [← List.sum_toFinset _ hnodup]
    rw [hsum_fin]
    by_cases ha : α a = 1
    · have hmem : a ∈ ((List.finRange n).filter (fun i => decide (α i = 1))).toFinset := by
        simp [ha]
      rw [Finset.sum_eq_single a]
      · simp [b2z, ha]
      · intro i _ hne; simp [b2z, hne]
      · intro hnot; exact False.elim (hnot hmem)
    · have ha0 : α a = 0 := by rcases zmod2_cases (α a) with h | h; exact h; exact False.elim (ha h)
      have hnot : a ∉ ((List.finRange n).filter (fun i => decide (α i = 1))).toFinset := by
        simp [ha]
      rw [Finset.sum_eq_zero]
      · exact ha0.symm
      · intro i hi
        have hne : i ≠ a := fun heq => hnot (heq ▸ hi)
        simp [b2z, hne]
  have hRsum : (wsR.map (fun i => valOf gs i a b)).sum = β b := by
    have hmap : wsR.map (fun i => valOf gs i a b) =
        ((List.finRange m).filter (fun j => decide (β j = 1))).map
          (fun j => b2z (decide (j = b))) := by
      simp only [wsR, List.map_map]
      refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp_apply, valOf, wires_eq_runFold]
      rw [runFold_getD_prefix _ _ _ (n + j.val) false (by rw [oneEach_length]; omega),
        oneEach_getD_right a b (n + j.val) (by omega) (by omega)]
      have hfin : (⟨n + j.val - n, by omega⟩ : Fin m) = j := Fin.ext (Nat.add_sub_cancel_left n j.val)
      rw [hfin]
    rw [hmap]
    have hnodup : ((List.finRange m).filter (fun j => decide (β j = 1))).Nodup :=
      (List.nodup_finRange m).filter _
    have hsum_fin : (((List.finRange m).filter (fun j => decide (β j = 1))).map
        (fun j => b2z (decide (j = b)))).sum =
        ∑ j ∈ ((List.finRange m).filter (fun j => decide (β j = 1))).toFinset,
          b2z (decide (j = b)) := by
      rw [← List.sum_toFinset _ hnodup]
    rw [hsum_fin]
    by_cases hb : β b = 1
    · have hmem : b ∈ ((List.finRange m).filter (fun j => decide (β j = 1))).toFinset := by
        simp [hb]
      rw [Finset.sum_eq_single b]
      · simp [b2z, hb]
      · intro j _ hne; simp [b2z, hne]
      · intro hnot; exact False.elim (hnot hmem)
    · have hb0 : β b = 0 := by rcases zmod2_cases (β b) with h | h; exact h; exact False.elim (hb h)
      have hnot : b ∉ ((List.finRange m).filter (fun j => decide (β j = 1))).toFinset := by
        simp [hb]
      rw [Finset.sum_eq_zero]
      · exact hb0.symm
      · intro j hj
        have hne : j ≠ b := fun heq => hnot (heq ▸ hj)
        simp [b2z, hne]
  rw [hLsum, hRsum]

private structure PairItem (n m q : ℕ) where
  mask : Fin q → ZMod 2
  a1 : Fin n → ZMod 2
  b1 : Fin m → ZMod 2
  a2 : Fin n → ZMod 2
  b2 : Fin m → ZMod 2

private theorem buildPairs {n m q : ℕ} (ps : List (PairItem n m q)) :
    ∀ (gs : List Gate), GoodCirc n m gs →
      ∃ (extra : List Gate) (ws : List (PairItem n m q × ℕ)),
        let gs' := gs ++ extra
        GoodCirc n m gs' ∧
        gs'.countP nonlinear = gs.countP nonlinear + ps.length ∧
        ws.map Prod.fst = ps ∧
        ∀ pw ∈ ws, pw.2 < n + m + gs'.length ∧ depOf n m gs' pw.2 = 1 ∧
          ∀ (a : Fin n) (b : Fin m),
            valOf gs' pw.2 a b = (pw.1.a1 a + pw.1.b2 b) * (pw.1.a2 a + pw.1.b1 b) := by
  induction ps with
  | nil =>
    intro gs hgs
    exact ⟨[], [], by simpa using hgs, by simp, rfl, fun _ h => by simp at h⟩
  | cons p rest ih =>
    intro gs hgs
    obtain ⟨ex1, w1, hgood1, hw1lt, hcnt1, hdep1, hval1⟩ := buildSep gs hgs p.a1 p.b2
    set gs1 := gs ++ ex1
    obtain ⟨ex2, w2, hgood2, hw2lt, hcnt2, hdep2, hval2⟩ := buildSep gs1 hgood1 p.a2 p.b1
    set gs2 := gs1 ++ ex2
    have hw1lt2 : w1 < n + m + gs2.length := by simp only [gs2, List.length_append]; omega
    obtain ⟨ex3, w3, hgood3, hw3lt, hcnt3, hdep3, hval3⟩ := buildAnd gs2 hgood2 w1 w2 hw1lt2 hw2lt
    set gs3 := gs2 ++ ex3
    obtain ⟨ex4, ws4, hgood4, hcnt4, hmap4, hprop4⟩ := ih gs3 hgood3
    refine ⟨ex1 ++ ex2 ++ ex3 ++ ex4, (p, w3) :: ws4, ?_, ?_, ?_, ?_⟩
    · simpa [gs3, gs2, gs1, List.append_assoc] using hgood4
    · have hEq : gs ++ (ex1 ++ ex2 ++ ex3 ++ ex4) = gs3 ++ ex4 := by
        simp [gs3, gs2, gs1, List.append_assoc]
      rw [hEq, hcnt4, hcnt3, hcnt2, hcnt1]
      simp only [List.length_cons]
      omega
    · simp [hmap4]
    · intro pw hpw
      have hEq : gs ++ (ex1 ++ ex2 ++ ex3 ++ ex4) = gs3 ++ ex4 := by
        simp [gs3, gs2, gs1, List.append_assoc]
      rw [hEq]
      rcases List.mem_cons.1 hpw with rfl | hrest
      · refine ⟨by simp only [List.length_append]; omega, ?_, ?_⟩
        · rw [depOf_append_prefix n m gs3 ex4 w3 hw3lt, hdep3,
            depOf_append_prefix n m gs1 ex2 w1 hw1lt, hdep1, hdep2]
          rfl
        · intro a b
          rw [valOf_append_prefix gs3 ex4 w3 hw3lt a b, hval3 a b,
            valOf_append_prefix gs1 ex2 w1 hw1lt a b, hval1 a b, hval2 a b]
      · exact hprop4 pw hrest

private theorem buildOutputs {n m q : ℕ}
    (ws : List (PairItem n m q × ℕ)) (α : Fin q → Fin n → ZMod 2) (β : Fin q → Fin m → ZMod 2)
    (js : List (Fin q)) :
    ∀ (gs : List Gate), GoodCirc n m gs →
      (∀ pw ∈ ws, pw.2 < n + m + gs.length ∧ depOf n m gs pw.2 ≤ 1) →
      ∃ (extra : List Gate) (taps : Fin q → ℕ),
        let gs' := gs ++ extra
        GoodCirc n m gs' ∧
        gs'.countP nonlinear = gs.countP nonlinear ∧
        ∀ j ∈ js,
          taps j < n + m + gs'.length ∧ depOf n m gs' (taps j) ≤ 1 ∧
          ∀ (a : Fin n) (b : Fin m),
            valOf gs' (taps j) a b = α j a + β j b +
              ((ws.filter (fun pw => decide (pw.1.mask j = 1))).map
                (fun pw => valOf gs pw.2 a b)).sum := by
  induction js with
  | nil =>
    intro gs hgs _
    exact ⟨[], fun _ => 0, by simpa using hgs, by simp, fun _ h => by simp at h⟩
  | cons j0 rest ih =>
    intro gs hgs hws
    obtain ⟨ex1, wsep, hgood1, hwseplt, hcnt1, hdep1, hval1⟩ := buildSep gs hgs (α j0) (β j0)
    set gs1 := gs ++ ex1
    let sel := (ws.filter (fun pw => decide (pw.1.mask j0 = 1))).map Prod.snd
    have hlist : ∀ i ∈ wsep :: sel, i < n + m + gs1.length ∧ depOf n m gs1 i ≤ 1 := by
      intro i hi
      rcases List.mem_cons.1 hi with rfl | hsel
      · exact ⟨hwseplt, by omega⟩
      · obtain ⟨pw, hpwf, rfl⟩ := List.mem_map.1 hsel
        have hpw := (List.mem_filter.1 hpwf).1
        obtain ⟨hlt, hdep⟩ := hws pw hpw
        exact ⟨by simp only [gs1, List.length_append]; omega,
          by rw [depOf_append_prefix n m gs ex1 pw.2 hlt]; exact hdep⟩
    obtain ⟨ex2, wout, hgood2, hwoutlt, hcnt2, hdep2, hval2⟩ :=
      buildXorList (wsep :: sel) 1 gs1 hgood1 hlist
    set gs2 := gs1 ++ ex2
    have hws2 : ∀ pw ∈ ws, pw.2 < n + m + gs2.length ∧ depOf n m gs2 pw.2 ≤ 1 := by
      intro pw hpw
      obtain ⟨hlt, hdep⟩ := hws pw hpw
      have hEq : gs2 = gs ++ (ex1 ++ ex2) := by simp [gs2, gs1, List.append_assoc]
      exact ⟨by rw [hEq, List.length_append]; omega,
        by rw [hEq, depOf_append_prefix n m gs (ex1 ++ ex2) pw.2 hlt]; exact hdep⟩
    obtain ⟨ex3, taps3, hgood3, hcnt3, htaps3⟩ := ih gs2 hgood2 hws2
    let taps : Fin q → ℕ := fun j => if j = j0 then wout else taps3 j
    refine ⟨ex1 ++ ex2 ++ ex3, taps, ?_, ?_, ?_⟩
    · simpa [gs2, gs1, List.append_assoc] using hgood3
    · have hEq : gs ++ (ex1 ++ ex2 ++ ex3) = gs2 ++ ex3 := by simp [gs2, gs1, List.append_assoc]
      rw [hEq, hcnt3, hcnt2, hcnt1]
    · intro j hj
      have hEq : gs ++ (ex1 ++ ex2 ++ ex3) = gs2 ++ ex3 := by simp [gs2, gs1, List.append_assoc]
      rw [hEq]
      by_cases hjj0 : j = j0
      · subst hjj0
        simp only [taps, ↓reduceIte]
        refine ⟨by simp only [List.length_append]; omega,
          by rw [depOf_append_prefix n m gs2 ex3 wout hwoutlt]; exact hdep2, fun a b => ?_⟩
        rw [valOf_append_prefix gs2 ex3 wout hwoutlt a b, hval2 a b]
        simp only [List.map_cons, List.sum_cons, sel, List.map_map]
        have h1 : valOf gs1 wsep a b = α j a + β j b := hval1 a b
        have hmap_eq : ((ws.filter (fun pw => decide (pw.1.mask j = 1))).map
            ((fun i => valOf gs1 i a b) ∘ Prod.snd)) =
            ((ws.filter (fun pw => decide (pw.1.mask j = 1))).map
              (fun pw => valOf gs pw.2 a b)) := by
          refine List.map_congr_left fun pw hpw => ?_
          have hpw_mem := (List.mem_filter.1 hpw).1
          exact valOf_append_prefix gs ex1 pw.2 (hws pw hpw_mem).1 a b
        rw [h1, hmap_eq]
      · have hjrest : j ∈ rest := by
          rcases List.mem_cons.1 hj with rfl | hr
          · exact False.elim (hjj0 rfl)
          · exact hr
        simp only [taps, hjj0, ↓reduceIte]
        obtain ⟨hlt3, hdep3, hval3⟩ := htaps3 j hjrest
        refine ⟨hlt3, hdep3, fun a b => ?_⟩
        rw [hval3 a b]
        congr 1
        refine congrArg List.sum (List.map_congr_left fun pw hpw => ?_)
        have hpw_mem := (List.mem_filter.1 hpw).1
        have hEq2 : gs2 = gs ++ (ex1 ++ ex2) := by simp [gs2, gs1, List.append_assoc]
        rw [hEq2]
        exact valOf_append_prefix gs (ex1 ++ ex2) pw.2 (hws pw hpw_mem).1 a b

private theorem list_sum_flatMap {α β : Type} [AddCommMonoid β] (f : α → List β) (L : List α) :
    (L.flatMap f).sum = (L.map (fun a => (f a).sum)).sum := by
  induction L with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem backward_aux {n m q : ℕ} (G : Fin q → Fin n → Fin m → Bool)
    (u : Fin n) (v : Fin m) (t : ℕ)
    (blocks : (Fin q → ZMod 2) → Matrix (Fin n) (Fin m) (ZMod 2))
    (hsum : ∀ j : Fin q,
      (fun a b => (if G j a b then (1 : ZMod 2) else 0) +
        (if G j a v then (1 : ZMod 2) else 0) +
        (if G j u b then (1 : ZMod 2) else 0) +
        (if G j u v then (1 : ZMod 2) else 0)) =
      ∑ h : Fin q → ZMod 2, (h j) • blocks h)
    (hrank : (∑ h : Fin q → ZMod 2, ((blocks h).rank + 1) / 2) ≤ t) :
    ∃ (C : Circuit) (tap : Fin q → ℕ),
      ReadsBack (n + m) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP nonlinear ≤ t ∧
      ∀ j : Fin q, (depths (n + m) C).getD (tap j) 0 ≤ 1 ∧ Represents (G j) ⟨C.gates, tap j⟩ := by
  let F := ZMod 2
  let Mask := Fin q → F
  let entry : Fin q → Fin n → Fin m → F := fun j a b => if G j a b then 1 else 0
  let anchored : Fin q → Matrix (Fin n) (Fin m) F := fun j a b =>
    entry j a b + entry j a v + entry j u b + entry j u v
  have hdec : ∀ h : Mask, ∃ (a : Fin (blocks h).rank → Fin n → F)
      (b : Fin (blocks h).rank → Fin m → F),
      blocks h = ∑ k : Fin (blocks h).rank, Matrix.vecMulVec (a k) (b k) :=
    fun h => matrix_rank_decomp (blocks h)
  choose ra rb hrab using hdec
  let mkPairs : Mask → List (PairItem n m q) := fun h =>
    let r := (blocks h).rank
    let p := (r + 1) / 2
    let getA : ℕ → Fin n → F := fun k => if hk : k < r then ra h ⟨k, hk⟩ else 0
    let getB : ℕ → Fin m → F := fun k => if hk : k < r then rb h ⟨k, hk⟩ else 0
    (List.finRange p).map fun k =>
      ⟨h, getA (2 * k.val), getB (2 * k.val), getA (2 * k.val + 1), getB (2 * k.val + 1)⟩
  have hmkPairs_len : ∀ h : Mask, (mkPairs h).length = ((blocks h).rank + 1) / 2 := by
    intro h; simp [mkPairs]
  have hmkPairs_mask : ∀ h : Mask, ∀ item ∈ mkPairs h, item.mask = h := by
    intro h item hmem
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hmem
    rfl
  have hmkPairs_sum : ∀ (h : Mask) (a : Fin n) (b : Fin m),
      ((mkPairs h).map fun p => p.a1 a * p.b1 b + p.a2 a * p.b2 b).sum = blocks h a b := by
    intro h a b
    let r := (blocks h).rank
    let p := (r + 1) / 2
    let getA : ℕ → Fin n → F := fun k => if hk : k < r then ra h ⟨k, hk⟩ else 0
    let getB : ℕ → Fin m → F := fun k => if hk : k < r then rb h ⟨k, hk⟩ else 0
    have h1 : ((mkPairs h).map fun it => it.a1 a * it.b1 b + it.a2 a * it.b2 b).sum =
        ∑ k ∈ Finset.range p, (getA (2 * k) a * getB (2 * k) b +
          getA (2 * k + 1) a * getB (2 * k + 1) b) := by
      simp only [mkPairs, List.map_map]
      have hfin : ((List.finRange p).map ((fun it : PairItem n m q => it.a1 a * it.b1 b + it.a2 a * it.b2 b) ∘
          fun k => ⟨h, getA (2 * k.val), getB (2 * k.val), getA (2 * k.val + 1), getB (2 * k.val + 1)⟩)).sum =
          ∑ k : Fin p, (getA (2 * k.val) a * getB (2 * k.val) b +
            getA (2 * k.val + 1) a * getB (2 * k.val + 1) b) := by
        rw [← List.sum_toFinset _ (List.nodup_finRange p)]
        have hto : (List.finRange p).toFinset = Finset.univ := by ext x; simp
        rw [hto]
        rfl
      rw [hfin]
      exact Fin.sum_univ_eq_sum_range (fun k => getA (2 * k) a * getB (2 * k) b +
        getA (2 * k + 1) a * getB (2 * k + 1) b) p
    have h2 : ∑ k ∈ Finset.range p, (getA (2 * k) a * getB (2 * k) b +
          getA (2 * k + 1) a * getB (2 * k + 1) b) =
        ∑ k ∈ Finset.range (2 * p), getA k a * getB k b := by
      clear h1
      induction p with
      | zero => simp
      | succ p0 ihp =>
        rw [Finset.sum_range_succ, ihp, show 2 * (p0 + 1) = 2 * p0 + 1 + 1 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]
    have h3 : ∑ k ∈ Finset.range (2 * p), getA k a * getB k b =
        ∑ k ∈ Finset.range r, getA k a * getB k b := by
      have hle : r ≤ 2 * p := by omega
      symm
      refine Finset.sum_subset (Finset.range_mono hle) fun k hk hnot => ?_
      have hge : ¬ k < r := by simp only [Finset.mem_range] at hnot; exact hnot
      simp [getA, hge]
    have h4 : ∑ k ∈ Finset.range r, getA k a * getB k b = blocks h a b := by
      rw [← Fin.sum_univ_eq_sum_range]
      rw [hrab h, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [getA, getB, k.isLt, Matrix.vecMulVec_apply]
    rw [h1, h2, h3, h4]
  let masksList : List Mask := (Finset.univ : Finset Mask).toList
  let ps : List (PairItem n m q) := masksList.flatMap mkPairs
  have hps_len : ps.length ≤ t := by
    have hlen : ps.length = ∑ h : Mask, ((blocks h).rank + 1) / 2 := by
      simp only [ps, List.length_flatMap, masksList]
      have hmap : (Finset.univ : Finset Mask).toList.map (fun h => (mkPairs h).length) =
          (Finset.univ : Finset Mask).toList.map (fun h => ((blocks h).rank + 1) / 2) :=
        List.map_congr_left fun h _ => hmkPairs_len h
      rw [hmap, ← List.sum_toFinset _ (Finset.nodup_toList (Finset.univ : Finset Mask))]
      have hto : (Finset.univ : Finset Mask).toList.toFinset = Finset.univ := by ext h; simp
      rw [hto]
    rw [hlen]; exact hrank
  have hps_sum : ∀ (j : Fin q) (a : Fin n) (b : Fin m),
      ((ps.filter (fun p => decide (p.mask j = 1))).map
        (fun p => p.a1 a * p.b1 b + p.a2 a * p.b2 b)).sum = anchored j a b := by
    intro j a b
    have hfilt : ps.filter (fun p => decide (p.mask j = 1)) =
        (masksList.filter (fun h => decide (h j = 1))).flatMap mkPairs := by
      simp only [ps, List.filter_flatMap]
      have h1 : ∀ (L : List Mask),
          (L.flatMap (fun h => (mkPairs h).filter (fun p => decide (p.mask j = 1)))) =
          (L.filter (fun h => decide (h j = 1))).flatMap mkPairs := by
        intro L
        induction L with
        | nil => simp
        | cons h rest ihL =>
          simp only [List.flatMap_cons, List.filter_cons]
          by_cases hhj : h j = 1
          · have hfilt_all : (mkPairs h).filter (fun p => decide (p.mask j = 1)) = mkPairs h :=
              List.filter_eq_self.2 fun item hitem => by simp [hmkPairs_mask h item hitem, hhj]
            simp [hhj, hfilt_all, ihL]
          · have hfilt_nil : (mkPairs h).filter (fun p => decide (p.mask j = 1)) = [] :=
              List.filter_eq_nil_iff.2 fun item hitem => by simp [hmkPairs_mask h item hitem, hhj]
            simp [hhj, hfilt_nil, ihL]
      exact h1 masksList
    rw [hfilt, List.map_flatMap, list_sum_flatMap]
    have hmap2 : ((masksList.filter (fun h => decide (h j = 1))).map
        (fun h => ((mkPairs h).map fun p => p.a1 a * p.b1 b + p.a2 a * p.b2 b).sum)) =
        (masksList.filter (fun h => decide (h j = 1))).map (fun h => blocks h a b) :=
      List.map_congr_left fun h _ => hmkPairs_sum h a b
    rw [hmap2]
    have hnd : (masksList.filter (fun h => decide (h j = 1))).Nodup :=
      (Finset.nodup_toList _).filter _
    rw [← List.sum_toFinset _ hnd]
    have hto : (masksList.filter (fun h => decide (h j = 1))).toFinset =
        (Finset.univ : Finset Mask).filter (fun h => h j = 1) := by
      ext h; simp [masksList]
    rw [hto]
    have hs := congrFun (congrFun (hsum j) a) b
    change anchored j a b = (∑ h : Mask, (h j) • blocks h) a b at hs
    rw [hs, Matrix.sum_apply]
    symm
    calc ∑ h : Mask, ((h j) • blocks h) a b
        = ∑ h ∈ (Finset.univ : Finset Mask).filter (fun h => h j = 1), ((h j) • blocks h) a b := by
          symm
          refine Finset.sum_subset (Finset.filter_subset _ _) fun h _ hnot => ?_
          have hne : h j ≠ 1 := by simpa using hnot
          have h0 : h j = 0 := by rcases zmod2_cases (h j) with h0 | h1; exact h0; exact False.elim (hne h1)
          simp [h0]
      _ = ∑ h ∈ (Finset.univ : Finset Mask).filter (fun h => h j = 1), blocks h a b := by
          refine Finset.sum_congr rfl fun h hh => ?_
          have h1 : h j = 1 := (Finset.mem_filter.1 hh).2
          simp [h1]
  have hgood0 : GoodCirc n m [] := ⟨fun j hj => by simp at hj, fun _ h => by simp at h⟩
  obtain ⟨ex1, ws, hgood1, hcnt1, hmap1, hprop1⟩ := buildPairs ps [] hgood0
  set gs1 := [] ++ ex1
  let α : Fin q → Fin n → F := fun j a =>
    entry j a v + ((ps.filter (fun p => decide (p.mask j = 1))).map (fun p => p.a1 a * p.a2 a)).sum
  let β : Fin q → Fin m → F := fun j b =>
    entry j u b + entry j u v +
      ((ps.filter (fun p => decide (p.mask j = 1))).map (fun p => p.b1 b * p.b2 b)).sum
  have hws1 : ∀ pw ∈ ws, pw.2 < n + m + gs1.length ∧ depOf n m gs1 pw.2 ≤ 1 := by
    intro pw hpw
    obtain ⟨hlt, hdep, _⟩ := hprop1 pw hpw
    exact ⟨hlt, by omega⟩
  obtain ⟨ex2, taps, hgood2, hcnt2, htaps2⟩ := buildOutputs ws α β (List.finRange q) gs1 hgood1 hws1
  set gs2 := gs1 ++ ex2
  refine ⟨⟨gs2, 0⟩, taps, hgood2.1, hgood2.2, ?_, ?_⟩
  · rw [hcnt2, hcnt1]; simp; exact hps_len
  · intro j
    obtain ⟨_, hdepj, hvalj⟩ := htaps2 j (List.mem_finRange j)
    refine ⟨hdepj, fun a b => ?_⟩
    apply b2z_inj
    change valOf gs2 (taps j) a b = entry j a b
    rw [hvalj a b]
    have hws_sum : ((ws.filter (fun pw => decide (pw.1.mask j = 1))).map
        (fun pw => valOf gs1 pw.2 a b)).sum =
        ((ps.filter (fun p => decide (p.mask j = 1))).map
          (fun p => (p.a1 a + p.b2 b) * (p.a2 a + p.b1 b))).sum := by
      have h1 : ((ws.filter (fun pw => decide (pw.1.mask j = 1))).map
          (fun pw => valOf gs1 pw.2 a b)) =
          ((ws.filter (fun pw => decide (pw.1.mask j = 1))).map
            (fun pw => (pw.1.a1 a + pw.1.b2 b) * (pw.1.a2 a + pw.1.b1 b))) := by
        refine List.map_congr_left fun pw hpw => ?_
        exact (hprop1 pw (List.mem_filter.1 hpw).1).2.2 a b
      rw [h1]
      have h2 : (ws.filter (fun pw => decide (pw.1.mask j = 1))).map
          (fun pw => (pw.1.a1 a + pw.1.b2 b) * (pw.1.a2 a + pw.1.b1 b)) =
          ((ws.map Prod.fst).filter (fun p => decide (p.mask j = 1))).map
            (fun p => (p.a1 a + p.b2 b) * (p.a2 a + p.b1 b)) := by
        rw [List.filter_map, List.map_map]
        rfl
      rw [h2, hmap1]
    rw [hws_sum]
    have hsplit_sum : ∀ (L : List (PairItem n m q)),
        (L.map (fun p => (p.a1 a + p.b2 b) * (p.a2 a + p.b1 b))).sum =
        (L.map (fun p => p.a1 a * p.b1 b + p.a2 a * p.b2 b)).sum +
        (L.map (fun p => p.a1 a * p.a2 a)).sum +
        (L.map (fun p => p.b1 b * p.b2 b)).sum := by
      intro L
      induction L with
      | nil => simp
      | cons p rest ihL =>
        simp only [List.map_cons, List.sum_cons, ihL]
        ring
    rw [hsplit_sum, hps_sum j a b]
    dsimp only [α, β, anchored]
    set sA := ((ps.filter (fun p => decide (p.mask j = 1))).map (fun p => p.a1 a * p.a2 a)).sum
    set sB := ((ps.filter (fun p => decide (p.mask j = 1))).map (fun p => p.b1 b * p.b2 b)).sum
    have hz : ∀ t : F, t + t = 0 := zmod2_add_self
    calc entry j a v + sA + (entry j u b + entry j u v + sB) +
          (entry j a b + entry j a v + entry j u b + entry j u v + sA + sB)
        = entry j a b + (entry j a v + entry j a v) + (entry j u b + entry j u b) +
          (entry j u v + entry j u v) + (sA + sA) + (sB + sB) := by ring
      _ = entry j a b := by simp only [hz, add_zero]

theorem main_aux :
    let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
      (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
    let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.gates.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
        (List.replicate width 0)
    let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
        (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
        ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
          PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩
    ∀ (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ),
      let F := ZMod 2
      let Mask := Fin q → F
      let Mat := Matrix (Fin n) (Fin m) F
      let entry := fun j a b => if G j a b then (1 : F) else 0
      let anchored : Fin q → Mat := fun j a b =>
        entry j a b + entry j a v + entry j u b + entry j u v
      fits n m q G t ↔
        ∃ blocks : Mask → Mat,
          (∀ j : Fin q, anchored j = ∑ h : Mask, (h j) • blocks h) ∧
          (∑ h : Mask, ((blocks h).rank + 1) / 2) ≤ t := by
  intro nl dp ft n m q G u v t F Mask Mat entry anchored
  constructor
  · rintro ⟨C, tap, hRB, hfan, hcnt, htap⟩
    exact forward_aux G u v t C tap hRB hfan hcnt htap
  · rintro ⟨blocks, hsum, hrank⟩
    exact backward_aux G u v t blocks hsum hrank

end Circ

namespace LA

open Matrix

private abbrev K := ZMod 2

variable {n m : ℕ}

theorem z2 : ∀ x : K, x = 0 ∨ x = 1 := by decide

theorem rank_add_le' {ι κ : Type} [Fintype κ] (A B : Matrix ι κ K) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self A.mulVecLin v) (LinearMap.mem_range_self B.mulVecLin v)
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem range_fromCols {k : ℕ} (A B : Matrix (Fin k) (Fin m) K) :
    LinearMap.range (Matrix.fromCols A B).mulVecLin =
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    simp only [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  · apply sup_le
    · rintro _ ⟨v, rfl⟩
      refine ⟨Sum.elim v 0, ?_⟩
      simp
    · rintro _ ⟨v, rfl⟩
      refine ⟨Sum.elim 0 v, ?_⟩
      simp

theorem rank_fromCols_le (A B : Matrix (Fin n) (Fin m) K) :
    (Matrix.fromCols A B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [range_fromCols]
  exact Submodule.finrank_add_le_finrank_add_finrank _ _

theorem rank_fromCols_self_le (S : Matrix (Fin n) (Fin m) K) :
    (Matrix.fromCols S S).rank ≤ S.rank := by
  unfold Matrix.rank
  rw [range_fromCols, sup_idem]

theorem row_le_of_add {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A B : Matrix ι κ K)
    (h : (A + B).rank = A.rank + B.rank) :
    LinearMap.range Bᵀ.mulVecLin ≤ LinearMap.range (A + B)ᵀ.mulVecLin := by
  have hle : LinearMap.range (A + B)ᵀ.mulVecLin ≤
      LinearMap.range Aᵀ.mulVecLin ⊔ LinearMap.range Bᵀ.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    simp only [Matrix.mulVecLin_apply, Matrix.transpose_add, Matrix.add_mulVec]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self Aᵀ.mulVecLin v)
      (LinearMap.mem_range_self Bᵀ.mulVecLin v)
  have hrk : Module.finrank K (LinearMap.range (A + B)ᵀ.mulVecLin) =
      Module.finrank K (LinearMap.range Aᵀ.mulVecLin) +
        Module.finrank K (LinearMap.range Bᵀ.mulVecLin) := by
    have e1 := Matrix.rank_transpose (A + B)
    have e2 := Matrix.rank_transpose A
    have e3 := Matrix.rank_transpose B
    unfold Matrix.rank at e1 e2 e3 h
    omega
  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    rw [hrk]; exact Submodule.finrank_add_le_finrank_add_finrank _ _)
  rw [heq]
  exact le_sup_right

theorem rows_tight (X Y P Q S : Matrix (Fin n) (Fin m) K) (hX : X = P + S) (hY : Y = Q + S)
    (ht : (Matrix.fromCols X Y).rank =
      (Matrix.fromCols P Q).rank + (Matrix.fromCols S S).rank) :
    (Matrix.fromRows X Y).rank + S.rank ≤ X.rank + Y.rank := by
  have hsum : Matrix.fromCols X Y = Matrix.fromCols P Q + Matrix.fromCols S S := by
    subst hX hY
    ext i (j | j) <;> simp
  rw [hsum] at ht
  have hle := row_le_of_add (Matrix.fromCols P Q) (Matrix.fromCols S S) ht
  rw [← hsum] at hle
  have hS : LinearMap.range Sᵀ.mulVecLin ≤
      LinearMap.range Xᵀ.mulVecLin ⊓ LinearMap.range Yᵀ.mulVecLin := by
    rintro _ ⟨w, rfl⟩
    have hm : (Matrix.fromCols S S)ᵀ.mulVecLin w ∈ LinearMap.range (Matrix.fromCols X Y)ᵀ.mulVecLin :=
      hle ⟨w, rfl⟩
    obtain ⟨w', hw'⟩ := hm
    simp only [Matrix.mulVecLin_apply, Matrix.transpose_fromCols, Matrix.fromRows_mulVec] at hw'
    constructor
    · refine ⟨w', ?_⟩
      funext i
      have := congrFun hw' (Sum.inl i)
      simpa [Matrix.mulVec_transpose] using this
    · refine ⟨w', ?_⟩
      funext i
      have := congrFun hw' (Sum.inr i)
      simpa [Matrix.mulVec_transpose] using this
  have hfr : (Matrix.fromRows X Y).rank =
      Module.finrank K ↥(LinearMap.range Xᵀ.mulVecLin ⊔ LinearMap.range Yᵀ.mulVecLin) := by
    rw [← Matrix.rank_transpose, Matrix.transpose_fromRows]
    unfold Matrix.rank
    rw [range_fromCols]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range Xᵀ.mulVecLin)
    (LinearMap.range Yᵀ.mulVecLin)
  have hmono := Submodule.finrank_mono hS
  have e1 := Matrix.rank_transpose X
  have e2 := Matrix.rank_transpose Y
  have e3 := Matrix.rank_transpose S
  unfold Matrix.rank at e1 e2 e3 hfr ⊢
  omega

theorem dual_pair (w1 w2 : Fin m → K) (h : LinearIndependent K ![w1, w2]) :
    ∃ v1 v2 : Fin m → K, w1 ⬝ᵥ v1 = 1 ∧ w2 ⬝ᵥ v1 = 0 ∧ w1 ⬝ᵥ v2 = 0 ∧ w2 ⬝ᵥ v2 = 1 := by
  rw [LinearIndependent.pair_iff] at h
  have n1 : w1 ≠ 0 := fun e => by
    have := h 1 0 (by simp [e]); exact one_ne_zero this.1
  have n2 : w2 ≠ 0 := fun e => by
    have := h 0 1 (by simp [e]); exact one_ne_zero this.2
  have n3 : w1 + w2 ≠ 0 := fun e => by
    have := h 1 1 (by simpa using e); exact one_ne_zero this.1
  have dsingle : ∀ (w : Fin m → K) (k : Fin m), w ⬝ᵥ Pi.single k 1 = w k := by
    intro w k; simp [dotProduct_single]
  obtain ⟨k, hk⟩ := Function.ne_iff.mp n1
  have hk1 : w1 k = 1 := (z2 _).resolve_left hk
  rcases z2 (w2 k) with h2k | h2k
  · obtain ⟨l, hl⟩ := Function.ne_iff.mp n2
    have hl1 : w2 l = 1 := (z2 _).resolve_left hl
    refine ⟨Pi.single k 1, Pi.single l 1 - (w1 l) • Pi.single k 1, ?_, ?_, ?_, ?_⟩
    · rw [dsingle]; exact hk1
    · rw [dsingle]; exact h2k
    · rw [dotProduct_sub, dotProduct_smul, dsingle, dsingle, hk1]; simp
    · rw [dotProduct_sub, dotProduct_smul, dsingle, dsingle, h2k, hl1]; simp
  · obtain ⟨l, hl⟩ := Function.ne_iff.mp n3
    simp only [Pi.add_apply, Pi.zero_apply] at hl
    rcases z2 (w1 l) with h1l | h1l <;> rcases z2 (w2 l) with h2l | h2l
    · rw [h1l, h2l] at hl; exact absurd rfl hl
    · refine ⟨Pi.single k 1 - Pi.single l 1, Pi.single l 1, ?_, ?_, ?_, ?_⟩ <;>
        simp only [dotProduct_sub, dsingle, hk1, h2k, h1l, h2l] <;> decide
    · refine ⟨Pi.single l 1, Pi.single k 1 - Pi.single l 1, ?_, ?_, ?_, ?_⟩ <;>
        simp only [dotProduct_sub, dsingle, hk1, h2k, h1l, h2l] <;> decide
    · rw [h1l, h2l] at hl; exact absurd (by decide) hl

theorem proj (X : Matrix (Fin n) (Fin m) K) (a1 a2 c1 c2 : Fin n → K)
    (hc1 : c1 ∈ LinearMap.range X.mulVecLin) (hc2 : c2 ∈ LinearMap.range X.mulVecLin)
    (d11 : a1 ⬝ᵥ c1 = 1) (d12 : a1 ⬝ᵥ c2 = 0) (d21 : a2 ⬝ᵥ c1 = 0) (d22 : a2 ⬝ᵥ c2 = 1) :
    (X - Matrix.vecMulVec c1 (a1 ᵥ* X) - Matrix.vecMulVec c2 (a2 ᵥ* X)).rank + 2 ≤ X.rank := by
  set X' := X - Matrix.vecMulVec c1 (a1 ᵥ* X) - Matrix.vecMulVec c2 (a2 ᵥ* X)
  set R' := LinearMap.range X'.mulVecLin
  set R := LinearMap.range X.mulVecLin
  set T := Submodule.span K (Set.range ![c1, c2])
  have hmv : ∀ v, X' *ᵥ v = X *ᵥ v - ((a1 ᵥ* X) ⬝ᵥ v) • c1 - ((a2 ᵥ* X) ⬝ᵥ v) • c2 := by
    intro v
    simp only [X', Matrix.sub_mulVec]
    congr 1
    · congr 1
      ext i; simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum, mul_comm,
        mul_left_comm]
    · ext i; simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum, mul_comm,
        mul_left_comm]
  have hRR : R' ≤ R := by
    rintro _ ⟨v, rfl⟩
    simp only [Matrix.mulVecLin_apply, hmv]
    exact R.sub_mem (R.sub_mem ⟨v, rfl⟩ (R.smul_mem _ hc1)) (R.smul_mem _ hc2)
  have hTR : T ≤ R := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hc1
    · exact hc2
  have hdot : ∀ y ∈ R', a1 ⬝ᵥ y = 0 ∧ a2 ⬝ᵥ y = 0 := by
    rintro _ ⟨v, rfl⟩
    simp only [Matrix.mulVecLin_apply, hmv, dotProduct_sub, dotProduct_smul, d11, d12, d21, d22,
      Matrix.dotProduct_mulVec, smul_eq_mul]
    constructor <;> ring
  have hind : LinearIndependent K ![c1, c2] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 := congrArg (fun y => a1 ⬝ᵥ y) hst
    have e2 := congrArg (fun y => a2 ⬝ᵥ y) hst
    simp only [dotProduct_add, dotProduct_smul, d11, d12, d21, d22, smul_eq_mul,
      dotProduct_zero] at e1 e2
    constructor
    · simpa using e1
    · simpa using e2
  have hT : Module.finrank K T = 2 := by
    rw [finrank_span_eq_card hind]; simp
  have hinf : R' ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro y ⟨hy1, hy2⟩
    obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy2
    rw [Fin.sum_univ_two] at hf
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hf
    obtain ⟨e1, e2⟩ := hdot y hy1
    rw [← hf] at e1 e2
    simp only [dotProduct_add, dotProduct_smul, d11, d12, d21, d22, smul_eq_mul] at e1 e2
    have f0 : f 0 = 0 := by simpa using e1
    have f1 : f 1 = 0 := by simpa using e2
    rw [← hf, f0, f1]; simp
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq R' T
  rw [hinf, finrank_bot] at hdim
  have hsup := Submodule.finrank_mono (sup_le hRR hTR)
  change Module.finrank K R' + 2 ≤ Module.finrank K R
  omega

theorem upper (X Y : Matrix (Fin n) (Fin m) K)
    (h : (Matrix.fromRows X Y).rank + 2 ≤ X.rank + Y.rank) :
    ∃ S : Matrix (Fin n) (Fin m) K, S.rank ≤ 2 ∧ (X - S).rank + 1 ≤ X.rank ∧
      (Y - S).rank + 1 ≤ Y.rank := by
  set U := LinearMap.range Xᵀ.mulVecLin
  set W := LinearMap.range Yᵀ.mulVecLin
  have hfr : (Matrix.fromRows X Y).rank = Module.finrank K ↥(U ⊔ W) := by
    rw [← Matrix.rank_transpose, Matrix.transpose_fromRows]
    unfold Matrix.rank
    rw [range_fromCols]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq U W
  have e1 : X.rank = Module.finrank K U := by rw [← Matrix.rank_transpose]; rfl
  have e2 : Y.rank = Module.finrank K W := by rw [← Matrix.rank_transpose]; rfl
  have h2 : 1 < Module.finrank K ↥(U ⊓ W) := by
    omega
  obtain ⟨x, hx⟩ : ∃ x : ↥(U ⊓ W), x ≠ 0 := by
    have : 0 < Module.finrank K ↥(U ⊓ W) := by omega
    exact (Module.finrank_pos_iff_exists_ne_zero).mp this
  obtain ⟨y, hxy⟩ := exists_linearIndependent_pair_of_one_lt_finrank h2 hx
  have hli : LinearIndependent K ![(x : Fin m → K), (y : Fin m → K)] := by
    have := hxy.map' (U ⊓ W).subtype (Submodule.ker_subtype _)
    convert this using 1
    ext i; fin_cases i <;> rfl
  obtain ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩⟩ := Submodule.mem_inf.mp x.2
  obtain ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩⟩ := Submodule.mem_inf.mp y.2
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at ha1 hb1 ha2 hb2
  generalize (x : Fin m → K) = w1 at ha1 hb1 hli
  generalize (y : Fin m → K) = w2 at ha2 hb2 hli
  obtain ⟨v1, v2, d11, d21, d12, d22⟩ := dual_pair w1 w2 hli
  set c1 := X *ᵥ v1
  set c2 := X *ᵥ v2
  set e1' := Y *ᵥ v1
  set e2' := Y *ᵥ v2
  have hX := proj X a1 a2 c1 c2 ⟨v1, rfl⟩ ⟨v2, rfl⟩
    (by simp only [c1, Matrix.dotProduct_mulVec, ha1]; exact d11)
    (by simp only [c2, Matrix.dotProduct_mulVec, ha1]; exact d12)
    (by simp only [c1, Matrix.dotProduct_mulVec, ha2]; exact d21)
    (by simp only [c2, Matrix.dotProduct_mulVec, ha2]; exact d22)
  have hY := proj Y b1 b2 e1' e2' ⟨v1, rfl⟩ ⟨v2, rfl⟩
    (by simp only [e1', Matrix.dotProduct_mulVec, hb1]; exact d11)
    (by simp only [e2', Matrix.dotProduct_mulVec, hb1]; exact d12)
    (by simp only [e1', Matrix.dotProduct_mulVec, hb2]; exact d21)
    (by simp only [e2', Matrix.dotProduct_mulVec, hb2]; exact d22)
  rw [ha1, ha2] at hX
  rw [hb1, hb2] at hY
  refine ⟨Matrix.vecMulVec c1 w1 + Matrix.vecMulVec e2' w2, ?_, ?_, ?_⟩
  · have := rank_add_le' (Matrix.vecMulVec c1 w1) (Matrix.vecMulVec e2' w2)
    have r1 := Matrix.rank_vecMulVec_le c1 w1
    have r2 := Matrix.rank_vecMulVec_le e2' w2
    omega
  · have eq : X - (Matrix.vecMulVec c1 w1 + Matrix.vecMulVec e2' w2) =
        (X - Matrix.vecMulVec c1 w1 - Matrix.vecMulVec c2 w2) + Matrix.vecMulVec (c2 - e2') w2 := by
      ext i j; simp [Matrix.vecMulVec_apply, sub_mul]; ring
    rw [eq]
    have := rank_add_le' (X - Matrix.vecMulVec c1 w1 - Matrix.vecMulVec c2 w2)
      (Matrix.vecMulVec (c2 - e2') w2)
    have r1 := Matrix.rank_vecMulVec_le (c2 - e2') w2
    omega
  · have eq : Y - (Matrix.vecMulVec c1 w1 + Matrix.vecMulVec e2' w2) =
        (Y - Matrix.vecMulVec e1' w1 - Matrix.vecMulVec e2' w2) + Matrix.vecMulVec (e1' - c1) w1 := by
      ext i j; simp [Matrix.vecMulVec_apply, sub_mul]; ring
    rw [eq]
    have := rank_add_le' (Y - Matrix.vecMulVec e1' w1 - Matrix.vecMulVec e2' w2)
      (Matrix.vecMulVec (e1' - c1) w1)
    have r1 := Matrix.rank_vecMulVec_le (e1' - c1) w1
    omega

theorem price (X Y : Matrix (Fin n) (Fin m) K)
    (hr : (Matrix.fromCols X Y).rank = X.rank + Y.rank) (t : ℕ) :
    (∃ P Q S : Matrix (Fin n) (Fin m) K, X = P + S ∧ Y = Q + S ∧
      (P.rank+1)/2 + (Q.rank+1)/2 + (S.rank+1)/2 ≤ t) ↔
    (X.rank+1)/2 + (Y.rank+1)/2 -
      (if X.rank % 2 = 1 ∧ Y.rank % 2 = 1 ∧ (Matrix.fromRows X Y).rank + 2 ≤ X.rank + Y.rank
        then 1 else 0) ≤ t := by
  constructor
  · rintro ⟨P, Q, S, hX, hY, ht⟩
    have hsum : Matrix.fromCols X Y = Matrix.fromCols P Q + Matrix.fromCols S S := by
      subst hX hY
      ext i (j | j) <;> simp
    have a1 : (Matrix.fromCols X Y).rank ≤
        (Matrix.fromCols P Q).rank + (Matrix.fromCols S S).rank := by
      rw [hsum]; exact rank_add_le' _ _
    have a2 := rank_fromCols_le P Q
    have a3 := rank_fromCols_self_le S
    have a4 : X.rank ≤ P.rank + S.rank := by rw [hX]; exact rank_add_le' _ _
    have a5 : Y.rank ≤ Q.rank + S.rank := by rw [hY]; exact rank_add_le' _ _
    by_cases htight : (Matrix.fromCols X Y).rank =
        (Matrix.fromCols P Q).rank + (Matrix.fromCols S S).rank
    · have a6 := rows_tight X Y P Q S hX hY htight
      split_ifs with hs <;> omega
    · split_ifs with hs <;> omega
  · intro ht
    split_ifs at ht with hs
    · obtain ⟨h1, h2, h3⟩ := hs
      obtain ⟨S, hS, hXS, hYS⟩ := upper X Y h3
      refine ⟨X - S, Y - S, S, by simp, by simp, ?_⟩
      omega
    · refine ⟨X, Y, 0, by simp, by simp, ?_⟩
      have : (0 : Matrix (Fin n) (Fin m) K).rank = 0 := by simp
      omega

def mask (a b : K) : Fin 2 → K := ![a, b]

theorem mask_sum {A : Type} [AddCommMonoid A] (f : (Fin 2 → K) → A) :
    ∑ h, f h = f (mask 0 0) + f (mask 0 1) + f (mask 1 0) + f (mask 1 1) := by
  have hs : (Finset.univ : Finset (Fin 2 → K)) = {(mask 0 0), (mask 0 1), (mask 1 0), (mask 1 1)} := by decide
  rw [hs]
  simp only [Finset.sum_insert (by decide : (mask 0 0) ∉ {(mask 0 1), (mask 1 0), (mask 1 1)}),
    Finset.sum_insert (by decide : mask 0 1 ∉ {(mask 1 0), (mask 1 1)}),
    Finset.sum_insert (by decide : mask 1 0 ∉ {(mask 1 1)}), Finset.sum_singleton, add_assoc]

theorem mask_crit (Aj : Fin 2 → Matrix (Fin n) (Fin m) K) (t : ℕ) :
    (∃ blocks : (Fin 2 → K) → Matrix (Fin n) (Fin m) K,
      (∀ j : Fin 2, Aj j = ∑ h, h j • blocks h) ∧
      (∑ h, ((blocks h).rank + 1) / 2) ≤ t) ↔
    ∃ P Q S : Matrix (Fin n) (Fin m) K, Aj 0 = P + S ∧ Aj 1 = Q + S ∧
      (P.rank+1)/2 + (Q.rank+1)/2 + (S.rank+1)/2 ≤ t := by
  constructor
  · rintro ⟨T, he, ht⟩
    refine ⟨T (mask 1 0), T (mask 0 1), T (mask 1 1), ?_, ?_, ?_⟩
    · simpa [mask_sum, mask] using he 0
    · simpa [mask_sum, mask] using he 1
    · rw [mask_sum] at ht
      omega
  · rintro ⟨P, Q, S, hA, hB, ht⟩
    let T := fun h : Fin 2 → K => if h 0 = 0 then (if h 1 = 0 then 0 else Q)
                              else (if h 1 = 0 then P else S)
    refine ⟨T, ?_, ?_⟩
    · intro j
      fin_cases j <;> simp [mask_sum, mask, T, hA, hB]
    · rw [mask_sum]
      have : (0 : Matrix (Fin n) (Fin m) K).rank = 0 := by simp
      simp only [T]
      simp [mask]
      omega

end LA
end PEqualNP.Outside.L_meta_29736

theorem PEqualNP.Outside.L_meta_29736 :
(let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩
∀ (n m : ℕ) (G : Fin 2 → Fin n → Fin m → Bool) (u : Fin n) (v : Fin m),
  let F := ZMod 2
  let entry := fun j x y => if G j x y then (1 : F) else 0
  let A : Fin 2 → Matrix (Fin n) (Fin m) F := fun j x y =>
    entry j x y + entry j x v + entry j u y + entry j u v
  let X := A 0
  let Y := A 1
  let r := X.rank
  let s := Y.rank
  (Matrix.fromCols X Y).rank = r+s →
  let save := if r % 2 = 1 ∧ s % 2 = 1 ∧ (Matrix.fromRows X Y).rank+2 ≤ r+s then 1 else 0
  ∀ t : ℕ, fits n m 2 G t ↔ (r+1)/2+(s+1)/2-save ≤ t) := by
  intro nonlinear depths fits n m G u v F entry A X Y r s hrank save t
  have key := PEqualNP.Outside.L_meta_29736.Circ.main_aux n m 2 G u v t
  exact (key.trans (PEqualNP.Outside.L_meta_29736.LA.mask_crit A t)).trans
    (PEqualNP.Outside.L_meta_29736.LA.price X Y hrank t)
