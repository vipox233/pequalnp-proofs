import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29768

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

private abbrev PairItem (n m q : ℕ) : Type :=
  (Fin q → ZMod 2) × (Fin n → ZMod 2) × (Fin m → ZMod 2) × (Fin n → ZMod 2) × (Fin m → ZMod 2)

private def PairItem.mask {n m q : ℕ} (p : PairItem n m q) : Fin q → ZMod 2 := p.1
private def PairItem.a1 {n m q : ℕ} (p : PairItem n m q) : Fin n → ZMod 2 := p.2.1
private def PairItem.b1 {n m q : ℕ} (p : PairItem n m q) : Fin m → ZMod 2 := p.2.2.1
private def PairItem.a2 {n m q : ℕ} (p : PairItem n m q) : Fin n → ZMod 2 := p.2.2.2.1
private def PairItem.b2 {n m q : ℕ} (p : PairItem n m q) : Fin m → ZMod 2 := p.2.2.2.2

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

private theorem main_aux :
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

section Pairing

open Module

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {k : ℕ}

private noncomputable def pairCoordinates (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) :
    K →ₗ[F] (Fin k → F) :=
  LinearMap.pi fun i => bit.comp (LinearMap.mulLeft F (b i))

private theorem pairCoordinates_apply (b : Basis (Fin k) F K)
    (bit : K →ₗ[F] F) (x : K) (i : Fin k) :
    pairCoordinates b bit x i = bit (b i * x) := rfl

private noncomputable def pairEquiv (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hbit : bit ≠ 0) :
    K ≃ₗ[F] (Fin k → F) := by
  letI : FiniteDimensional F K := b.finiteDimensional_of_finite
  have dim : finrank F K = finrank F (Fin k → F) := by
    simp [Module.finrank_eq_card_basis b]
  have hinj : Function.Injective (pairCoordinates b bit) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hn
    have hz : bit.comp (LinearMap.mulLeft F x) = 0 := by
      apply b.ext
      intro i
      have hi := congrFun (LinearMap.mem_ker.mp hx) i
      simpa [pairCoordinates_apply, mul_comm x (b i)] using hi
    apply hbit
    ext y
    have hy := DFunLike.congr_fun hz (x⁻¹ * y)
    simpa [← mul_assoc, mul_inv_cancel₀ hn] using hy
  exact LinearEquiv.ofBijective (pairCoordinates b bit)
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mp hinj⟩

private noncomputable def pairMatrix (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (C : K →ₗ[F] K) : Matrix (Fin k) (Fin k) F :=
  fun i j => bit (b i * C (b j))

private noncomputable def pairMap (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hbit : bit ≠ 0)
    (A : Matrix (Fin k) (Fin k) F) : K →ₗ[F] K :=
  (pairEquiv b bit hbit).symm.toLinearMap.comp (Matrix.toLin b (Pi.basisFun F _) A)

private theorem pair_toLin_entry (b : Basis (Fin k) F K) (A : Matrix (Fin k) (Fin k) F)
    (i j : Fin k) : Matrix.toLin b (Pi.basisFun F _) A (b j) i = A i j := by
  rw [Matrix.toLin_self]
  simp [Pi.single_apply, mul_ite]

private theorem pairMatrix_pairMap (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (A : Matrix (Fin k) (Fin k) F) :
    pairMatrix b bit (pairMap b bit hbit A) = A := by
  ext i j
  change pairEquiv b bit hbit ((pairEquiv b bit hbit).symm
    (Matrix.toLin b (Pi.basisFun F _) A (b j))) i = A i j
  rw [LinearEquiv.apply_symm_apply, pair_toLin_entry]

private theorem pairMatrix_injective (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) : Function.Injective (pairMatrix b bit) := by
  intro C D h
  apply b.ext
  intro j
  apply (pairEquiv b bit hbit).injective
  funext i
  exact congrFun (congrFun h i) j

private theorem rank_pairMatrix (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (C : K →ₗ[F] K) :
    (pairMatrix b bit C).rank = finrank F (LinearMap.range C) := by
  rw [Matrix.rank_eq_finrank_range_toLin _ (Pi.basisFun F _) b]
  have h : Matrix.toLin b (Pi.basisFun F _) (pairMatrix b bit C) =
      (pairEquiv b bit hbit).toLinearMap.comp C := by
    apply b.ext
    intro j
    funext i
    rw [pair_toLin_entry]
    rfl
  rw [h, LinearMap.range_comp, LinearEquiv.finrank_map_eq]

private noncomputable def pairAnchor (A : Matrix (Fin k) (Fin k) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F :=
  fun i j => Fin.cases 0 (fun i => Fin.cases 0 (A i) j) i

@[local simp] private theorem pairAnchor_zero_left (A : Matrix (Fin k) (Fin k) F) (j : Fin (k + 1)) :
    pairAnchor A 0 j = 0 := rfl

@[local simp] private theorem pairAnchor_zero_right (A : Matrix (Fin k) (Fin k) F) (i : Fin (k + 1)) :
    pairAnchor A i 0 = 0 := by
  refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

@[local simp] private theorem pairAnchor_succ_succ (A : Matrix (Fin k) (Fin k) F) (i j : Fin k) :
    pairAnchor A i.succ j.succ = A i j := rfl

private theorem pairAnchor_submatrix (A : Matrix (Fin (k + 1)) (Fin (k + 1)) F)
    (hrow : ∀ j, A 0 j = 0) (hcol : ∀ i, A i 0 = 0) :
    pairAnchor (A.submatrix Fin.succ Fin.succ) = A := by
  ext i j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) j) i
  · exact (hrow j).symm
  · exact (hcol i.succ).symm
  · rfl

private theorem rank_pairAnchor (A : Matrix (Fin k) (Fin k) F) : (pairAnchor A).rank = A.rank := by
  classical
  let e : (Fin k → F) →ₗ[F] (Fin (k + 1) → F) :=
    { toFun := Fin.cases 0
      map_add' := by
        intro x y
        funext i
        refine Fin.cases ?_ (fun _ => rfl) i
        simp
      map_smul' := by
        intro a x
        funext i
        refine Fin.cases ?_ (fun _ => rfl) i
        simp }
  let p : (Fin (k + 1) → F) →ₗ[F] (Fin k → F) :=
    { toFun := fun x i => x i.succ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he : Function.Injective e := fun _ _ h => funext fun i => congrFun h i.succ
  have hp : LinearMap.range p = ⊤ :=
    LinearMap.range_eq_top.mpr (fun x => ⟨e x, rfl⟩)
  have heq : (pairAnchor A).mulVecLin = e.comp (A.mulVecLin.comp p) := by
    ext x i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [e, Matrix.mulVec, dotProduct]
    · simp [e, p, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [Matrix.rank, Matrix.rank, heq, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ hp]
  exact (Submodule.equivMapOfInjective e he _).finrank_eq.symm

private theorem rank_pairAnchor_pairMatrix (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (C : K →ₗ[F] K) :
    (pairAnchor (pairMatrix b bit C)).rank = finrank F (LinearMap.range C) :=
  (rank_pairAnchor _).trans (rank_pairMatrix b bit hbit C)

private theorem pair_add_lmul (bit : K →ₗ[F] F) (C : K →ₗ[F] K) (t x y : K) :
    bit (x * (C + LinearMap.mulLeft F t) y) = bit (x * C y) + bit (t * x * y) := by
  change bit (x * (C y + t * y)) = _
  rw [mul_add, map_add, ← mul_assoc, mul_comm x t]

private theorem pairAnchor_pairMatrix_apply (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (C : K →ₗ[F] K) (i j : Fin (k + 1)) :
    pairAnchor (pairMatrix b bit C) i j =
      bit (Fin.cases 0 b i * C (Fin.cases 0 b j)) := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) j) i
  · simp
  · simp
  · rfl


end Pairing

section Core

open Module

private theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

private theorem b2z_ne (a : ZMod 2) : b2z (decide (a ≠ 0)) = a := by
  revert a
  decide

private theorem parity_sum {ι : Type} [DecidableEq ι] (S : Finset ι) (f : ι → Bool) :
    b2z (((S.filter (fun i => f i)).card % 2) == 1) = ∑ i ∈ S, b2z (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [b2z]
  | @insert i S hi ih =>
    by_cases h : f i = true
    · have h' : i ∉ S.filter (fun i => f i = true) := fun hh => hi (Finset.mem_filter.mp hh).1
      simp only [Finset.filter_insert, h, ite_true,Finset.card_insert_of_notMem h', Finset.sum_insert hi]
      rw [←ih]
      let k := (S.filter (fun i => f i = true)).card
      change b2z (((k+1)%2)==1) = 1+b2z ((k%2)==1)
      by_cases e : k%2=0
      · have e' : (k+1)%2=1 := by omega
        rw [e,e']; decide
      · have e' : (k+1)%2=0 := by omega
        have e1 : k%2=1 := by omega
        rw [e1,e']; decide
    · have h' : f i = false := Bool.eq_false_iff.mpr h
      simpa [Finset.filter_insert,h',hi,b2z] using ih

private def Fits (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) : Prop :=
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
  let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    C.gates.foldl (fun (ds : List ℕ) g =>
      ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
      (List.replicate width 0)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩

private theorem fits_iff (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (t : ℕ) :
    Fits n m q G t ↔
      ∃ blocks : (Fin q → ZMod 2) → Matrix (Fin n) (Fin m) (ZMod 2),
        (∀ j : Fin q, anchor u v (Matrix.of fun a b => b2z (G j a b)) = ∑ h, (h j) • blocks h) ∧
        (∑ h, ((blocks h).rank + 1) / 2) ≤ t :=
  main_aux n m q G u v t

private theorem mask1_sum {β : Type} [AddCommMonoid β] (g : (Fin 1 → ZMod 2) → β)
    (h0 : ∀ h, h 0 = 0 → g h = 0) : ∑ h, g h = g (fun _ => 1) := by
  apply Finset.sum_eq_single
  · intro h _ hne
    apply h0
    rcases zmod2_cases (h 0) with e | e
    · exact e
    · exfalso
      apply hne
      funext i
      rw [Fin.fin_one_eq_zero i]
      exact e
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem fits_one {n m : ℕ} (Q : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ) :
    Fits n m 1 (fun _ => Q) t ↔ (anchor u v (Matrix.of fun a b => b2z (Q a b))).rank ≤ 2 * t := by
  rw [fits_iff n m 1 _ u v t]
  constructor
  · rintro ⟨blocks, hsum, hcost⟩
    have h1 := hsum 0
    rw [mask1_sum _ (fun h e => by rw [e, zero_smul])] at h1
    have h2 := Finset.single_le_sum (f := fun h : Fin 1 → ZMod 2 => ((blocks h).rank + 1) / 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (fun _ => (1 : ZMod 2)))
    rw [h1, one_smul]
    omega
  · intro hr
    refine ⟨fun h => h 0 • anchor u v (Matrix.of fun a b => b2z (Q a b)), ?_, ?_⟩
    · intro j
      rw [Fin.fin_one_eq_zero j, mask1_sum _ (fun h e => by rw [e, zero_smul])]
      simp
    · rw [mask1_sum _ (fun h e => by
        beta_reduce
        rw [e, zero_smul, matrix_rank_zero]
        rfl)]
      beta_reduce
      rw [one_smul]
      omega

end Core

section Minors

private theorem det_one_add {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod 2)) :
    (1 + M).det = ∑ J : Finset ι,
      (M.submatrix (fun i : ↥J => i.val) (fun j : ↥J => j.val)).det := by
  have h := (Matrix.detRowAlternating (R := ZMod 2) (n := ι)).toMultilinearMap.map_add_univ M (1 : Matrix ι ι (ZMod 2))
  rw [add_comm]
  have h' : (M + 1).det = ∑ J : Finset ι, (Matrix.of (J.piecewise M (1 : Matrix ι ι (ZMod 2)))).det := h
  refine h'.trans (Finset.sum_congr rfl fun J _ => ?_)
  rw [Matrix.twoBlockTriangular_det _ (fun i => i ∈ J)]
  · have h1 : Matrix.toSquareBlockProp (Matrix.of (J.piecewise M (1 : Matrix ι ι (ZMod 2)))) (fun i => i ∈ J) =
        M.submatrix (fun i : ↥J => i.val) (fun j : ↥J => j.val) := by
      ext i j
      simp [Matrix.toSquareBlockProp, Matrix.toBlock, Finset.piecewise, i.2]
    have h2 : Matrix.toSquareBlockProp (Matrix.of (J.piecewise M (1 : Matrix ι ι (ZMod 2)))) (fun i => ¬ i ∈ J) = 1 := by
      ext i j
      simp [Matrix.toSquareBlockProp, Matrix.toBlock, Finset.piecewise, i.2, Matrix.one_apply,
        Subtype.ext_iff]
    rw [h1, h2, Matrix.det_one, mul_one]
    convert rfl
  · intro i hi j hj
    have hne : i ≠ j := fun e => hi (e ▸ hj)
    simp [Finset.piecewise, hi, hne]

private def restr {ι : Type} [DecidableEq ι] (H : Matrix ι ι (ZMod 2)) (R : Finset ι) :
    Matrix ι ι (ZMod 2) :=
  fun i j => if j ∈ R then H i j else 0

private theorem det_sub_restr {ι : Type} [DecidableEq ι] (H : Matrix ι ι (ZMod 2))
    (R J : Finset ι) :
    ((restr H R).submatrix (fun i : ↥J => i.val) (fun j : ↥J => j.val)).det =
      if J ⊆ R then (H.submatrix (fun i : ↥J => i.val) (fun j : ↥J => j.val)).det else 0 := by
  split_ifs with h
  · congr 1
    ext i j
    simp [restr, h j.2]
  · obtain ⟨j, hjJ, hjR⟩ := Finset.not_subset.mp h
    exact Matrix.det_eq_zero_of_column_eq_zero ⟨j, hjJ⟩ (fun i => by simp [restr, hjR])

private def minorSum {s : ℕ} (H : Matrix (Fin s × Fin 2) (Fin s × Fin 2) (ZMod 2))
    (U : Finset (Fin s)) : ZMod 2 :=
  ∑ J ∈ ((Finset.univ : Finset (Fin s × Fin 2)).powerset.filter
    (fun J => J.image Prod.fst = U)),
    Matrix.det (Matrix.submatrix H (fun i : ↥J => i.val) (fun j : ↥J => j.val))

private theorem minorSum_empty {s : ℕ} (H : Matrix (Fin s × Fin 2) (Fin s × Fin 2) (ZMod 2)) :
    minorSum H ∅ = 1 := by
  have hf : ((Finset.univ : Finset (Fin s × Fin 2)).powerset.filter
      (fun J => J.image Prod.fst = ∅)) = {∅} := by
    ext J
    simp [Finset.image_eq_empty]
  rw [minorSum, hf, Finset.sum_singleton]
  exact Matrix.det_isEmpty

private theorem compress {s : ℕ} (H : Matrix (Fin s × Fin 2) (Fin s × Fin 2) (ZMod 2))
    (U : Finset (Fin s)) :
    (1 + restr H (U ×ˢ (Finset.univ : Finset (Fin 2)))).det =
      ∑ U' ∈ U.powerset, minorSum H U' := by
  rw [det_one_add]
  simp only [det_sub_restr]
  rw [← Finset.sum_filter]
  have hmaps : ∀ J ∈ (Finset.univ : Finset (Finset (Fin s × Fin 2))).filter
      (fun J => J ⊆ U ×ˢ (Finset.univ : Finset (Fin 2))),
      J.image Prod.fst ∈ U.powerset := by
    intro J hJ
    rw [Finset.mem_powerset]
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_product.mp ((Finset.mem_filter.mp hJ).2 hx)).1
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun U' hU' => ?_
  rw [minorSum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext J
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset,
    Finset.subset_univ]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    intro x hx
    rw [Finset.mem_product]
    refine ⟨Finset.mem_powerset.mp hU' ?_, Finset.mem_univ _⟩
    rw [← h]
    exact Finset.mem_image_of_mem _ hx

private theorem comb {s : ℕ} (mf : Finset (Fin s) → ZMod 2) (h0 : mf ∅ = 1) :
    (∃ U : Finset (Fin s), ∑ U' ∈ U.powerset, mf U' = 0) ↔
      ∃ U : Finset (Fin s), U.Nonempty ∧ mf U ≠ 0 := by
  constructor
  · rintro ⟨U, hU⟩
    by_contra hne
    push Not at hne
    have hs : ∑ U' ∈ U.powerset, mf U' = mf ∅ :=
      Finset.sum_eq_single ∅
        (fun U' _ hU' => hne U' (Finset.nonempty_iff_ne_empty.mpr hU'))
        (fun h => absurd (Finset.empty_mem_powerset U) h)
    rw [hs, h0] at hU
    exact one_ne_zero hU
  · intro hex
    have hex' : ∃ c : ℕ, ∃ U : Finset (Fin s), U.Nonempty ∧ mf U ≠ 0 ∧ U.card = c := by
      obtain ⟨U, h1, h2⟩ := hex
      exact ⟨U.card, U, h1, h2, rfl⟩
    classical
    obtain ⟨U, hne, hU, hc⟩ := Nat.find_spec hex'
    have hmin := fun c (hlt : c < Nat.find hex') => Nat.find_min hex' hlt
    refine ⟨U, ?_⟩
    have hUe : (∅ : Finset (Fin s)) ≠ U := fun e => Finset.not_nonempty_empty (e ▸ hne)
    rw [Finset.sum_eq_add_of_mem ∅ U (Finset.empty_mem_powerset U)
      (Finset.mem_powerset.mpr (Finset.Subset.refl U)) hUe]
    · rw [h0]
      rcases zmod2_cases (mf U) with e | e
      · exact absurd e hU
      · rw [e]
        decide
    · intro c hcU hcne
      by_contra hmc
      have hsub : c ⊆ U := Finset.mem_powerset.mp hcU
      have hlt : c.card < U.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hcne.2⟩)
      exact hmin c.card (hc ▸ hlt)
        ⟨c, Finset.nonempty_iff_ne_empty.mpr hcne.1, hmc, rfl⟩

end Minors

section Singular

open Module

variable {K : Type} [Field K] [Algebra (ZMod 2) K] {k : ℕ}

private noncomputable def Lmap {ι : Type} (z : K) (u : ι → K) (f : ι → (K →ₗ[ZMod 2] ZMod 2))
    (R : Finset ι) : K →ₗ[ZMod 2] K :=
  LinearMap.mulLeft (ZMod 2) z + ∑ j ∈ R, (f j).smulRight (u j)

private theorem Lmap_apply {ι : Type} (z : K) (u : ι → K) (f : ι → (K →ₗ[ZMod 2] ZMod 2))
    (R : Finset ι) (b : K) : Lmap z u f R b = z * b + ∑ j ∈ R, f j b • u j := by
  simp [Lmap, LinearMap.sum_apply]

private theorem Lmap_entry {ι : Type} (bit : K →ₗ[ZMod 2] ZMod 2) (z : K) (u : ι → K)
    (f : ι → (K →ₗ[ZMod 2] ZMod 2)) (R : Finset ι) (x y : K) :
    bit (x * Lmap z u f R y) = bit (z * x * y) + ∑ j ∈ R, bit (u j * x) * f j y := by
  rw [Lmap_apply, mul_add, map_add, Finset.mul_sum, map_sum]
  congr 1
  · congr 1
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm x, mul_comm]

private theorem char_two (x : K) : x + x = 0 := by
  have h : (1 + 1 : ZMod 2) • x = 0 := by
    rw [show (1 + 1 : ZMod 2) = 0 from by decide, zero_smul]
  simpa [add_smul] using h

private theorem sing_iff {ι : Type} [Fintype ι] [DecidableEq ι] (z : K) (hz : z ≠ 0)
    (u : ι → K) (f : ι → (K →ₗ[ZMod 2] ZMod 2)) (R : Finset ι) :
    (∃ b : K, b ≠ 0 ∧ Lmap z u f R b = 0) ↔
      (1 + restr (Matrix.of fun i j => f i (z⁻¹ * u j)) R).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  have hmv : ∀ (v : ι → ZMod 2) (i : ι),
      ((1 + restr (Matrix.of fun i j => f i (z⁻¹ * u j)) R).mulVec v) i =
        v i + ∑ j ∈ R, f i (z⁻¹ * u j) * v j := by
    intro v i
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, restr, Matrix.of_apply, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  constructor
  · rintro ⟨b, hb, hL⟩
    refine ⟨fun j => f j b, ?_, ?_⟩
    · intro hv
      apply hb
      have hv' : ∀ j, f j b = 0 := congrFun hv
      rw [Lmap_apply] at hL
      simp only [hv', zero_smul, Finset.sum_const_zero, add_zero] at hL
      exact (mul_eq_zero.mp hL).resolve_left hz
    · funext i
      rw [hmv]
      have hh : f i (z⁻¹ * Lmap z u f R b) = f i b + ∑ j ∈ R, f i (z⁻¹ * u j) * f j b := by
        rw [Lmap_apply, mul_add, ← mul_assoc, inv_mul_cancel₀ hz, one_mul, map_add,
          Finset.mul_sum, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
      rw [← hh, hL, mul_zero, map_zero]
      rfl
  · rintro ⟨v, hv, hmul⟩
    have hfix : ∀ i, ∑ j ∈ R, f i (z⁻¹ * u j) * v j = v i := by
      intro i
      have h1 := congrFun hmul i
      rw [hmv] at h1
      have h2 := zmod2_add_self (v i)
      have h3 : (0 : ι → ZMod 2) i = 0 := rfl
      rw [h3] at h1
      linear_combination h1 - h2
    have hfb : ∀ i, f i (∑ j ∈ R, v j • (z⁻¹ * u j)) = v i := by
      intro i
      simp only [map_sum, map_smul, smul_eq_mul]
      rw [← hfix i]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    refine ⟨∑ j ∈ R, v j • (z⁻¹ * u j), ?_, ?_⟩
    · intro hb0
      apply hv
      funext i
      rw [← hfb i, hb0, map_zero]
      rfl
    · rw [Lmap_apply]
      simp only [hfb]
      have hzb : z * ∑ j ∈ R, v j • (z⁻¹ * u j) = ∑ j ∈ R, v j • u j := by
        simp only [Finset.mul_sum, mul_smul_comm, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
      rw [hzb]
      exact char_two _

private theorem rank_iff (basis : Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2)
    (hbit : bit ≠ 0) (odd : k % 2 = 1) (L : K →ₗ[ZMod 2] K) :
    (pairAnchor (pairMatrix basis bit L)).rank ≤ 2 * (k / 2) ↔ ∃ b : K, b ≠ 0 ∧ L b = 0 := by
  rw [rank_pairAnchor_pairMatrix basis bit hbit L]
  have : FiniteDimensional (ZMod 2) K := basis.finiteDimensional_of_finite
  have dims := L.finrank_range_add_finrank_ker
  rw [Module.finrank_eq_card_basis basis, Fintype.card_fin] at dims
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hker : LinearMap.ker L = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      by_contra hx0
      exact hne x hx0 (LinearMap.mem_ker.mp hx)
    rw [hker, finrank_bot] at dims
    omega
  · rintro ⟨x, hx, h0⟩
    have : Nontrivial (LinearMap.ker L) :=
      ⟨⟨⟨x, LinearMap.mem_ker.mpr h0⟩, 0, fun e => hx (congrArg Subtype.val e)⟩⟩
    have kerpos : 0 < finrank (ZMod 2) (LinearMap.ker L) := Module.finrank_pos
    omega

end Singular

section Pieces

private theorem pair_sum {β : Type} [AddCommMonoid β] (D : ℕ → β) (N : ℕ) :
    ∑ x : Fin N, (D (2 * x.val) + D (2 * x.val + 1)) = ∑ j ∈ Finset.range (2 * N), D j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_castSucc, show 2 * (N + 1) = 2 * N + 1 + 1 from by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, ← ih, add_assoc]
    rfl

private theorem split {M : Type} [Fintype M] [DecidableEq M] {n m s : ℕ}
    (blocks : M → Matrix (Fin n) (Fin m) (ZMod 2))
    (hcost : ∑ h, ((blocks h).rank + 1) / 2 ≤ s) :
    ∃ (α : Fin s × Fin 2 → Fin n → ZMod 2) (β : Fin s × Fin 2 → Fin m → ZMod 2),
      ∀ Hs : Finset M, ∃ U : Finset (Fin s),
        ∑ h ∈ Hs, blocks h =
          ∑ j ∈ U ×ˢ (Finset.univ : Finset (Fin 2)), Matrix.vecMulVec (α j) (β j) := by
  classical
  choose ra rb hrab using fun h => matrix_rank_decomp (blocks h)
  have hcard : Fintype.card (Σ h : M, Fin (((blocks h).rank + 1) / 2)) ≤ Fintype.card (Fin s) := by
    simpa using hcost
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let getA : M → ℕ → Fin n → ZMod 2 := fun h j =>
    if hj : j < (blocks h).rank then ra h ⟨j, hj⟩ else 0
  let getB : M → ℕ → Fin m → ZMod 2 := fun h j =>
    if hj : j < (blocks h).rank then rb h ⟨j, hj⟩ else 0
  let g : Fin s → Option (Σ h : M, Fin (((blocks h).rank + 1) / 2)) := fun i =>
    if hx : ∃ x, e x = i then some (Classical.choose hx) else none
  have hg : ∀ x, g (e x) = some x := by
    intro x
    have hx : ∃ y, e y = e x := ⟨x, rfl⟩
    simp only [g, dite_eq_left hx]
    exact congrArg some (e.injective (Classical.choose_spec hx))
  let α : Fin s × Fin 2 → Fin n → ZMod 2 := fun j =>
    (g j.1).elim 0 (fun x => getA x.1 (2 * x.2.val + j.2.val))
  let β : Fin s × Fin 2 → Fin m → ZMod 2 := fun j =>
    (g j.1).elim 0 (fun x => getB x.1 (2 * x.2.val + j.2.val))
  have hα : ∀ x c, α (e x, c) = getA x.1 (2 * x.2.val + c.val) := by
    intro x c
    simp only [α, hg]
    rfl
  have hβ : ∀ x c, β (e x, c) = getB x.1 (2 * x.2.val + c.val) := by
    intro x c
    simp only [β, hg]
    rfl
  refine ⟨α, β, fun Hs => ⟨(Hs.sigma (fun _ => Finset.univ)).map e, ?_⟩⟩
  rw [Finset.sum_product, Finset.sum_map, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [hα, hβ, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, add_zero]
  rw [pair_sum (fun j => Matrix.vecMulVec (getA h j) (getB h j))]
  have hsub : Finset.range (blocks h).rank ⊆ Finset.range (2 * (((blocks h).rank + 1) / 2)) := by
    intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_range]
    conv_lhs => rw [hrab h]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [getA, getB, dite_eq_left j.2]
  · intro j _ hj
    have hj' : ¬ j < (blocks h).rank := fun h' => hj (Finset.mem_range.mpr h')
    simp only [getA, dite_eq_right hj']
    ext a b
    simp [Matrix.vecMulVec_apply]

private theorem single_eq {s : ℕ} (i i0 : Fin s) :
    (Pi.single i0 1 : Fin s → ZMod 2) = Pi.single i 1 ↔ i = i0 := by
  constructor
  · intro h
    by_contra hne
    have h1 := congrFun h i0
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (fun e => hne e.symm)] at h1
    exact one_ne_zero h1
  · intro h
    rw [h]

private theorem pieces_fit {n m s : ℕ} (u : Fin n) (v : Fin m)
    (P : Fin s → Matrix (Fin n) (Fin m) (ZMod 2)) (hr : ∀ i, (P i).rank ≤ 2)
    (hu : ∀ i y, P i u y = 0) (hv : ∀ i x, P i x v = 0) :
    Fits n m s (fun i x y => decide (P i x y ≠ 0)) s := by
  classical
  rw [fits_iff n m s _ u v s]
  refine ⟨fun h => ∑ i, if h = Pi.single i 1 then P i else 0, ?_, ?_⟩
  · intro j
    have hanch : anchor u v (Matrix.of fun a b => b2z (decide (P j a b ≠ 0))) = P j := by
      ext a b
      simp only [anchor, Matrix.of_apply, b2z_ne, hu, hv, add_zero]
    rw [hanch]
    simp only [Finset.smul_sum, smul_ite, smul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp [Pi.single_apply, ite_smul]
  · have hper : ∀ h : Fin s → ZMod 2,
        ((∑ i, if h = Pi.single i 1 then P i else 0).rank + 1) / 2 ≤
          ∑ i : Fin s, if h = Pi.single i 1 then 1 else 0 := by
      intro h
      by_cases hh : ∃ i0, h = Pi.single i0 1
      · obtain ⟨i0, rfl⟩ := hh
        have hb : (∑ i, if (Pi.single i0 1 : Fin s → ZMod 2) = Pi.single i 1 then P i else 0)
            = P i0 := by
          simp only [single_eq]
          simp
        rw [hb]
        have h1 : (if (Pi.single i0 1 : Fin s → ZMod 2) = Pi.single i0 1 then 1 else 0) ≤
            ∑ i : Fin s, if (Pi.single i0 1 : Fin s → ZMod 2) = Pi.single i 1 then 1 else 0 :=
          Finset.single_le_sum (f := fun i : Fin s =>
            if (Pi.single i0 1 : Fin s → ZMod 2) = Pi.single i 1 then 1 else 0)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i0)
        rw [ite_eq_left rfl] at h1
        have h2 := hr i0
        omega
      · push Not at hh
        have hb : (∑ i, if h = Pi.single i 1 then P i else 0) = 0 :=
          Finset.sum_eq_zero fun i _ => ite_eq_right (hh i)
        rw [hb, matrix_rank_zero]
        exact Nat.zero_le _
    refine (Finset.sum_le_sum fun h _ => hper h).trans ?_
    rw [Finset.sum_comm]
    simp

end Pieces

section Assembly

open Module

variable {K : Type} [Field K] [Algebra (ZMod 2) K] {k : ℕ}

private noncomputable def pt (basis : Basis (Fin k) (ZMod 2) K) : Fin (k + 1) → K := Fin.cases 0 basis

private noncomputable def resid {g : ℕ} (basis : Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2)
    (T : Fin g → Fin (k + 1) → Fin (k + 1) → Bool) (S : Finset (Fin g)) (z : K)
    (x y : Fin (k + 1)) : Bool :=
  xor (decide (bit (z * pt basis x * pt basis y) ≠ 0))
    (((S.filter (fun i => T i x y)).card % 2) == 1)

private theorem anchor_sum {ι : Type} {n m : ℕ} (u : Fin n) (v : Fin m) (S : Finset ι)
    (A : ι → Matrix (Fin n) (Fin m) (ZMod 2)) :
    anchor u v (∑ i ∈ S, A i) = ∑ i ∈ S, anchor u v (A i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [anchor_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, anchor_add, ih]

private theorem anchor_row {n m : ℕ} (u : Fin n) (v : Fin m)
    (A : Matrix (Fin n) (Fin m) (ZMod 2)) (y : Fin m) : anchor u v A u y = 0 := by
  have h := zmod2_add_self (A u y + A u v)
  simp only [anchor]
  rw [← h]
  ring

private theorem anchor_col {n m : ℕ} (u : Fin n) (v : Fin m)
    (A : Matrix (Fin n) (Fin m) (ZMod 2)) (x : Fin n) : anchor u v A x v = 0 := by
  have h := zmod2_add_self (A x v + A u v)
  simp only [anchor]
  rw [← h]
  ring

private theorem resid_matrix {g : ℕ} (basis : Basis (Fin k) (ZMod 2) K)
    (bit : K →ₗ[ZMod 2] ZMod 2) (T : Fin g → Fin (k + 1) → Fin (k + 1) → Bool)
    (S : Finset (Fin g)) (z : K) :
    anchor 0 0 (Matrix.of fun a b => b2z (resid basis bit T S z a b)) =
      (Matrix.of fun x y => bit (z * pt basis x * pt basis y)) +
        ∑ i ∈ S, anchor 0 0 (Matrix.of fun a b => b2z (T i a b)) := by
  have h1 : (Matrix.of fun a b => b2z (resid basis bit T S z a b)) =
      (Matrix.of fun x y => bit (z * pt basis x * pt basis y)) +
        ∑ i ∈ S, (Matrix.of fun a b => b2z (T i a b)) := by
    ext a b
    simp only [resid, b2z_xor, b2z_ne, parity_sum, Matrix.add_apply, Matrix.sum_apply,
      Matrix.of_apply]
  have h2 : anchor 0 0 (Matrix.of fun x y => bit (z * pt basis x * pt basis y)) =
      (Matrix.of fun x y => bit (z * pt basis x * pt basis y)) := by
    ext a b
    simp [anchor, pt]
  rw [h1, anchor_add, anchor_sum, h2]

private theorem forward (basis : Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2)
    (hbit : bit ≠ 0) (odd : k % 2 = 1) (s : ℕ) (Z : Finset K) (hZ : (0 : K) ∉ Z)
    (hex : ∃ (p : ℕ) (T : Fin p → Fin (k + 1) → Fin (k + 1) → Bool),
      Fits (k + 1) (k + 1) p T s ∧ ∀ z ∈ Z, ∃ S : Finset (Fin p),
        Fits (k + 1) (k + 1) 1 (fun _ => resid basis bit T S z) (k / 2)) :
    ∃ (u : Fin s × Fin 2 → K) (f : Fin s × Fin 2 → (K →ₗ[ZMod 2] ZMod 2)),
      ∀ z ∈ Z, ∃ U : Finset (Fin s), U.Nonempty ∧
        minorSum (Matrix.of fun i j => f i (z⁻¹ * u j)) U ≠ 0 := by
  obtain ⟨p, T, hT, hres⟩ := hex
  obtain ⟨blocks, hsum, hcost⟩ := (fits_iff _ _ p T 0 0 s).mp hT
  obtain ⟨α, β, hsplit⟩ := split blocks hcost
  let u : Fin s × Fin 2 → K := fun j => (pairEquiv basis bit hbit).symm (fun x => α j x.succ)
  let f : Fin s × Fin 2 → (K →ₗ[ZMod 2] ZMod 2) := fun j =>
    basis.constr (ZMod 2) (fun y => β j y.succ)
  have hu : ∀ j x, bit (u j * basis x) = α j x.succ := by
    intro j x
    have h := congrFun ((pairEquiv basis bit hbit).apply_symm_apply (fun x => α j x.succ)) x
    rw [mul_comm]
    exact h
  have hf : ∀ j y, f j (basis y) = β j y.succ := by
    intro j y
    simp [f]
  refine ⟨u, f, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := fun h => hZ (h ▸ hz)
  obtain ⟨S, hS⟩ := hres z hz
  have hrank := (fits_one _ 0 0 (k / 2)).mp hS
  obtain ⟨U, hU⟩ := hsplit (Finset.univ.filter (fun h => ∑ i ∈ S, h i = 1))
  have hA : anchor 0 0 (Matrix.of fun a b => b2z (resid basis bit T S z a b)) =
      (Matrix.of fun x y => bit (z * pt basis x * pt basis y)) +
        ∑ j ∈ U ×ˢ (Finset.univ : Finset (Fin 2)), Matrix.vecMulVec (α j) (β j) := by
    rw [resid_matrix, ← hU]
    congr 1
    simp only [hsum]
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [← Finset.sum_smul]
    rcases zmod2_cases (∑ i ∈ S, h i) with e | e <;> simp [e]
  have hmat : anchor 0 0 (Matrix.of fun a b => b2z (resid basis bit T S z a b)) =
      pairAnchor (pairMatrix basis bit (Lmap z u f (U ×ˢ (Finset.univ : Finset (Fin 2))))) := by
    ext x y
    refine Fin.cases ?_ (fun x => Fin.cases ?_ (fun y => ?_) y) x
    · rw [anchor_row]
      rfl
    · rw [anchor_col, pairAnchor_zero_right]
    · rw [hA, pairAnchor_succ_succ, pairMatrix, Lmap_entry]
      simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.of_apply, Matrix.vecMulVec_apply,
        hu, hf, pt, Fin.cases_succ]
  rw [hmat, rank_iff basis bit hbit odd, sing_iff z hz0] at hrank
  rw [compress] at hrank
  exact (comb _ (minorSum_empty _)).mp ⟨U, hrank⟩

private theorem backward (basis : Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2)
    (hbit : bit ≠ 0) (odd : k % 2 = 1) (s : ℕ) (Z : Finset K) (hZ : (0 : K) ∉ Z)
    (hex : ∃ (u : Fin s × Fin 2 → K) (f : Fin s × Fin 2 → (K →ₗ[ZMod 2] ZMod 2)),
      ∀ z ∈ Z, ∃ U : Finset (Fin s), U.Nonempty ∧
        minorSum (Matrix.of fun i j => f i (z⁻¹ * u j)) U ≠ 0) :
    ∃ (p : ℕ) (T : Fin p → Fin (k + 1) → Fin (k + 1) → Bool),
      Fits (k + 1) (k + 1) p T s ∧ ∀ z ∈ Z, ∃ S : Finset (Fin p),
        Fits (k + 1) (k + 1) 1 (fun _ => resid basis bit T S z) (k / 2) := by
  obtain ⟨u, f, hyp⟩ := hex
  let P : Fin s → Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2) := fun i =>
    ∑ c : Fin 2, Matrix.vecMulVec (fun x => bit (u (i, c) * pt basis x))
      (fun y => f (i, c) (pt basis y))
  have hP0 : ∀ i y, P i 0 y = 0 := by
    intro i y
    simp [P, Matrix.vecMulVec_apply, pt]
  have hP0' : ∀ i x, P i x 0 = 0 := by
    intro i x
    simp [P, Matrix.vecMulVec_apply, pt]
  have hPr : ∀ i, (P i).rank ≤ 2 := by
    intro i
    refine (matrix_rank_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun c _ => Matrix.rank_vecMulVec_le _ _).trans ?_
    simp
  refine ⟨s, fun i x y => decide (P i x y ≠ 0), pieces_fit 0 0 P hPr hP0 hP0', fun z hz => ?_⟩
  have hz0 : z ≠ 0 := fun h => hZ (h ▸ hz)
  obtain ⟨U, hU⟩ := (comb _ (minorSum_empty (Matrix.of fun i j => f i (z⁻¹ * u j)))).mpr (hyp z hz)
  rw [← compress, ← sing_iff z hz0, ← rank_iff basis bit hbit odd] at hU
  refine ⟨U, (fits_one _ 0 0 (k / 2)).mpr ?_⟩
  have hmat : anchor 0 0 (Matrix.of fun a b =>
      b2z (resid basis bit (fun i x y => decide (P i x y ≠ 0)) U z a b)) =
      pairAnchor (pairMatrix basis bit (Lmap z u f (U ×ˢ (Finset.univ : Finset (Fin 2))))) := by
    have hanch : ∀ i, anchor 0 0 (Matrix.of fun a b => b2z (decide (P i a b ≠ 0))) = P i := by
      intro i
      ext a b
      simp only [anchor, Matrix.of_apply, b2z_ne, hP0, hP0', add_zero]
    rw [resid_matrix]
    simp only [hanch]
    ext x y
    rw [pairAnchor_pairMatrix_apply, Lmap_entry, Finset.sum_product]
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.of_apply, Matrix.vecMulVec_apply, P, pt]
  rw [hmat]
  exact hU

private theorem final (basis : Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2)
    (hbit : bit ≠ 0) (odd : k % 2 = 1) (s : ℕ) (Z : Finset K) (hZ : (0 : K) ∉ Z) :
    (∃ (p : ℕ) (T : Fin p → Fin (k + 1) → Fin (k + 1) → Bool),
      Fits (k + 1) (k + 1) p T s ∧ ∀ z ∈ Z, ∃ S : Finset (Fin p),
        Fits (k + 1) (k + 1) 1 (fun _ => resid basis bit T S z) (k / 2)) ↔
    ∃ (u : Fin s × Fin 2 → K) (f : Fin s × Fin 2 → (K →ₗ[ZMod 2] ZMod 2)),
      ∀ z ∈ Z, ∃ U : Finset (Fin s), U.Nonempty ∧
        minorSum (Matrix.of fun i j => f i (z⁻¹ * u j)) U ≠ 0 :=
  ⟨forward basis bit hbit odd s Z hZ, backward basis bit hbit odd s Z hZ⟩

end Assembly

end PEqualNP.Outside.L_meta_29768

theorem PEqualNP.Outside.L_meta_29768 : (
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

let F := ZMod 2
∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
    (k : ℕ) (basis : Module.Basis (Fin k) F K) (bit : K →ₗ[F] F), bit ≠ 0 →
  let n := k+1
  let point : Fin n → K := Fin.cases 0 basis
  let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
  let residual := fun {g : ℕ} (T : Fin g → Fin n → Fin n → Bool) (S : Finset (Fin g))
      (z : K) (x y : Fin n) => xor (mult z x y) (((S.filter (fun i => T i x y)).card % 2) == 1)

  k % 2 = 1 → ∀ (s : ℕ) (Z : Finset K), (0 : K) ∉ Z →
    ((∃ (p : ℕ) (T : Fin p → Fin n → Fin n → Bool),
      fits n n p T s ∧ ∀ z ∈ Z, ∃ S : Finset (Fin p),
        fits n n 1 (fun _ => residual T S z) (k/2)) ↔
    ∃ (u : Fin s × Fin 2 → K) (f : Fin s × Fin 2 → (K →ₗ[F] F)),
      ∀ z ∈ Z,
        let H : Matrix (Fin s × Fin 2) (Fin s × Fin 2) F := fun i j => f i (z⁻¹ * u j)
        let sub := fun (J : Finset (Fin s × Fin 2)) =>
          Matrix.submatrix H (fun i : ↥J => i.val) (fun j : ↥J => j.val)
        ∃ U : Finset (Fin s), U.Nonempty ∧
          (∑ J ∈ ((Finset.univ : Finset (Fin s × Fin 2)).powerset.filter
            (fun J => J.image Prod.fst = U)), Matrix.det (sub J)) ≠ 0)
) := by
  intro nonlinear depths fits F K _ _ _ k basis bit hbit n point mult residual odd s Z hZ
  exact PEqualNP.Outside.L_meta_29768.final basis bit hbit odd s Z hZ
