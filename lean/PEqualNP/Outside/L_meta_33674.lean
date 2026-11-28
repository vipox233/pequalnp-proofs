import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33674

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depths (width : ℕ) (C : Circuit) : List ℕ :=
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> revert h <;> decide

private lemma zmod2_add_self (t : ZMod 2) : t + t = 0 := by
  revert t
  decide

private lemma zmod2_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t
  decide

private lemma b2z_decide_eq_one (t : ZMod 2) : b2z (decide (t = 1)) = t := by
  revert t
  decide

private lemma gate_eval_one_affine (op : GateOp) :
    ∃ c0 c1 : ZMod 2, ∀ x : Bool, b2z (op.eval [x]) = c0 + c1 * b2z x := by
  refine ⟨b2z (op.eval [false]), b2z (op.eval [true]) + b2z (op.eval [false]), fun x => ?_⟩
  cases x
  · simp [b2z]
  · simp only [b2z, ↓reduceIte, mul_one]
    generalize op.eval [false] = a
    generalize op.eval [true] = b
    cases a <;> cases b <;> decide

private lemma gate_eval_two_poly (op : GateOp) :
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

private lemma foldr_max_le_iff (l : List ℕ) (k : ℕ) :
    l.foldr max 0 ≤ k ↔ ∀ a ∈ l, a ≤ k := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, max_le_iff, List.mem_cons, forall_eq_or_imp, ih]

private lemma mem_le_foldr_max {l : List ℕ} {a : ℕ} (ha : a ∈ l) :
    a ≤ l.foldr max 0 :=
  (foldr_max_le_iff l (l.foldr max 0)).1 (le_refl _) a ha

private def runFold {α : Type} (step : List α → Gate → α) (init : List α) (gs : List Gate) : List α :=
  gs.foldl (fun l g => l ++ [step l g]) init

private lemma runFold_length {α : Type} (step : List α → Gate → α) (init : List α) (gs : List Gate) :
    (runFold step init gs).length = init.length + gs.length := by
  unfold runFold
  induction gs generalizing init with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma runFold_append {α : Type} (step : List α → Gate → α) (init : List α)
    (gs1 gs2 : List Gate) :
    runFold step init (gs1 ++ gs2) = runFold step (runFold step init gs1) gs2 := by
  unfold runFold
  exact List.foldl_append

private lemma getD_append_left {α : Type} (l1 l2 : List α) (i : ℕ) (d0 : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d0 = l1.getD i d0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_of_ge {α : Type} (l : List α) (i : ℕ) (d0 : α) (hi : l.length ≤ i) :
    l.getD i d0 = d0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

private lemma runFold_getD_prefix {α : Type} (step : List α → Gate → α) (init : List α)
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

private lemma runFold_getD_gate {α : Type} (step : List α → Gate → α) (init : List α)
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

private lemma wires_eq_runFold (C : Circuit) (x : List Bool) :
    C.wires x = runFold (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) x C.gates :=
  rfl

private lemma depths_eq_runFold (width : ℕ) (C : Circuit) :
    depths width C = runFold (fun ds g =>
      (g.inputs.map fun a => ds.getD a 0).foldr max 0 + (nonlinear g).toNat)
      (List.replicate width 0) C.gates :=
  rfl

private lemma oneEach_length {n m : ℕ} (a : Fin n) (b : Fin m) :
    (oneEach a b).length = n + m := by
  simp [oneEach]

private lemma oneEach_getD_left {n m : ℕ} (a : Fin n) (b : Fin m) (w : ℕ) (hw : w < n) :
    (oneEach a b).getD w false = decide ((⟨w, hw⟩ : Fin n) = a) := by
  unfold oneEach
  rw [getD_append_left _ _ _ _ (by simp [hw])]
  simp [List.getD_eq_getElem?_getD, hw]

private lemma oneEach_getD_right {n m : ℕ} (a : Fin n) (b : Fin m) (w : ℕ)
    (hlo : n ≤ w) (hhi : w < n + m) :
    (oneEach a b).getD w false = decide ((⟨w - n, by omega⟩ : Fin m) = b) := by
  unfold oneEach
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [hlo])]
  simp only [List.length_ofFn]
  have hlt : w - n < m := by omega
  simp [hlt]

private lemma gateAt_eq_getElem (C : Circuit) (idx : ℕ) (hidx : idx < C.gates.length) :
    gateAt C idx = C.gates[idx] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hidx]

private lemma wires_getD_gate {n m : ℕ} (C : Circuit) (hRB : ReadsBack (n + m) C)
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

private lemma depths_getD_gate {n m : ℕ} (C : Circuit) (hRB : ReadsBack (n + m) C)
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

private lemma depths_getD_input (width : ℕ) (C : Circuit) (w : ℕ) (hw : w < width) :
    (depths width C).getD w 0 = 0 := by
  rw [depths_eq_runFold, runFold_getD_prefix _ _ _ w 0 (by simp [hw])]
  simp [List.getD_eq_getElem?_getD, hw]

private lemma depths_getD_oob (width : ℕ) (C : Circuit) (w : ℕ) (hw : width + C.gates.length ≤ w) :
    (depths width C).getD w 0 = 0 := by
  rw [depths_eq_runFold, getD_of_ge _ w 0]
  rw [runFold_length, List.length_replicate]
  exact hw

private lemma matrix_rank_zero {n m : ℕ} :
    (0 : Matrix (Fin n) (Fin m) (ZMod 2)).rank = 0 := by
  simp [Matrix.rank]

private lemma matrix_rank_add_le {n m : ℕ} (A B : Matrix (Fin n) (Fin m) (ZMod 2)) :
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

private def anchor {n m : ℕ} (u : Fin n) (v : Fin m)
    (M : Matrix (Fin n) (Fin m) (ZMod 2)) : Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun a b => M a b + M a v + M u b + M u v

private lemma anchor_zero {n m : ℕ} (u : Fin n) (v : Fin m) :
    anchor u v (0 : Matrix (Fin n) (Fin m) (ZMod 2)) = 0 := by
  ext a b; simp [anchor]

private lemma anchor_add {n m : ℕ} (u : Fin n) (v : Fin m)
    (A B : Matrix (Fin n) (Fin m) (ZMod 2)) :
    anchor u v (A + B) = anchor u v A + anchor u v B := by
  ext a b; simp only [anchor, Matrix.add_apply]; ring

private lemma anchor_smul {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2)
    (A : Matrix (Fin n) (Fin m) (ZMod 2)) :
    anchor u v (c • A) = c • anchor u v A := by
  ext a b; simp only [anchor, Matrix.smul_apply, smul_eq_mul]; ring

private def IsSep {n m : ℕ} (M : Matrix (Fin n) (Fin m) (ZMod 2)) : Prop :=
  ∃ (α : Fin n → ZMod 2) (β : Fin m → ZMod 2), ∀ a b, M a b = α a + β b

private lemma anchor_of_isSep {n m : ℕ} (u : Fin n) (v : Fin m)
    {M : Matrix (Fin n) (Fin m) (ZMod 2)} (hM : IsSep M) :
    anchor u v M = 0 := by
  obtain ⟨α, β, h⟩ := hM
  ext a b
  simp only [anchor, h, Matrix.zero_apply]
  calc α a + β b + (α a + β v) + (α u + β b) + (α u + β v)
      = (α a + α a) + (α u + α u) + (β b + β b) + (β v + β v) := by ring
    _ = 0 := by simp [zmod2_add_self]

private lemma isSep_const {n m : ℕ} (c : ZMod 2) :
    IsSep (Matrix.of (fun (_ : Fin n) (_ : Fin m) => c)) :=
  ⟨fun _ => c, fun _ => 0, fun _ _ => by simp⟩

private lemma isSep_add {n m : ℕ} {A B : Matrix (Fin n) (Fin m) (ZMod 2)}
    (hA : IsSep A) (hB : IsSep B) : IsSep (A + B) := by
  obtain ⟨α1, β1, h1⟩ := hA
  obtain ⟨α2, β2, h2⟩ := hB
  refine ⟨fun a => α1 a + α2 a, fun b => β1 b + β2 b, fun a b => ?_⟩
  simp only [Matrix.add_apply, h1, h2]
  ring

private lemma isSep_smul {n m : ℕ} (c : ZMod 2) {A : Matrix (Fin n) (Fin m) (ZMod 2)}
    (hA : IsSep A) : IsSep (c • A) := by
  obtain ⟨α, β, h⟩ := hA
  refine ⟨fun a => c * α a, fun b => c * β b, fun a b => ?_⟩
  simp only [Matrix.smul_apply, smul_eq_mul, h]
  ring

private lemma anchor_vecMulVec_rank_le_one {n m : ℕ} (u : Fin n) (v : Fin m)
    (α : Fin n → ZMod 2) (β : Fin m → ZMod 2) :
    (anchor u v (Matrix.vecMulVec α β)).rank ≤ 1 := by
  have heq : anchor u v (Matrix.vecMulVec α β) =
      Matrix.vecMulVec (fun a => α a + α u) (fun b => β b + β v) := by
    ext a b
    simp only [anchor, Matrix.vecMulVec_apply]
    ring
  rw [heq]
  exact Matrix.rank_vecMulVec_le _ _


def liveSet (C : Circuit) : Finset (Fin C.gates.length) :=
  Finset.univ.filter (fun j => nonlinear (C.gates.get j))

def shallowSet (width : ℕ) (C : Circuit) : Finset (Fin C.gates.length) :=
  Finset.univ.filter (fun j => nonlinear (C.gates.get j) = true ∧
    (depths width C).getD (width + j.val) 0 = 1)

private def wireMat {n m : ℕ} (C : Circuit) (w : ℕ) : Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun a b => b2z ((C.wires (oneEach a b)).getD w false)

private lemma actualForward {n m : ℕ} (u : Fin n) (v : Fin m) (C : Circuit)
    (hRB : ReadsBack (n+m) C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (∀ j ∈ shallowSet (n+m) C, (anchor u v (wireMat C (n+m+j.val))).rank ≤ 2) ∧
    ∀ w : ℕ, (depths (n+m) C).getD w 0 ≤ 1 → ∃ c : Fin C.gates.length → ZMod 2,
      anchor u v (wireMat C w) =
        ∑ j ∈ shallowSet (n+m) C, c j • anchor u v (wireMat C (n+m+j.val)) := by
  let F := ZMod 2
  let Mat := Matrix (Fin n) (Fin m) F
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
  exact ⟨hMgate_rank, hdep1_span⟩

noncomputable def targetTable {I : Type} [Fintype I] (K : Matrix I I (ZMod 2))
    (x y : Fin (Fintype.card I + 1)) : Bool :=
  Fin.cases false (fun i => Fin.cases false (fun j =>
    decide (K ((Fintype.equivFin I).symm i) ((Fintype.equivFin I).symm j) ≠ 0)) y) x

noncomputable def actualR (I : Type) [Fintype I] (C : Circuit) (j : Fin C.gates.length) :
    Matrix I I (ZMod 2) := fun x y =>
  let w := Fintype.card I
  let val := fun (r c : Fin (w+1)) =>
    (⟨C.gates, (w+1)+(w+1)+j.val⟩ : Circuit).eval (oneEach r c)
  let e := Fintype.equivFin I
  if xor (xor (val (e x).succ (e y).succ) (val (e x).succ 0))
      (xor (val 0 (e y).succ) (val 0 0)) then 1 else 0

private lemma b2z_xor (x y : Bool) : b2z (xor x y) = b2z x + b2z y := by
  cases x <;> cases y <;> decide

private lemma b2z_decide (c : ZMod 2) [Decidable (c ≠ 0)] : b2z (decide (c ≠ 0)) = c := by
  rcases zmod2_cases c with rfl | rfl <;> simp [b2z]

lemma extractActual {I Z : Type} [Fintype I] (K : Z → Matrix I I (ZMod 2))
    (C : Circuit) (tap : Z → ℕ)
    (hRB : ReadsBack ((Fintype.card I+1)+(Fintype.card I+1)) C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (htap : ∀ z, (depths ((Fintype.card I+1)+(Fintype.card I+1)) C).getD (tap z) 0 ≤ 1 ∧
      Represents (targetTable (K z)) ⟨C.gates, tap z⟩) :
    ∃ D : Finset (Fin C.gates.length), D ⊆ liveSet C ∧
      (∀ j ∈ D, (actualR I C j).rank ≤ 2) ∧
      ∀ z, ∃ c : Fin C.gates.length → ZMod 2, K z = ∑ j ∈ D, c j • actualR I C j := by
  classical
  let n := Fintype.card I + 1
  let idx : I → Fin n := fun i => (Fintype.equivFin I i).succ
  let A (w : ℕ) := anchor (0 : Fin n) (0 : Fin n) (wireMat C w)
  obtain ⟨hr, hspan⟩ := actualForward (0 : Fin n) (0 : Fin n) C hRB hfan
  have hR (j : Fin C.gates.length) :
      actualR I C j = (A (n+n+j.val)).submatrix idx idx := by
    ext x y
    change b2z (xor (xor _ _) (xor _ _)) = _
    rw [b2z_xor, b2z_xor, b2z_xor, ← add_assoc]
    rfl
  refine ⟨shallowSet (n+n) C, ?_, ?_, ?_⟩
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩
  · intro j hj
    rw [hR]
    exact (Matrix.rank_submatrix_le _ _ _).trans (hr j hj)
  · intro z
    obtain ⟨c, hc⟩ := hspan (tap z) (htap z).1
    refine ⟨c, ?_⟩
    have hv (r s : Fin n) : wireMat C (tap z) r s = b2z (targetTable (K z) r s) :=
      congrArg b2z ((htap z).2 r s)
    ext x y
    have hp := congrArg (fun (B : Matrix (Fin n) (Fin n) (ZMod 2)) => B (idx x) (idx y)) hc
    simp only [anchor, hv, idx, targetTable, Fin.cases_succ, Fin.cases_zero,
      Equiv.symm_apply_apply, b2z_decide, show b2z false = 0 from rfl, add_zero,
      Matrix.sum_apply, Matrix.smul_apply] at hp
    simpa only [hR, A, Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply,
      anchor, idx] using hp

abbrev F := ZMod 2
abbrev X (q : ℕ) := Fin q → F
abbrev BI {l : ℕ} (s : Fin l → ℕ) := (i : Fin l) × Fin (2*s i)
abbrev Block {l : ℕ} (s : Fin l → ℕ) (i : Fin l) := Matrix (Fin (2*s i)) (Fin (2*s i)) F

open Finset

lemma simultaneous {I H B : Type} [Fintype I] [Fintype H] [Fintype B]
    (U : Matrix I H F) (V : Matrix H I F) (e : B → I)
    (hl : (U*V).submatrix e id = 0) (hr : (U*V).submatrix id e = 0) :
    (U.submatrix e id).rank + (V.submatrix id e).rank + (U*V).rank ≤ Fintype.card H := by
  classical
  let W := V.submatrix id e
  have hl' : U.submatrix e id * V = 0 := by
    simpa only [Matrix.submatrix_mul U V e id id Function.bijective_id,
      Matrix.submatrix_id_id] using hl
  have hr' : U * W = 0 := by
    simpa only [W, Matrix.submatrix_mul U V id id e Function.bijective_id,
      Matrix.submatrix_id_id] using hr
  have h₁ := Matrix.rank_add_rank_le_card_of_mul_eq_zero hl'
  have hle : LinearMap.range W.mulVecLin ≤ LinearMap.range V.mulVecLin := by
    rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  have hker : LinearMap.range W.mulVecLin ≤ LinearMap.ker U.mulVecLin := by
    rw [LinearMap.range_le_ker_iff, ← Matrix.mulVecLin_mul, hr', Matrix.mulVecLin_zero]
  let Y := LinearMap.range V.mulVecLin
  let f := U.mulVecLin.comp Y.subtype
  let g : LinearMap.range W.mulVecLin →ₗ[F] LinearMap.ker f :=
    { toFun := fun x => ⟨⟨x.val, hle x.property⟩, hker x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hg : Function.Injective g := fun x y h => Subtype.ext (congrArg (fun z : LinearMap.ker f => z.val.val) h)
  have hdim := LinearMap.finrank_le_finrank_of_injective hg
  have hf : LinearMap.range f = LinearMap.range (U*V).mulVecLin := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]
  have hn := f.finrank_range_add_finrank_ker
  rw [hf] at hn
  change W.rank ≤ Module.finrank F (LinearMap.ker f) at hdim
  change (U*V).rank + Module.finrank F (LinearMap.ker f) = V.rank at hn
  change (U.submatrix e id).rank + W.rank + (U*V).rank ≤ _
  omega

lemma existenceProjector {B : Type} [Fintype B] (P : Submodule F (B → F)) :
    ∃ L : Matrix B B F, L*L=L ∧ L.rank + Module.finrank F P = Fintype.card B ∧
      ∀ v ∈ P, L.mulVec v = 0 := by
  classical
  obtain ⟨Q,hQ⟩ := P.exists_isCompl
  let f := Q.projection P hQ.symm
  refine ⟨LinearMap.toMatrix' f, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_mul]
    exact congrArg LinearMap.toMatrix' (Submodule.isIdempotentElem_projection hQ.symm).eq
  · have hn := f.finrank_range_add_finrank_ker
    rw [show LinearMap.ker f = P from Submodule.ker_projection _, Module.finrank_pi F] at hn
    change Module.finrank F (LinearMap.range (Matrix.toLin' (LinearMap.toMatrix' f))) + _ = _
    rw [Matrix.toLin'_toMatrix']
    exact hn
  · intro v hv
    rw [LinearMap.toMatrix'_mulVec]
    exact Submodule.projection_apply_of_mem_right hQ.symm hv

lemma factorTwo {I : Type} [Fintype I] (A : Matrix I I F) (h : A.rank ≤ 2) :
    ∃ (u v : Fin 2 → I → F), ∀ i j, A i j = ∑ k, u k i * v k j := by
  classical
  let r := A.rank
  let b := Module.finBasisOfFinrankEq F (LinearMap.range A.mulVecLin)
    (rfl : Module.finrank F (LinearMap.range A.mulVecLin) = r)
  have hcol : ∀ j : I, (fun i => A i j) ∈ LinearMap.range A.mulVecLin := by
    intro j
    refine ⟨Pi.single j 1, ?_⟩
    ext i
    simp [Matrix.mulVec_single]
  let u : Fin 2 → I → F := fun k i => if hk : k.val < r then (b ⟨k.val,hk⟩).val i else 0
  let v : Fin 2 → I → F := fun k j =>
    if hk : k.val < r then b.repr ⟨fun i => A i j, hcol j⟩ ⟨k.val,hk⟩ else 0
  refine ⟨u,v,fun i j => ?_⟩
  have heval : A i j = ∑ t : Fin r, (b t).val i * b.repr ⟨fun i => A i j, hcol j⟩ t := by
    have h1 := congrArg (fun (v : LinearMap.range A.mulVecLin) => v.val i)
      (b.sum_repr ⟨fun i => A i j,hcol j⟩)
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul_of_tower,
      Pi.smul_apply, smul_eq_mul] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [heval]
  symm
  have hfilt : ∑ k : Fin 2, u k i * v k j =
      ∑ k ∈ Finset.univ.filter (fun k : Fin 2 => k.val < r), u k i * v k j := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hnk
    rw [Finset.mem_filter] at hnk
    have hge : ¬ k.val < r := fun hk => hnk ⟨Finset.mem_univ k, hk⟩
    simp [u, v, hge]
  rw [hfilt]
  refine Finset.sum_bij (fun k hk => ⟨k.val, (Finset.mem_filter.mp hk).2⟩) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro k1 _ k2 _ heq; exact Fin.ext (Fin.mk.inj heq)
  · intro t _
    refine ⟨⟨t.val,Nat.lt_of_lt_of_le t.isLt h⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,t.isLt⟩,Fin.ext rfl⟩
  · intro k hk
    have hlt : k.val < r := (Finset.mem_filter.mp hk).2
    simp only [u,v,hlt,dite_true]
    rfl

lemma spanSampling {A B Z : Type} [Fintype A] [DecidableEq A] [Fintype B] [Fintype Z]
    (v : A → B → F) (S : Z → Finset A) (N c : ℕ)
    (hc : ∀ a, N ≤ c * (univ.filter (fun z => a ∈ S z)).card) :
    N * Module.finrank F (Submodule.span F (Set.range v)) ≤
      c * ∑ z, Module.finrank F (Submodule.span F (v '' (S z : Set A))) := by
  classical
  obtain ⟨T, f, hf, heq, hli⟩ := exists_linearIndependent' F v
  letI : Finite T := Finite.of_injective f hf
  letI : Fintype T := Fintype.ofFinite T
  have hcard := linearIndependent_iff_card_eq_finrank_span.mp hli
  change Fintype.card T = Module.finrank F (Submodule.span F (Set.range (v ∘ f))) at hcard
  rw [heq] at hcard
  rw [← hcard]
  have hpt (z : Z) : (univ.filter (fun t : T => f t ∈ S z)).card ≤
      Module.finrank F (Submodule.span F (v '' (S z : Set A))) := by
    let M := univ.filter (fun t : T => f t ∈ S z)
    have hli' := hli.comp (Subtype.val : M → T) Subtype.val_injective
    have hd := linearIndependent_iff_card_eq_finrank_span.mp hli'
    rw [Fintype.card_coe] at hd
    change M.card ≤ _
    rw [hd]
    apply Submodule.finrank_mono
    apply Submodule.span_mono
    rintro _ ⟨t,rfl⟩
    exact ⟨f t.val, (Finset.mem_filter.mp t.property).2, rfl⟩
  calc N * Fintype.card T = ∑ _t : T, N := by simp [Nat.mul_comm]
    _ ≤ ∑ t : T, c * (univ.filter (fun z => f t ∈ S z)).card :=
      Finset.sum_le_sum fun t _ => hc (f t)
    _ = c * ∑ z, (univ.filter (fun t : T => f t ∈ S z)).card := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.sum_le_sum fun z _ => hpt z)

open Finset

abbrev K2 := ZMod 2
abbrev Vec (q : ℕ) := Fin q → K2

def dot {q} (a z : Vec q) : K2 := ∑ k, a k * z k
def plane {q} (a b : Vec q) : Finset (Vec q) := {a,b,a+b}
abbrev off {q} (a b z : Vec q) := dot a z = 0 ∧ dot b z = 0

lemma cases01 (x : K2) : x = 0 ∨ x = 1 := by revert x; decide
lemma nz_one (x : K2) : x ≠ 0 ↔ x = 1 := by rcases cases01 x with rfl|rfl <;> decide

private lemma vec_sum_zero {q} {x y : Vec q} : x+y=0 ↔ x=y := by
  constructor
  · intro h; funext i
    exact CharTwo.add_eq_zero.mp (congrFun h i)
  · rintro rfl; funext i; exact CharTwo.add_self_eq_zero _

private lemma uniform {q t} (M : Matrix (Fin t) (Fin q) K2)
    (h : LinearIndependent K2 M.row) (y : Vec t) :
    Fintype.card (Vec q) = 2^t * (univ.filter (fun z => M.mulVec z = y)).card := by
  classical
  let f := M.mulVecLin
  have hs : Function.Surjective f := h.mulVec_surjective
  have he (v : Vec t) :
      (univ.filter (fun z => f z = v)).card = (univ.filter (fun z => f z = y)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (hs v) (hs y)
  have hc := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Vec q)))
    (t := (univ : Finset (Vec t))) (f := f) (fun _ _ => mem_univ _)
  simp_rw [he] at hc
  simp [f,Fintype.card_fun,ZMod.card] at hc ⊢
  refine hc.trans ?_
  congr 2 <;> ext z <;> simp

lemma half {q} (a : Vec q) (ha : a ≠ 0) :
    Fintype.card (Vec q) = 2 * (univ.filter (fun z => dot a z ≠ 0)).card := by
  let M : Matrix (Fin 1) (Fin q) K2 := ![a]
  have hli : LinearIndependent K2 M.row := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    fin_cases k
    rcases cases01 (g 0) with h|h
    · exact h
    · exfalso; apply ha
      simpa [Fin.sum_univ_one,M,Matrix.row,h] using hg
  have hf : (univ.filter (fun z => M.mulVec z = ![1])).card =
      (univ.filter (fun z => dot a z ≠ 0)).card := by
    congr 1; ext z
    simp only [mem_filter, mem_univ, true_and, nz_one]
    constructor
    · exact fun h => congrFun h 0
    · intro h; funext k; fin_cases k; exact h
  simpa only [pow_one, hf] using uniform M hli ![1]

lemma quarter {q} (a b : Vec q) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Fintype.card (Vec q) = 4 * (univ.filter (off a b)).card := by
  let M : Matrix (Fin 2) (Fin q) K2 := ![a,b]
  have hli : LinearIndependent K2 M.row := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    rcases cases01 (g 0) with h0|h0 <;> rcases cases01 (g 1) with h1|h1 <;>
      simp [Fin.sum_univ_two,M,Matrix.row,h0,h1,vec_sum_zero,ha,hb,hab] at hg
    fin_cases k <;> assumption
  have hf : (univ.filter (fun z => M.mulVec z = ![0,0])).card =
      (univ.filter (off a b)).card := by
    congr 1; ext z
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h0,h1⟩; funext k; fin_cases k <;> assumption
  simpa only [show 2^2 = 4 from rfl, hf] using uniform M hli ![0,0]

lemma eighth {q} (a b c : Vec q) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hc : c ≠ 0) (hbad : c ∉ plane a b) :
    Fintype.card (Vec q) = 8 * (univ.filter (fun z => off a b z ∧ dot c z ≠ 0)).card := by
  have hca : a ≠ c := fun h => hbad (by simp [plane,h])
  have hcb : b ≠ c := fun h => hbad (by simp [plane,h])
  have hcab : a+b ≠ c := fun h => hbad (by simp [plane,h])
  let M : Matrix (Fin 3) (Fin q) K2 := ![a,b,c]
  have hli : LinearIndependent K2 M.row := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    rcases cases01 (g 0) with h0|h0 <;> rcases cases01 (g 1) with h1|h1 <;>
      rcases cases01 (g 2) with h2|h2 <;>
      simp [Fin.sum_univ_three,M,Matrix.row,h0,h1,h2,vec_sum_zero,ha,hb,hab,
        hca,hcb,hcab,hc] at hg
    fin_cases k <;> assumption
  have hf : (univ.filter (fun z => M.mulVec z = ![0,0,1])).card =
      (univ.filter (fun z => off a b z ∧ dot c z ≠ 0)).card := by
    congr 1; ext z
    simp only [mem_filter, mem_univ, true_and, nz_one]
    constructor
    · exact fun h => ⟨⟨congrFun h 0,congrFun h 1⟩,congrFun h 2⟩
    · rintro ⟨⟨h0,h1⟩,h2⟩; funext k; fin_cases k <;> assumption
  simpa only [show 2^3 = 8 from rfl,hf] using uniform M hli ![0,0,1]

open Finset

def pencil {q l} (s : Fin l → ℕ) (a b : Fin l → X q) (U W : (i : Fin l) → Block s i)
    (z : X q) : Matrix (BI s) (BI s) F :=
  Matrix.blockDiagonal' (fun i => dot (a i) z • U i + dot (b i) z • W i)

lemma blockVec {J : Type} [Fintype J] [DecidableEq J] {B : J → Type} [∀ i, Fintype (B i)]
    (D : ∀ i, Matrix (B i) (B i) F) (v : ((i : J) × B i) → F) (i : J) (x : B i) :
    (Matrix.blockDiagonal' D).mulVec v ⟨i,x⟩ = (D i).mulVec (fun y => v ⟨i,y⟩) x := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_sigma]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j h
    exact Finset.sum_eq_zero fun y _ => by rw [Matrix.blockDiagonal'_apply_ne D _ _ h.symm,zero_mul]

lemma dotUnit {q} (a : X q) (k : Fin q) : dot a (Pi.single k 1) = a k := by
  classical
  simp [dot,Pi.single_apply,mul_ite]

lemma pencilExpand {q l} (s : Fin l → ℕ) (a b : Fin l → X q)
    (U W : (i : Fin l) → Block s i) (z : X q) :
    pencil s a b U W z = ∑ k, z k • pencil s a b U W (Pi.single k 1) := by
  classical
  ext ⟨i,x⟩ ⟨j,y⟩
  by_cases h : i=j
  · subst j
    simp only [pencil,Matrix.sum_apply,Matrix.smul_apply,Matrix.blockDiagonal'_apply_eq,
      Matrix.add_apply,smul_eq_mul]
    simp only [dotUnit]
    simp only [dot,Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _; ring
  · simp [pencil,Matrix.sum_apply,Matrix.smul_apply,Matrix.blockDiagonal'_apply_ne _ _ _ h]

def mass {q l} (s : Fin l → ℕ) (a b : Fin l → X q) (z : X q) : ℕ :=
  ∑ i, if off (a i) (b i) z then 0 else 2*s i

lemma mass_le_rank {q l} (s : Fin l → ℕ) (a b : Fin l → X q)
    (U W : (i : Fin l) → Block s i)
    (hr : ∀ i, (U i).rank=2*s i ∧ (W i).rank=2*s i ∧ (U i+W i).rank=2*s i)
    (z : X q) : mass s a b z ≤ (pencil s a b U W z).rank := by
  classical
  let S := univ.filter (fun i => ¬ off (a i) (b i) z)
  let B (i : S) := Fin (2*s i.val)
  let e : ((i : S) × B i) → BI s := fun x => ⟨x.1.val,x.2⟩
  let D (i : S) : Block s i.val := dot (a i.val) z • U i.val + dot (b i.val) z • W i.val
  have hd (i : S) : (D i).rank = Fintype.card (B i) := by
    have hn := (mem_filter.mp i.property).2
    obtain ⟨hU,hW,hUW⟩ := hr i.val
    rcases cases01 (dot (a i.val) z) with h₁|h₁ <;> rcases cases01 (dot (b i.val) z) with h₂|h₂ <;>
      simp_all [D,B,off]
  have hsub : (pencil s a b U W z).submatrix e e = Matrix.blockDiagonal' D := by
    ext ⟨i,x⟩ ⟨j,y⟩
    by_cases h : i=j
    · subst j; simp [e,pencil,D]
    · have h' : i.val ≠ j.val := fun hij => h (Subtype.ext hij)
      simp only [Matrix.submatrix_apply,e,pencil, Matrix.blockDiagonal'_apply_ne _ _ _ h',
        Matrix.blockDiagonal'_apply_ne _ _ _ h]
  have hsur : Function.Surjective (Matrix.blockDiagonal' D).mulVec := by
    intro y
    have hs (i : S) : Function.Surjective (D i).mulVec := Matrix.mulVec_surjective_iff_rank_eq_card.mpr (hd i)
    choose v hv using fun i : S => hs i (fun x => y ⟨i,x⟩)
    refine ⟨fun p => v p.1 p.2, ?_⟩
    funext ⟨i,x⟩
    rw [blockVec]
    exact congrFun (hv i) x
  have hcard : Fintype.card ((i : S) × B i) = mass s a b z := by
    rw [Fintype.card_sigma]
    simp only [B,Fintype.card_fin]
    rw [Finset.sum_coe_sort S (fun i => 2*s i)]
    simp only [S,Finset.sum_filter,mass,ite_not]
  calc mass s a b z = (Matrix.blockDiagonal' D).rank :=
      hcard.symm.trans (Matrix.mulVec_surjective_iff_rank_eq_card.mp hsur).symm
    _ ≤ _ := hsub ▸ Matrix.rank_submatrix_le (pencil s a b U W z) e e

lemma pencil_off {q l} (s : Fin l → ℕ) (a b : Fin l → X q)
    (U W : (i : Fin l) → Block s i) (z : X q) (i : Fin l) (h : off (a i) (b i) z) :
    (pencil s a b U W z).submatrix (Sigma.mk i) id = 0 ∧
    (pencil s a b U W z).submatrix id (Sigma.mk i) = 0 := by
  constructor
  · ext x ⟨j,y⟩
    by_cases hij : i=j
    · subst j; simp [pencil,h.1,h.2]
    · simp [pencil,Matrix.blockDiagonal'_apply_ne _ _ _ hij]
  · ext ⟨j,x⟩ y
    by_cases hij : j=i
    · subst j; simp [pencil,h.1,h.2]
    · simp [pencil,Matrix.blockDiagonal'_apply_ne _ _ _ hij]

open Finset

def active {J : Type} [Fintype J] {q} (m : J → X q) (z : X q) : Finset J :=
  univ.filter (fun j => dot (m j) z ≠ 0)

def slack {J : Type} [Fintype J] {q l} (s : Fin l → ℕ) (a b : Fin l → X q)
    (m : J → X q) (z : X q) := 2*(active m z).card - mass s a b z

lemma sumBudget {J : Type} [Fintype J] {q} (m : J → X q) (hm : ∀ j, m j ≠ 0) :
    (∑ z, 2*(active m z).card) = Fintype.card (X q) * Fintype.card J := by
  classical
  calc (∑ z, 2*(active m z).card) =
      ∑ j, 2 * (univ.filter (fun z => dot (m j) z ≠ 0)).card := by
        simp only [active,Finset.card_filter,Finset.mul_sum]
        rw [Finset.sum_comm]
    _ = ∑ _j : J, Fintype.card (X q) := Finset.sum_congr rfl fun j _ => (half _ (hm j)).symm
    _ = _ := by simp [Nat.mul_comm]

lemma sumMass {q l} (s : Fin l → ℕ) (a b : Fin l → X q)
    (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) :
    2*(∑ z, mass s a b z) = 3*Fintype.card (X q)*(∑ i, s i) := by
  classical
  unfold mass
  rw [Finset.sum_comm,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let Z := univ.filter (fun z => ¬ off (a i) (b i) z)
  let P := univ.filter (off (a i) (b i))
  have hcard : 4*Z.card = 3*Fintype.card (X q) := by
    have hq := quarter (a i) (b i) (hab i).1 (hab i).2.1 (hab i).2.2
    have ha := (univ : Finset (X q)).card_filter_add_card_filter_not (off (a i) (b i))
    rw [card_univ] at ha
    change P.card + Z.card = Fintype.card (X q) at ha
    change Fintype.card (X q) = 4*P.card at hq
    omega
  have hz : (∑ z, if off (a i) (b i) z then 0 else 2*s i) = Z.card*(2*s i) := by
    calc (∑ z, if off (a i) (b i) z then 0 else 2*s i) =
        ∑ z, if ¬ off (a i) (b i) z then 2*s i else 0 := by
          apply Finset.sum_congr rfl
          intro z _
          split_ifs <;> simp_all
      _ = ∑ _z ∈ Z, 2*s i := (Finset.sum_filter ..).symm
      _ = _ := by simp
  rw [hz,← hcard]
  ring

lemma account {J : Type} [Fintype J] {q l} (s : Fin l → ℕ) (a b : Fin l → X q)
    (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) (m : J → X q) (hm : ∀ j, m j ≠ 0)
    (hpt : ∀ z, mass s a b z ≤ 2*(active m z).card) :
    2*(∑ z, slack s a b m z) + 3*Fintype.card (X q)*(∑ i, s i) =
      2*Fintype.card (X q)*Fintype.card J := by
  have h : (∑ z, slack s a b m z) + (∑ z, mass s a b z) = ∑ z, 2*(active m z).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => Nat.sub_add_cancel (hpt z)
  rw [sumBudget m hm] at h
  have h' := sumMass s a b hab
  nlinarith only [h,h']

open Finset

def cols {J I : Type} (u : J → Fin 2 → I → F) (A : Finset J) :
    Matrix I (A × Fin 2) F := fun x jk => u jk.1.val jk.2 x

lemma coordsProduct {J I : Type} [Fintype I] (R : J → Matrix I I F)
    (u v : J → Fin 2 → I → F) (h : ∀ j x y, R j x y = ∑ k, u j k x * v j k y) (A : Finset J) :
    cols u A * (cols v A).transpose = ∑ j ∈ A, R j := by
  classical
  ext x y
  simp only [Matrix.mul_apply,cols,Matrix.transpose_apply,Fintype.sum_prod_type,Matrix.sum_apply,h]
  exact A.sum_coe_sort (fun j => ∑ k, u j k x * v j k y)

def cutSpan {J : Type} {q l} (s : Fin l → ℕ) (a b : Fin l → X q)
    (m : J → X q) (u : J → Fin 2 → BI s → F) (i : Fin l) : Submodule F (X (2*s i)) :=
  Submodule.span F (Set.range (fun p : {j // m j ∉ plane (a i) (b i)} × Fin 2 =>
    fun x => u p.1.val p.2 ⟨i,x⟩))

noncomputable def cutLoss {J : Type} [Fintype J] {q l} (s : Fin l → ℕ) (a b : Fin l → X q)
    (m : J → X q) (u : J → Fin 2 → BI s → F) (i : Fin l) (z : X q) : ℕ :=
  if off (a i) (b i) z then ((cols u (active m z)).submatrix (Sigma.mk i) id).rank else 0

lemma sampledCut {J : Type} [Fintype J] {q l} (s : Fin l → ℕ) (a b : Fin l → X q)
    (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) (m : J → X q) (hm : ∀ j, m j ≠ 0)
    (u : J → Fin 2 → BI s → F) (i : Fin l) :
    Fintype.card (X q) * Module.finrank F (cutSpan s a b m u i) ≤
      8 * ∑ z, cutLoss s a b m u i z := by
  classical
  let H := {j // m j ∉ plane (a i) (b i)} × Fin 2
  let v : H → X (2*s i) := fun p x => u p.1.val p.2 ⟨i,x⟩
  let Z (z : X q) : Finset H := univ.filter (fun p => off (a i) (b i) z ∧ dot (m p.1.val) z ≠ 0)
  have hp (p : H) : Fintype.card (X q) ≤ 8*(univ.filter (fun z => p ∈ Z z)).card := by
    have hc := eighth (a i) (b i) (m p.1.val) (hab i).1 (hab i).2.1 (hab i).2.2
      (hm p.1.val) p.1.property
    simpa [Z] using hc.le
  have hpt (z : X q) : Module.finrank F (Submodule.span F (v '' (Z z : Set H))) ≤
      cutLoss s a b m u i z := by
    by_cases hz : off (a i) (b i) z
    · rw [cutLoss,if_pos hz,Matrix.rank_eq_finrank_span_cols]
      apply Submodule.finrank_mono
      apply Submodule.span_mono
      rintro _ ⟨p,hp,rfl⟩
      exact ⟨(⟨p.1.val,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hp).2.2⟩⟩,p.2),rfl⟩
    · simp [Z,cutLoss,hz]
  exact (spanSampling v Z (Fintype.card (X q)) 8 hp).trans
    (Nat.mul_le_mul_left 8 (Finset.sum_le_sum fun z _ => hpt z))

def project {l} {s : Fin l → ℕ} (L T : (i : Fin l) → Block s i)
    (A : Matrix (BI s) (BI s) F) := Matrix.blockDiagonal' L * A * Matrix.blockDiagonal' T

lemma projectedSupport {J : Type} {q l} (s : Fin l → ℕ) (a b : Fin l → X q)
    (m : J → X q) (R : J → Matrix (BI s) (BI s) F) (u v : J → Fin 2 → BI s → F)
    (h : ∀ j x y, R j x y = ∑ k, u j k x * v j k y)
    (L Q : (i : Fin l) → Block s i)
    (hL : ∀ i w, w ∈ cutSpan s a b m u i → (L i).mulVec w = 0)
    (hQ : ∀ i w, w ∈ cutSpan s a b m v i → (Q i).mulVec w = 0)
    (j : J) (x y : BI s) (hn : project L (fun i => (Q i).transpose) (R j) x y ≠ 0) :
    m j ∈ plane (a x.1) (b x.1) ∧ m j ∈ plane (a y.1) (b y.1) := by
  classical
  have hR : R j = ∑ k, Matrix.vecMulVec (u j k) (v j k) := by
    ext r c; simpa [Matrix.vecMulVec_apply] using h j r c
  have hz : project L (fun i => (Q i).transpose) (R j) x y =
      ∑ k, (L x.1).mulVec (fun r => u j k ⟨x.1,r⟩) x.2 *
        (Q y.1).mulVec (fun c => v j k ⟨y.1,c⟩) y.2 := by
    rw [project,hR,Finset.mul_sum,Finset.sum_mul]
    simp only [Matrix.sum_apply,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,Matrix.vecMulVec_apply,
      ← Matrix.blockDiagonal'_transpose,Matrix.vecMul_transpose]
    exact Finset.sum_congr rfl fun k _ =>
      congrArg₂ (· * ·) (blockVec L (u j k) x.1 x.2) (blockVec Q (v j k) y.1 y.2)
  rw [hz] at hn
  constructor
  · by_contra hn'
    apply hn; apply Finset.sum_eq_zero
    intro k _
    have hm : (fun r => u j k ⟨x.1,r⟩) ∈ cutSpan s a b m u x.1 :=
      Submodule.subset_span ⟨(⟨j,hn'⟩,k),rfl⟩
    rw [hL x.1 _ hm]
    exact zero_mul _
  · by_contra hn'
    apply hn; apply Finset.sum_eq_zero
    intro k _
    have hm : (fun c => v j k ⟨y.1,c⟩) ∈ cutSpan s a b m v y.1 :=
      Submodule.subset_span ⟨(⟨j,hn'⟩,k),rfl⟩
    rw [hQ y.1 _ hm]
    exact mul_zero _

open Finset

private lemma loss_eq {n r k : ℕ} (h : r+k=n) : n-r=k := by omega

lemma compress {q l} {J : Type} [Fintype J] (s : Fin l → ℕ) (a b : Fin l → X q)
    (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (U W : (i : Fin l) → Block s i)
    (hr : ∀ i, (U i).rank=2*s i ∧ (W i).rank=2*s i ∧ (U i+W i).rank=2*s i)
    (m : J → X q) (hm : ∀ j, m j ≠ 0) (R : J → Matrix (BI s) (BI s) F)
    (hR : ∀ j, (R j).rank ≤ 2)
    (hrep : ∀ z, pencil s a b U W z = ∑ j ∈ active m z, R j) :
    3*(∑ i, s i) ≤ 2*Fintype.card J ∧ ∃ (L T : (i : Fin l) → Block s i),
      (∀ i, L i * L i = L i ∧ T i * T i = T i ∧
        (2*s i-(L i).rank) + (2*s i-(T i).rank) + 12*(∑ k, s k) ≤ 8*Fintype.card J) ∧
      ∀ j x y, project L T (R j) x y ≠ 0 →
        m j ∈ plane (a x.1) (b x.1) ∧ m j ∈ plane (a y.1) (b y.1) := by
  classical
  choose u v huv using fun j => factorTwo (R j) (hR j)
  let A z := cols u (active m z)
  let B z := (cols v (active m z)).transpose
  have hK (z : X q) : A z * B z = pencil s a b U W z :=
    (coordsProduct R u v huv (active m z)).trans (hrep z).symm
  have hsize (z : X q) : Fintype.card ((active m z) × Fin 2) = 2*(active m z).card := by
    simp [Fintype.card_prod,Nat.mul_comm]
  have hmass (z : X q) := mass_le_rank s a b U W hr z
  have hpt (z : X q) : mass s a b z ≤ 2*(active m z).card := by
    rw [← hsize]
    have h := hmass z
    rw [← hK] at h
    exact h.trans ((Matrix.rank_mul_le_left (A z) (B z)).trans (A z).rank_le_card_width)
  have haccount := account s a b hab m hm hpt
  have hn : 0 < Fintype.card (X q) := Fintype.card_pos
  have h3 : 3*(∑ i, s i) ≤ 2*Fintype.card J := by
    refine Nat.le_of_mul_le_mul_left ?_ hn
    calc Fintype.card (X q)*(3*(∑ i, s i)) = 3*Fintype.card (X q)*(∑ i, s i) := by ring
      _ ≤ 2*(∑ z, slack s a b m z) + 3*Fintype.card (X q)*(∑ i, s i) := Nat.le_add_left _ _
      _ = 2*Fintype.card (X q)*Fintype.card J := haccount
      _ = Fintype.card (X q)*(2*Fintype.card J) := by ring
  have hloss (i : Fin l) (z : X q) :
      cutLoss s a b m u i z + cutLoss s a b m v i z ≤ slack s a b m z := by
    by_cases hz : off (a i) (b i) z
    · have hzero := pencil_off s a b U W z i hz
      have h := simultaneous (A z) (B z) (Sigma.mk i) (by rw [hK]; exact hzero.1)
        (by rw [hK]; exact hzero.2)
      have hv : ((B z).submatrix id (Sigma.mk i)).rank =
          ((cols v (active m z)).submatrix (Sigma.mk i) id).rank :=
        Matrix.rank_transpose _
      rw [hv,hK,hsize] at h
      simp only [cutLoss,if_pos hz,slack]
      change ((A z).submatrix (Sigma.mk i) id).rank + _ ≤ _
      have hM := hmass z
      omega
    · simp [cutLoss,hz]
  have hdim (i : Fin l) :
      Module.finrank F (cutSpan s a b m u i) + Module.finrank F (cutSpan s a b m v i) +
        12*(∑ k, s k) ≤ 8*Fintype.card J := by
    have hu := sampledCut s a b hab m hm u i
    have hv := sampledCut s a b hab m hm v i
    have hsum := Finset.sum_le_sum (s := (univ : Finset (X q))) (fun z _ => hloss i z)
    rw [Finset.sum_add_distrib] at hsum
    refine Nat.le_of_mul_le_mul_left ?_ hn
    nlinarith only [haccount,hu,hv,hsum]
  choose L hLL hLd hL using fun i => existenceProjector (cutSpan s a b m u i)
  choose Q hQQ hQd hQ using fun i => existenceProjector (cutSpan s a b m v i)
  refine ⟨h3,L,fun i => (Q i).transpose,?_,projectedSupport s a b m R u v huv L Q hL hQ⟩
  intro i
  refine ⟨hLL i,?_,?_⟩
  · rw [← Matrix.transpose_mul,hQQ]
  · rw [Matrix.rank_transpose]
    have hl : (L i).rank + Module.finrank F (cutSpan s a b m u i) = 2*s i := by
      simpa only [Fintype.card_fin] using hLd i
    have hq : (Q i).rank + Module.finrank F (cutSpan s a b m v i) = 2*s i := by
      simpa only [Fintype.card_fin] using hQd i
    rw [loss_eq hl, loss_eq hq]
    exact hdim i

open Finset

lemma selectMask {q l} {G : Type} (s : Fin l → ℕ) (a b : Fin l → X q)
    (U W : (i : Fin l) → Block s i) (D : Finset G) (R : G → Matrix (BI s) (BI s) F)
    (hs : ∀ z, ∃ c : G → F, pencil s a b U W z = ∑ j ∈ D, c j • R j) :
    ∃ (used : Finset G) (m : G → X q), used ⊆ D ∧ (∀ j ∈ used, m j ≠ 0) ∧
      ∀ z, pencil s a b U W z = ∑ j ∈ active (fun j : used => m j.val) z, R j.val := by
  classical
  choose c hc using fun k : Fin q => hs (Pi.single k 1)
  let m : G → X q := fun j k => c k j
  let used := D.filter (fun j => m j ≠ 0)
  refine ⟨used,m,filter_subset _ _,fun j hj => (mem_filter.mp hj).2,?_⟩
  intro z
  calc pencil s a b U W z = ∑ k, z k • pencil s a b U W (Pi.single k 1) :=
      pencilExpand s a b U W z
    _ = ∑ j ∈ D, dot (m j) z • R j := by
      simp_rw [hc,Finset.smul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [dot,Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro k _
      rw [smul_smul,mul_comm]
    _ = ∑ j ∈ active (fun j : used => m j.val) z, R j.val := by
      rw [active,Finset.sum_filter,
        Finset.sum_coe_sort used (fun j => if dot (m j) z ≠ 0 then R j else 0)]
      simp only [used,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : m j = 0
      · simp [hj,dot]
      · rcases cases01 (dot (m j) z) with h|h <;> simp [h,hj]

open Finset

lemma finishBank {q l} {G : Type} [DecidableEq G] (s : Fin l → ℕ) (a b : Fin l → X q)
    (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (hdis : ∀ i j, i ≠ j → Disjoint (plane (a i) (b i)) (plane (a j) (b j)))
    (U W : (i : Fin l) → Block s i)
    (hr : ∀ i, (U i).rank=2*s i ∧ (W i).rank=2*s i ∧ (U i+W i).rank=2*s i)
    (live D : Finset G) (hD : D ⊆ live) (R : G → Matrix (BI s) (BI s) F)
    (hR : ∀ j ∈ D, (R j).rank ≤ 2)
    (hrep : ∀ z, ∃ c : G → F, pencil s a b U W z = ∑ j ∈ D, c j • R j) :
    let d := 2*live.card - 3*(∑ i, s i)
    3*(∑ i, s i) ≤ 2*live.card ∧
      ∃ (E : Finset G) (L T : (i : Fin l) → Block s i),
        E ⊆ live ∧ 2*E.card ≤ d ∧
        (∀ i, L i * L i = L i ∧ T i * T i = T i ∧
          (2*s i - (L i).rank) + (2*s i - (T i).rank) + 8*E.card ≤ 4*d) ∧
        (∀ j ∈ live \ E, ∃ B : Finset (Fin l), B.card ≤ 1 ∧
          ∀ x y, project L T (R j) x y ≠ 0 → x.1 ∈ B ∧ y.1 ∈ B) ∧
        ∀ z, project L T (pencil s a b U W z) ∈ Submodule.span F
          {A : Matrix (BI s) (BI s) F | ∃ j ∈ live \ E, A = project L T (R j)} := by
  intro d
  classical
  obtain ⟨used,m,hsub,hnz,hsel⟩ := selectMask s a b U W D R hrep
  have hused : used ⊆ live := hsub.trans hD
  let E := live \ used
  have hcard : E.card + used.card = live.card := card_sdiff_add_card_eq_card hused
  have hrem : live \ E = used := by
    ext j
    simp only [E,mem_sdiff]
    exact ⟨fun h => by by_contra hn; exact h.2 ⟨h.1,hn⟩,fun h => ⟨hused h, fun h' => h'.2 h⟩⟩
  obtain ⟨h₃,L,T,hLT,hsp⟩ := compress s a b hab U W hr (fun j : used => m j.val)
    (fun j => hnz j.val j.property) (fun j => R j.val)
    (fun j => hR _ (hsub j.property)) hsel
  simp only [Fintype.card_coe] at h₃ hLT
  refine ⟨by omega,E,L,T,sdiff_subset,by dsimp [d]; omega,?_,?_,?_⟩
  · intro i
    obtain ⟨hl,ht,h⟩ := hLT i
    exact ⟨hl,ht,by dsimp [d]; omega⟩
  · intro j hj
    rw [hrem] at hj
    let B := univ.filter (fun i => m j ∈ plane (a i) (b i))
    refine ⟨B,?_,?_⟩
    · apply Finset.card_le_one.mpr
      intro i hi k hk
      by_contra hne
      exact (Finset.disjoint_left.mp (hdis i k hne)) (mem_filter.mp hi).2 (mem_filter.mp hk).2
    · intro x y hxy
      obtain ⟨hx,hy⟩ := hsp (⟨j,hj⟩ : used) x y hxy
      exact ⟨mem_filter.mpr ⟨mem_univ _,hx⟩,mem_filter.mpr ⟨mem_univ _,hy⟩⟩
  · intro z
    rw [hsel z,project,Finset.mul_sum,Finset.sum_mul]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.subset_span ⟨j.val, hrem.symm ▸ j.property,rfl⟩

end PEqualNP.Outside.L_meta_33674

theorem PEqualNP.Outside.L_meta_33674 :
(let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let F := ZMod 2
∀ (q l : ℕ) (s : Fin l → ℕ),
  let V := Fin q → F
  let I := Σ i : Fin l, Fin (2*s i)
  let M := Matrix I I F
  let dot := fun (a z : V) => ∑ k, a k * z k
  ∀ (a b : Fin l → V), (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) →
    let line := fun i : Fin l => ({a i,b i,a i+b i} : Finset V)
    (∀ i j, i ≠ j → Disjoint (line i) (line j)) →
    ∀ (U W : (i : Fin l) → Matrix (Fin (2*s i)) (Fin (2*s i)) F),
      (∀ i, (U i).rank = 2*s i ∧ (W i).rank = 2*s i ∧ (U i + W i).rank = 2*s i) →
      let K := fun (z : V) =>
        Matrix.blockDiagonal' (fun i => dot (a i) z • U i + dot (b i) z • W i)
      let w := Fintype.card I
      let coord := Fintype.equivFin I
      let width := (w+1)+(w+1)
      let table := fun (z : V) (x y : Fin (w+1)) =>
        Fin.cases false (fun i => Fin.cases false (fun j =>
          decide (K z (coord.symm i) (coord.symm j) ≠ 0)) y) x
      let mixed := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (j : Fin C.gates.length)
          (x y : I) =>
        let val := fun (r c : Fin (w+1)) =>
          (⟨C.gates,width+j.val⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval
            (PEqualNP.Represents.oneEach r c)
        xor (xor (val (coord x).succ (coord y).succ) (val (coord x).succ 0))
          (xor (val 0 (coord y).succ) (val 0 0))
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : V → ℕ),
        PEqualNP.MetaComplexity.NestedCover.ReadsBack width C →
        (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
        (∀ z : V, (depths width C).getD (tap z) 0 ≤ 1 ∧
          PEqualNP.Represents.Represents (table z) ⟨C.gates,tap z⟩) →
        let live := Finset.univ.filter (fun j : Fin C.gates.length => nonlinear (C.gates.get j))
        let d := 2*live.card - 3*(∑ i, s i)
        let R := fun j : Fin C.gates.length => (fun x y => if mixed C j x y then 1 else 0 : M)
        3*(∑ i, s i) ≤ 2*live.card ∧
        ∃ (E : Finset (Fin C.gates.length))
          (L T : (i : Fin l) → Matrix (Fin (2*s i)) (Fin (2*s i)) F),
          let proj := fun (A : M) => Matrix.blockDiagonal' L * A * Matrix.blockDiagonal' T
          E ⊆ live ∧ 2*E.card ≤ d ∧
          (∀ i, L i * L i = L i ∧ T i * T i = T i ∧
            (2*s i - (L i).rank) + (2*s i - (T i).rank) + 8*E.card ≤ 4*d) ∧
          (∀ j ∈ live \ E, ∃ B : Finset (Fin l), B.card ≤ 1 ∧
            ∀ x y, proj (R j) x y ≠ 0 → x.1 ∈ B ∧ y.1 ∈ B) ∧
          ∀ z : V, proj (K z) ∈ Submodule.span F {A : M |
            ∃ j ∈ live \ E, A = proj (R j)}) := by
  intro nonlinear depths F q l s V I M dot a b hab line hdis U W hr K w coord width table mixed
    C tap hRB hfan ht live d R
  obtain ⟨D,hD,hR,hrep⟩ := PEqualNP.Outside.L_meta_33674.extractActual
    (PEqualNP.Outside.L_meta_33674.pencil s a b U W) C tap hRB hfan ht
  exact PEqualNP.Outside.L_meta_33674.finishBank s a b hab hdis U W hr live D hD R hR hrep
