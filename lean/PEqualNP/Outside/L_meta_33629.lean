import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33629

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

abbrev F := ZMod 2

def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthsOf (width : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)

def depths (width : ℕ) (C : Circuit) : List ℕ :=
  depthsOf width C.gates

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def b2z (b : Bool) : F := if b then 1 else 0

lemma zmod2_cases (a : F) : a = 0 ∨ a = 1 :=
  match a with
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr rfl

lemma zmod2_add_self (a : F) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma zmod2_sub_eq_add (a b : F) : a - b = a + b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp [b2z] at h ⊢

lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_decide_ne_zero (a : F) [Decidable (a ≠ 0)] : b2z (decide (a ≠ 0)) = a := by
  rcases zmod2_cases a with rfl | rfl <;> simp [b2z]

lemma vec_add_self {α : Type} (v : α → F) : v + v = 0 := by
  funext i; exact zmod2_add_self (v i)

lemma vec_add_eq_zero_iff {α : Type} (u v : α → F) : u + v = 0 ↔ u = v := by
  constructor
  · intro h; funext i
    have hi := congrFun h i
    rcases zmod2_cases (u i) with h1 | h1 <;> rcases zmod2_cases (v i) with hTwo | hTwo <;>
      simp_all
  · rintro rfl; exact vec_add_self u

lemma mat_add_self {α β : Type} (A : Matrix α β F) : A + A = 0 := by
  ext i j; exact zmod2_add_self (A i j)

lemma mat_sub_eq_add {α β : Type} (A B : Matrix α β F) : A - B = A + B := by
  ext i j; exact zmod2_sub_eq_add (A i j) (B i j)

lemma matrix_rank_add_le {α β : Type} [Fintype β] (A B : Matrix α β F) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_add, LinearMap.add_apply]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self A.mulVecLin v)
      (LinearMap.mem_range_self B.mulVecLin v)
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma matrix_rank_sum_le {α β ι : Type} [Fintype β] (s : Finset ι) (f : ι → Matrix α β F) :
    (∑ i ∈ s, f i).rank ≤ ∑ i ∈ s, (f i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    unfold Matrix.rank
    rw [Matrix.mulVecLin_zero, LinearMap.range_zero, finrank_bot]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (matrix_rank_add_le _ _).trans (Nat.add_le_add_left ih _)

private lemma gate_eval_one_affine (op : GateOp) :
    ∃ c0 c1 : F, ∀ x : Bool, b2z (op.eval [x]) = c0 + c1 * b2z x := by
  refine ⟨b2z (op.eval [false]), b2z (op.eval [true]) + b2z (op.eval [false]), fun x => ?_⟩
  cases x
  · simp [b2z]
  · simp only [b2z, ↓reduceIte, mul_one]
    generalize op.eval [false] = a
    generalize op.eval [true] = b
    cases a <;> cases b <;> decide

private lemma gate_eval_two_poly (op : GateOp) :
    ∃ c0 c1 c2 : F, ∀ x y : Bool,
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

private def runFold {α : Type} (step : List α → Gate → α) (init : List α) (gs : List Gate) :
    List α :=
  gs.foldl (fun l g => l ++ [step l g]) init

private lemma runFold_length {α : Type} (step : List α → Gate → α) (init : List α)
    (gs : List Gate) :
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

private lemma getD_append_last {α : Type} (l : List α) (a d0 : α) :
    (l ++ [a]).getD l.length d0 = a := by
  simp [List.getD_eq_getElem?_getD]

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
  have hlen1 : init.length + idx <
      (runFold step (runFold step init (gs.take idx)) [gs[idx]]).length := by
    rw [runFold_length, hlen_take, List.length_singleton]; omega
  rw [runFold_getD_prefix step _ (gs.drop (idx + 1)) (init.length + idx) d0 hlen1]
  unfold runFold
  simp only [List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD]
  have heq : init.length + idx =
      (gs.take idx |>.foldl (fun l g => l ++ [step l g]) init).length := hlen_take.symm
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
      C.gates[idx].op.eval
        (C.gates[idx].inputs.map fun i => (C.wires (oneEach a b)).getD i false) := by
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
  have htake : C.gates = C.gates.take idx ++ C.gates.drop idx :=
    (List.take_append_drop idx C.gates).symm
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
  have htake : C.gates = C.gates.take idx ++ C.gates.drop idx :=
    (List.take_append_drop idx C.gates).symm
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

private lemma depths_getD_oob (width : ℕ) (C : Circuit) (w : ℕ)
    (hw : width + C.gates.length ≤ w) :
    (depths width C).getD w 0 = 0 := by
  rw [depths_eq_runFold, getD_of_ge _ w 0]
  rw [runFold_length, List.length_replicate]
  exact hw

private def anchor {n m : ℕ} (u : Fin n) (v : Fin m)
    (M : Matrix (Fin n) (Fin m) F) : Matrix (Fin n) (Fin m) F :=
  fun a b => M a b + M a v + M u b + M u v

private lemma anchor_add {n m : ℕ} (u : Fin n) (v : Fin m)
    (A B : Matrix (Fin n) (Fin m) F) :
    anchor u v (A + B) = anchor u v A + anchor u v B := by
  ext a b; simp only [anchor, Matrix.add_apply]; ring

private lemma anchor_smul {n m : ℕ} (u : Fin n) (v : Fin m) (c : F)
    (A : Matrix (Fin n) (Fin m) F) :
    anchor u v (c • A) = c • anchor u v A := by
  ext a b; simp only [anchor, Matrix.smul_apply, smul_eq_mul]; ring

private def IsSep {n m : ℕ} (M : Matrix (Fin n) (Fin m) F) : Prop :=
  ∃ (α : Fin n → F) (β : Fin m → F), ∀ a b, M a b = α a + β b

private lemma anchor_of_isSep {n m : ℕ} (u : Fin n) (v : Fin m)
    {M : Matrix (Fin n) (Fin m) F} (hM : IsSep M) :
    anchor u v M = 0 := by
  obtain ⟨α, β, h⟩ := hM
  ext a b
  simp only [anchor, h, Matrix.zero_apply]
  calc α a + β b + (α a + β v) + (α u + β b) + (α u + β v)
      = (α a + α a) + (α u + α u) + (β b + β b) + (β v + β v) := by ring
    _ = 0 := by simp [zmod2_add_self]

private lemma isSep_const {n m : ℕ} (c : F) :
    IsSep (Matrix.of (fun (_ : Fin n) (_ : Fin m) => c)) :=
  ⟨fun _ => c, fun _ => 0, fun _ _ => by simp⟩

private lemma isSep_add {n m : ℕ} {A B : Matrix (Fin n) (Fin m) F}
    (hA : IsSep A) (hB : IsSep B) : IsSep (A + B) := by
  obtain ⟨α1, β1, h1⟩ := hA
  obtain ⟨α2, β2, hTwo⟩ := hB
  refine ⟨fun a => α1 a + α2 a, fun b => β1 b + β2 b, fun a b => ?_⟩
  simp only [Matrix.add_apply, h1, hTwo]
  ring

private lemma isSep_smul {n m : ℕ} (c : F) {A : Matrix (Fin n) (Fin m) F}
    (hA : IsSep A) : IsSep (c • A) := by
  obtain ⟨α, β, h⟩ := hA
  refine ⟨fun a => c * α a, fun b => c * β b, fun a b => ?_⟩
  simp only [Matrix.smul_apply, smul_eq_mul, h]
  ring

private lemma anchor_vecMulVec_rank_le_one {n m : ℕ} (u : Fin n) (v : Fin m)
    (α : Fin n → F) (β : Fin m → F) :
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

private lemma card_liveSet (C : Circuit) : (liveSet C).card = C.gates.countP nonlinear := by
  unfold liveSet
  have h1 : (Finset.univ.filter (fun j : Fin C.gates.length => nonlinear (C.gates.get j))).card =
      ((List.finRange C.gates.length).filter (fun j => nonlinear (C.gates.get j))).length := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _)]
    congr 1
    ext j
    simp
  rw [h1, ← List.countP_eq_length_filter]
  change (List.finRange C.gates.length).countP (nonlinear ∘ C.gates.get) = _
  rw [← List.countP_map]
  have hm : (List.finRange C.gates.length).map C.gates.get = C.gates := by
    apply List.ext_getElem
    · simp
    · intro i h1 hTwo; simp
  rw [hm]

private def wireMat {n m : ℕ} (C : Circuit) (w : ℕ) : Matrix (Fin n) (Fin m) F :=
  fun a b => b2z ((C.wires (oneEach a b)).getD w false)

private lemma actualForward {n m : ℕ} (u : Fin n) (v : Fin m) (C : Circuit)
    (hRB : ReadsBack (n + m) C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (∀ j ∈ shallowSet (n + m) C, (anchor u v (wireMat C (n + m + j.val))).rank ≤ 2) ∧
    ∀ w : ℕ, (depths (n + m) C).getD w 0 ≤ 1 → ∃ c : Fin C.gates.length → F,
      anchor u v (wireMat C w) =
        ∑ j ∈ shallowSet (n + m) C, c j • anchor u v (wireMat C (n + m + j.val)) := by
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
              have hcomb : val w =
                  Matrix.of (fun (_ : Fin n) (_ : Fin m) => c0) + c1 • val i1 := by
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
              have hcomb : val w = Matrix.of (fun (_ : Fin n) (_ : Fin m) => c0) +
                  c1 • val i1 + c2 • val i2 := by
                ext a b
                rw [hval_g a b, hlist]
                have hp := hpoly ((C.wires (oneEach a b)).getD i1 false)
                  ((C.wires (oneEach a b)).getD i2 false)
                rw [hxor_false] at hp
                simp only [b2z, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero] at hp
                exact hp
              rw [hcomb]
              exact isSep_add (isSep_add (isSep_const c0) (isSep_smul c1 hi1_sep))
                (isSep_smul c2 hi2_sep)
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
    · have hdep_g : dep (n + m + idx.val) =
          (g.inputs.map dep).foldr max 0 + (nonlinear g).toNat :=
        depths_getD_gate C hRB idx.val idx.isLt
      rw [hdep1, hnl, hlist] at hdep_g
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
        Bool.toNat_true] at hdep_g
      have hdi1 : dep i1 = 0 := by omega
      have hdi2 : dep i2 = 0 := by omega
      obtain ⟨α1, β1, h1⟩ := hdep0_sep i1 hdi1
      obtain ⟨α2, β2, hTwo⟩ := hdep0_sep i2 hdi2
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
          have hv2 : b2z ((C.wires (oneEach a b)).getD i2 false) = α2 a + β2 b := hTwo a b
          change b2z ((C.wires (oneEach a b)).getD (n + m + idx.val) false) = _
          rw [hw, show C.gates[idx.val] = g from rfl, hlist]
          simp only [List.map_cons, List.map_nil]
          rw [hp, hv1, hv2]
          simp only [b2z, ↓reduceIte, one_mul, Matrix.add_apply, Matrix.vecMulVec_apply,
            Matrix.of_apply]
          ring
        change anchor u v (val (n + m + idx.val)) = _
        rw [hval_eq, anchor_add, anchor_add, anchor_of_isSep u v hsep_part, add_zero]
      rw [hdecomp]
      calc (anchor u v (Matrix.vecMulVec α1 β2) + anchor u v (Matrix.vecMulVec α2 β1)).rank
          ≤ (anchor u v (Matrix.vecMulVec α1 β2)).rank +
              (anchor u v (Matrix.vecMulVec α2 β1)).rank :=
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
            have hcomb : val w =
                Matrix.of (fun (_ : Fin n) (_ : Fin m) => c0) + c1 • val i1 := by
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
            have hcomb : val w = Matrix.of (fun (_ : Fin n) (_ : Fin m) => c0) +
                c1 • val i1 + c2 • val i2 := by
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

def mkTable {w : ℕ} {α : Type} (coord : α ≃ Fin w) (M : Matrix α α F)
    (x y : Fin (w + 1)) : Bool :=
  Fin.cases false (fun i => Fin.cases false (fun j =>
    decide (M (coord.symm i) (coord.symm j) ≠ 0)) y) x

def actualR {w : ℕ} {α : Type} (coord : α ≃ Fin w) (C : Circuit) (j : Fin C.gates.length) :
    Matrix α α F := fun x y =>
  let val := fun (r c : Fin (w + 1)) =>
    (⟨C.gates, (w + 1) + (w + 1) + j.val⟩ : Circuit).eval (oneEach r c)
  if xor (xor (val (coord x).succ (coord y).succ) (val (coord x).succ 0))
      (xor (val 0 (coord y).succ) (val 0 0)) then 1 else 0

lemma extractSpan {w t : ℕ} {α Z : Type} [Fintype α]
    (coord : α ≃ Fin w) (Target : Z → Matrix α α F)
    (C : Circuit) (tap : Z → ℕ)
    (hRB : ReadsBack ((w + 1) + (w + 1)) C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcnt : C.gates.countP nonlinear ≤ t)
    (htap : ∀ z, (depths ((w + 1) + (w + 1)) C).getD (tap z) 0 ≤ 1 ∧
      Represents (mkTable coord (Target z)) ⟨C.gates, tap z⟩) :
    ∃ (D : Finset (Fin C.gates.length)), D.card ≤ t ∧
      (∀ j ∈ D, (actualR coord C j).rank ≤ 2) ∧
      ∀ z, Target z ∈ Submodule.span F (Set.range (fun j : D => actualR coord C j.val)) := by
  classical
  let n := w + 1
  let idx : α → Fin n := fun i => (coord i).succ
  let A (u : ℕ) := anchor (0 : Fin n) (0 : Fin n) (wireMat C u)
  obtain ⟨hr, hspan⟩ := actualForward (0 : Fin n) (0 : Fin n) C hRB hfan
  have hR (j : Fin C.gates.length) :
      actualR coord C j = (A (n + n + j.val)).submatrix idx idx := by
    ext x y
    change b2z (xor (xor _ _) (xor _ _)) = _
    rw [b2z_xor, b2z_xor, b2z_xor, ← add_assoc]
    rfl
  have hsub : shallowSet (n + n) C ⊆ liveSet C := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩
  refine ⟨shallowSet (n + n) C, ?_, ?_, ?_⟩
  · exact (Finset.card_le_card hsub).trans ((card_liveSet C).le.trans hcnt)
  · intro j hj
    rw [hR]
    exact (Matrix.rank_submatrix_le _ _ _).trans (hr j hj)
  · intro z
    obtain ⟨c, hc⟩ := hspan (tap z) (htap z).1
    have hv (r s : Fin n) : wireMat C (tap z) r s = b2z (mkTable coord (Target z) r s) :=
      congrArg b2z ((htap z).2 r s)
    have htz : Target z = ∑ j ∈ shallowSet (n + n) C, c j • actualR coord C j := by
      ext x y
      have hp := congrArg (fun (B : Matrix (Fin n) (Fin n) F) => B (idx x) (idx y)) hc
      simp only [anchor, hv, idx, mkTable, Fin.cases_succ, Fin.cases_zero,
        Equiv.symm_apply_apply, b2z_decide_ne_zero, show b2z false = 0 from rfl, add_zero,
        Matrix.sum_apply, Matrix.smul_apply] at hp
      simpa only [hR, A, Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply,
        anchor, idx] using hp
    rw [htz]
    apply Submodule.sum_mem
    intro j hj
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)

private lemma depthsOf_length (width : ℕ) (gs : List Gate) :
    (depthsOf width gs).length = width + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [depthsOf]
  | append_singleton gs g ih =>
    simp only [depthsOf, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton] at ih ⊢
    omega

private lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresOf]
  | append_singleton gs g ih =>
    simp only [wiresOf, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton] at ih ⊢
    omega

private lemma wiresOf_append_prefix (gs1 gs2 : List Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs1.length) :
    (wiresOf (gs1 ++ gs2) x).getD w false = (wiresOf gs1 x).getD w false := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    have h1 : gs1 ++ (gs2 ++ [g]) = (gs1 ++ gs2) ++ [g] := (List.append_assoc _ _ _).symm
    have hstep : wiresOf ((gs1 ++ gs2) ++ [g]) x =
        wiresOf (gs1 ++ gs2) x ++
          [g.op.eval (g.inputs.map fun i => (wiresOf (gs1 ++ gs2) x).getD i false)] := by
      simp [wiresOf, List.foldl_append]
    rw [h1, hstep, getD_append_left _ _ _ _ (by rw [wiresOf_length, List.length_append]; omega)]
    exact ih

private lemma depthsOf_append_prefix (width : ℕ) (gs1 gs2 : List Gate) (w : ℕ)
    (hw : w < width + gs1.length) :
    (depthsOf width (gs1 ++ gs2)).getD w 0 = (depthsOf width gs1).getD w 0 := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    have h1 : gs1 ++ (gs2 ++ [g]) = (gs1 ++ gs2) ++ [g] := (List.append_assoc _ _ _).symm
    have hstep : depthsOf width ((gs1 ++ gs2) ++ [g]) =
        depthsOf width (gs1 ++ gs2) ++
          [(g.inputs.map (fun a => (depthsOf width (gs1 ++ gs2)).getD a 0)).foldr max 0 +
            (nonlinear g).toNat] := by
      simp [depthsOf, List.foldl_append]
    rw [h1, hstep, getD_append_left _ _ _ _ (by rw [depthsOf_length, List.length_append]; omega)]
    exact ih

abbrev Quad (n m : ℕ) :=
  (Fin n → F) × (Fin m → F) × (Fin n → F) × (Fin m → F)

def evalQuad {n m : ℕ} (q : Quad n m) (x : Fin n) (y : Fin m) : F :=
  q.1 x * q.2.1 y + q.2.2.1 x * q.2.2.2 y

private def goodGates (w : ℕ) (gs : List Gate) : Prop :=
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < w + j) ∧
  (∀ g ∈ gs, g.inputs.length ≤ 2)

private lemma append_gate_good (w : ℕ) (gs : List Gate) (g : Gate)
    (hgood : goodGates w gs) (hfan : g.inputs.length ≤ 2)
    (hback : ∀ i ∈ g.inputs, i < w + gs.length) :
    goodGates w (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [getD_append_left _ _ _ _ hlt] at hi
      exact hgood.1 j hlt i hi
    · have heq : j = gs.length := by omega
      subst heq
      rw [getD_append_last] at hi
      exact hback i hi
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | rfl
    · exact hgood.2 g' h
    · exact hfan

private lemma append_constFalse (w : ℕ) (gs : List Gate) (hgood : goodGates w gs) :
    let gs' := gs ++ [⟨GateOp.or, []⟩]
    let out := w + gs.length
    gs.length ≤ gs'.length ∧ goodGates w gs' ∧
    gs'.countP nonlinear = gs.countP nonlinear ∧
    out < w + gs'.length ∧
    (depthsOf w gs').getD out 0 = 0 ∧
    (∀ u < w + gs.length, (depthsOf w gs').getD u 0 = (depthsOf w gs).getD u 0) ∧
    (∀ (x : List Bool), x.length = w →
      (∀ u < w + gs.length, (wiresOf gs' x).getD u false = (wiresOf gs x).getD u false) ∧
      (wiresOf gs' x).getD out false = false) := by
  intro gs' out
  have hnl : nonlinear ⟨GateOp.or, []⟩ = false := by decide
  refine ⟨by simp [gs'], append_gate_good w gs _ hgood (by simp) (fun _ h => by cases h),
    by simp [gs', List.countP_append, hnl], by simp [gs', out], ?_, ?_, ?_⟩
  · simp only [gs', out, depthsOf, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (depthsOf w gs).length = w + gs.length := depthsOf_length w gs
    change ((depthsOf w gs) ++ [_]).getD (w + gs.length) 0 = 0
    rw [← hlen, getD_append_last]
    simp [hnl]
  · intro u hu
    exact depthsOf_append_prefix w gs _ u hu
  · intro x hx
    refine ⟨fun u hu => wiresOf_append_prefix gs _ x u (by omega), ?_⟩
    simp only [gs', out, wiresOf, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (wiresOf gs x).length = w + gs.length := by rw [wiresOf_length, hx]
    change ((wiresOf gs x) ++ [_]).getD (w + gs.length) false = false
    rw [← hlen, getD_append_last]
    rfl

private lemma append_xor2 (w : ℕ) (gs : List Gate) (u v : ℕ)
    (hgood : goodGates w gs) (hu : u < w + gs.length) (hv : v < w + gs.length) :
    let gs' := gs ++ [⟨GateOp.mod 2, [u, v]⟩, ⟨GateOp.not, [w + gs.length]⟩]
    let out := w + gs.length + 1
    gs.length ≤ gs'.length ∧ goodGates w gs' ∧
    gs'.countP nonlinear = gs.countP nonlinear ∧
    out < w + gs'.length ∧
    (depthsOf w gs').getD out 0 = max ((depthsOf w gs).getD u 0) ((depthsOf w gs).getD v 0) ∧
    (∀ k < w + gs.length, (depthsOf w gs').getD k 0 = (depthsOf w gs).getD k 0) ∧
    (∀ (x : List Bool), x.length = w →
      (∀ k < w + gs.length, (wiresOf gs' x).getD k false = (wiresOf gs x).getD k false) ∧
      (wiresOf gs' x).getD out false =
        xor ((wiresOf gs x).getD u false) ((wiresOf gs x).getD v false)) := by
  intro gs' out
  have hnl1 : nonlinear ⟨GateOp.mod 2, [u, v]⟩ = false := by simp [nonlinear]; decide
  have hnl2 : nonlinear ⟨GateOp.not, [w + gs.length]⟩ = false := by simp [nonlinear]
  have hgs'_eq : gs' = (gs ++ [⟨GateOp.mod 2, [u, v]⟩]) ++ [⟨GateOp.not, [w + gs.length]⟩] := by
    simp [gs']
  have hgood1 : goodGates w (gs ++ [⟨GateOp.mod 2, [u, v]⟩]) :=
    append_gate_good w gs _ hgood (by simp) (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega)
  have hgood2 : goodGates w gs' := by
    rw [hgs'_eq]
    exact append_gate_good w _ _ hgood1 (by simp) (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rw [hi, List.length_append, List.length_singleton]; omega)
  refine ⟨by simp [gs'], hgood2, by simp [gs', List.countP_append, hnl1, hnl2],
    by simp [gs', out]; omega, ?_, ?_, ?_⟩
  · rw [hgs'_eq]
    set gs1 := gs ++ [⟨GateOp.mod 2, [u, v]⟩]
    have hd1_len : (depthsOf w gs1).length = w + gs.length + 1 := by
      rw [depthsOf_length]; simp [gs1]; omega
    have hd0_len : (depthsOf w gs).length = w + gs.length := depthsOf_length w gs
    have hd_mid : (depthsOf w gs1).getD (w + gs.length) 0 =
        max ((depthsOf w gs).getD u 0) ((depthsOf w gs).getD v 0) := by
      have hstep : depthsOf w gs1 = depthsOf w gs ++
          [(([u, v]).map (fun a => (depthsOf w gs).getD a 0)).foldr max 0 +
            (nonlinear ⟨GateOp.mod 2, [u, v]⟩).toNat] := by
        simp [gs1, depthsOf, List.foldl_append]
      rw [hstep, ← hd0_len, getD_append_last, hnl1]
      simp
    have hstep2 : depthsOf w (gs1 ++ [⟨GateOp.not, [w + gs.length]⟩]) = depthsOf w gs1 ++
        [(([w + gs.length]).map (fun a => (depthsOf w gs1).getD a 0)).foldr max 0 +
          (nonlinear ⟨GateOp.not, [w + gs.length]⟩).toNat] := by
      simp [depthsOf, List.foldl_append]
    rw [hstep2]
    change (depthsOf w gs1 ++ _).getD (w + gs.length + 1) 0 = _
    rw [← hd1_len, getD_append_last, hnl2]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
      Bool.toNat_false, add_zero]
    rw [hd_mid]
    omega
  · intro k hk
    exact depthsOf_append_prefix w gs _ k hk
  · intro x hx
    refine ⟨fun k hk => wiresOf_append_prefix gs _ x k (by omega), ?_⟩
    rw [hgs'_eq]
    set gs1 := gs ++ [⟨GateOp.mod 2, [u, v]⟩]
    have hw0_len : (wiresOf gs x).length = w + gs.length := by rw [wiresOf_length, hx]
    have hw1_len : (wiresOf gs1 x).length = w + gs.length + 1 := by
      rw [wiresOf_length, hx]; simp [gs1]; omega
    have hmid : (wiresOf gs1 x).getD (w + gs.length) false =
        (GateOp.mod 2).eval [(wiresOf gs x).getD u false, (wiresOf gs x).getD v false] := by
      have hstep : wiresOf gs1 x = wiresOf gs x ++
          [(GateOp.mod 2).eval (([u, v]).map fun i => (wiresOf gs x).getD i false)] := by
        simp [gs1, wiresOf, List.foldl_append]
      rw [hstep, ← hw0_len, getD_append_last]
      rfl
    have hstep2 : wiresOf (gs1 ++ [⟨GateOp.not, [w + gs.length]⟩]) x = wiresOf gs1 x ++
        [GateOp.not.eval (([w + gs.length]).map fun i => (wiresOf gs1 x).getD i false)] := by
      simp [wiresOf, List.foldl_append]
    rw [hstep2]
    change (wiresOf gs1 x ++ _).getD (w + gs.length + 1) false = _
    rw [← hw1_len, getD_append_last]
    simp only [List.map_cons, List.map_nil]
    rw [hmid]
    generalize (wiresOf gs x).getD u false = bu
    generalize (wiresOf gs x).getD v false = bv
    cases bu <;> cases bv <;> decide

private lemma append_and2 (w : ℕ) (gs : List Gate) (u v : ℕ)
    (hgood : goodGates w gs) (hu : u < w + gs.length) (hv : v < w + gs.length) :
    let gs' := gs ++ [⟨GateOp.and, [u, v]⟩]
    let out := w + gs.length
    gs.length ≤ gs'.length ∧ goodGates w gs' ∧
    gs'.countP nonlinear = gs.countP nonlinear + 1 ∧
    out < w + gs'.length ∧
    (depthsOf w gs').getD out 0 =
      max ((depthsOf w gs).getD u 0) ((depthsOf w gs).getD v 0) + 1 ∧
    (∀ k < w + gs.length, (depthsOf w gs').getD k 0 = (depthsOf w gs).getD k 0) ∧
    (∀ (x : List Bool), x.length = w →
      (∀ k < w + gs.length, (wiresOf gs' x).getD k false = (wiresOf gs x).getD k false) ∧
      (wiresOf gs' x).getD out false =
        ((wiresOf gs x).getD u false && (wiresOf gs x).getD v false)) := by
  intro gs' out
  have hnl : nonlinear ⟨GateOp.and, [u, v]⟩ = true := by simp [nonlinear]; decide
  refine ⟨by simp [gs'], append_gate_good w gs _ hgood (by simp) (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega),
    by simp [gs', List.countP_append, hnl], by simp [gs', out], ?_, ?_, ?_⟩
  · have hstep : depthsOf w gs' = depthsOf w gs ++
        [(([u, v]).map (fun a => (depthsOf w gs).getD a 0)).foldr max 0 +
          (nonlinear ⟨GateOp.and, [u, v]⟩).toNat] := by
      simp [gs', depthsOf, List.foldl_append]
    have hlen : (depthsOf w gs).length = w + gs.length := depthsOf_length w gs
    rw [hstep]
    change (depthsOf w gs ++ _).getD (w + gs.length) 0 = _
    rw [← hlen, getD_append_last, hnl]
    simp
  · intro k hk
    exact depthsOf_append_prefix w gs _ k hk
  · intro x hx
    refine ⟨fun k hk => wiresOf_append_prefix gs _ x k (by omega), ?_⟩
    have hstep : wiresOf gs' x = wiresOf gs x ++
        [GateOp.and.eval (([u, v]).map fun i => (wiresOf gs x).getD i false)] := by
      simp [gs', wiresOf, List.foldl_append]
    have hlen : (wiresOf gs x).length = w + gs.length := by rw [wiresOf_length, hx]
    rw [hstep]
    change (wiresOf gs x ++ _).getD (w + gs.length) false = _
    rw [← hlen, getD_append_last]
    simp only [List.map_cons, List.map_nil]
    generalize (wiresOf gs x).getD u false = bu
    generalize (wiresOf gs x).getD v false = bv
    cases bu <;> cases bv <;> decide

private lemma exists_xorList (w : ℕ) (gs : List Gate) (ws : List ℕ) (D : ℕ)
    (hgood : goodGates w gs) (hws : ∀ u ∈ ws, u < w + gs.length)
    (hdep : ∀ u ∈ ws, (depthsOf w gs).getD u 0 ≤ D) :
    ∃ (gs' : List Gate) (out : ℕ),
      gs.length ≤ gs'.length ∧ goodGates w gs' ∧
      gs'.countP nonlinear = gs.countP nonlinear ∧
      out < w + gs'.length ∧
      (depthsOf w gs').getD out 0 ≤ D ∧
      (∀ k < w + gs.length, (depthsOf w gs').getD k 0 = (depthsOf w gs).getD k 0) ∧
      (∀ (x : List Bool), x.length = w →
        (∀ k < w + gs.length, (wiresOf gs' x).getD k false = (wiresOf gs x).getD k false) ∧
        b2z ((wiresOf gs' x).getD out false) =
          (ws.map (fun u => b2z ((wiresOf gs x).getD u false))).sum) := by
  induction ws with
  | nil =>
    have h := append_constFalse w gs hgood
    refine ⟨_, _, h.1, h.2.1, h.2.2.1, h.2.2.2.1, by rw [h.2.2.2.2.1]; omega, h.2.2.2.2.2.1,
      fun x hx => ⟨(h.2.2.2.2.2.2 x hx).1, by rw [(h.2.2.2.2.2.2 x hx).2]; simp [b2z]⟩⟩
  | cons a t ih =>
    have ha : a < w + gs.length := hws a List.mem_cons_self
    have ha_dep : (depthsOf w gs).getD a 0 ≤ D := hdep a List.mem_cons_self
    rcases ih (fun u hu => hws u (List.mem_cons_of_mem a hu))
      (fun u hu => hdep u (List.mem_cons_of_mem a hu)) with
      ⟨gs1, out1, hlen1, hgood1, hcnt1, hout1, hdep1, hdpref1, hval1⟩
    have hTwo := append_xor2 w gs1 a out1 hgood1 (by omega) hout1
    refine ⟨_, _, by omega, hTwo.2.1, by rw [hTwo.2.2.1, hcnt1], hTwo.2.2.2.1, ?_, ?_, ?_⟩
    · rw [hTwo.2.2.2.2.1, hdpref1 a ha]
      exact max_le ha_dep hdep1
    · intro k hk
      rw [hTwo.2.2.2.2.2.1 k (by omega), hdpref1 k hk]
    · intro x hx
      refine ⟨fun k hk => by rw [(hTwo.2.2.2.2.2.2 x hx).1 k (by omega), (hval1 x hx).1 k hk], ?_⟩
      rw [(hTwo.2.2.2.2.2.2 x hx).2, b2z_xor, (hval1 x hx).1 a ha, (hval1 x hx).2]
      simp

private lemma synth_depth1_quads (n m q : ℕ) (qs : List (Quad n m))
    (mask : Fin q → Fin qs.length → F)
    (α : Fin q → Fin n → F) (β : Fin q → Fin m → F) :
    ∃ (C : Circuit) (tap : Fin q → ℕ),
      ReadsBack (n + m) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP nonlinear ≤ qs.length ∧
      ∀ j : Fin q, (depthsOf (n + m) C.gates).getD (tap j) 0 ≤ 1 ∧
        ∀ (x : Fin n) (y : Fin m),
          b2z ((wiresOf C.gates (oneEach x y)).getD (tap j) false) =
            α j x + β j y + ∑ p : Fin qs.length, mask j p * evalQuad (qs.get p) x y := by
  classical
  have hbase_in : ∀ (gs : List Gate) (x : Fin n) (y : Fin m),
      (∀ i : Fin n, (wiresOf gs (oneEach x y)).getD i.val false = decide (i = x)) ∧
      (∀ j : Fin m, (wiresOf gs (oneEach x y)).getD (n + j.val) false = decide (j = y)) := by
    intro gs x y
    constructor
    · intro i
      have h1 := wiresOf_append_prefix [] gs (oneEach x y) i.val
        (by rw [oneEach_length]; simp; omega)
      change (wiresOf gs (oneEach x y)).getD i.val false = (oneEach x y).getD i.val false at h1
      rw [h1]
      simp only [oneEach]
      have hlen : (List.ofFn (fun i' : Fin n => decide (i' = x))).length = n := by simp
      rw [getD_append_left _ _ _ _ (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]
    · intro j
      have h1 := wiresOf_append_prefix [] gs (oneEach x y) (n + j.val)
        (by rw [oneEach_length]; simp)
      change (wiresOf gs (oneEach x y)).getD (n + j.val) false =
        (oneEach x y).getD (n + j.val) false at h1
      rw [h1]
      simp only [oneEach]
      have hlen : (List.ofFn (fun i' : Fin n => decide (i' = x))).length = n := by simp
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]; omega)]
      simp only [hlen, Nat.add_sub_cancel_left, List.getElem?_ofFn, dif_pos j.isLt,
        Option.getD_some]
  have hbase_dep : ∀ (gs : List Gate) (u : ℕ), u < n + m →
      (depthsOf (n + m) gs).getD u 0 = 0 := by
    intro gs u hu
    have h1 := depthsOf_append_prefix (n + m) [] gs u (by simp; omega)
    change (depthsOf (n + m) gs).getD u 0 = (List.replicate (n + m) 0).getD u 0 at h1
    rw [h1]
    simp [List.getD_eq_getElem?_getD, hu]
  have hbuild_aff : ∀ (gs : List Gate) (f : Fin n → F) (h : Fin m → F),
      goodGates (n + m) gs →
      ∃ (gs' : List Gate) (out : ℕ),
        gs.length ≤ gs'.length ∧ goodGates (n + m) gs' ∧
        gs'.countP nonlinear = gs.countP nonlinear ∧
        out < (n + m) + gs'.length ∧
        (depthsOf (n + m) gs').getD out 0 = 0 ∧
        (∀ k < (n + m) + gs.length,
          (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
        (∀ (x : Fin n) (y : Fin m),
          (∀ k < (n + m) + gs.length,
            (wiresOf gs' (oneEach x y)).getD k false = (wiresOf gs (oneEach x y)).getD k false) ∧
          b2z ((wiresOf gs' (oneEach x y)).getD out false) = f x + h y) := by
    intro gs f h hgood
    let wsX : List ℕ := ((List.finRange n).filter (fun i => decide (f i = 1))).map Fin.val
    let wsY : List ℕ :=
      ((List.finRange m).filter (fun j => decide (h j = 1))).map (fun j => n + j.val)
    let ws := wsX ++ wsY
    have hws_lt : ∀ u ∈ ws, u < (n + m) + gs.length := by
      intro u hu
      simp only [ws, wsX, wsY, List.mem_append, List.mem_map, List.mem_filter] at hu
      rcases hu with ⟨i, _, rfl⟩ | ⟨j, _, rfl⟩ <;> omega
    have hws_dep : ∀ u ∈ ws, (depthsOf (n + m) gs).getD u 0 ≤ 0 := by
      intro u hu
      simp only [ws, wsX, wsY, List.mem_append, List.mem_map, List.mem_filter] at hu
      rcases hu with ⟨i, _, rfl⟩ | ⟨j, _, rfl⟩
      · rw [hbase_dep gs i.val (by omega)]
      · rw [hbase_dep gs (n + j.val) (by omega)]
    rcases exists_xorList (n + m) gs ws 0 hgood hws_lt hws_dep with
      ⟨gs', out, hlen, hgood', hcnt, hout, hdep, hdpref, hval⟩
    refine ⟨gs', out, hlen, hgood', hcnt, hout, by omega, hdpref, fun x y => ?_⟩
    have hv := hval (oneEach x y) (oneEach_length x y)
    refine ⟨hv.1, ?_⟩
    rw [hv.2]
    simp only [ws, List.map_append, List.sum_append]
    have hsumX :
        (wsX.map (fun u => b2z ((wiresOf gs (oneEach x y)).getD u false))).sum = f x := by
      have h1 : wsX.map (fun u => b2z ((wiresOf gs (oneEach x y)).getD u false)) =
          ((List.finRange n).filter (fun i => decide (f i = 1))).map
            (fun i => b2z (decide (i = x))) := by
        simp only [wsX, List.map_map]
        refine List.map_congr_left fun i _ => ?_
        dsimp only [Function.comp]
        rw [(hbase_in gs x y).1 i]
      rw [h1]
      have hnodup : ((List.finRange n).filter (fun i => decide (f i = 1))).Nodup :=
        (List.nodup_finRange n).filter _
      have htoF : ((List.finRange n).filter (fun i => decide (f i = 1))).toFinset =
          Finset.univ.filter (fun i : Fin n => f i = 1) := by ext i; simp
      rw [← List.sum_toFinset _ hnodup, htoF]
      by_cases hfx : f x = 1
      · rw [Finset.sum_eq_single x]
        · simp [hfx, b2z]
        · intro i _ hix; simp [hix, b2z]
        · intro h0; exact (h0 (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hfx⟩)).elim
      · have hfx0 : f x = 0 := by
          rcases zmod2_cases (f x) with h0 | h1; exact h0; exact (hfx h1).elim
        rw [hfx0]
        apply Finset.sum_eq_zero
        intro i hi
        have hne : i ≠ x := fun heq => hfx (heq ▸ (Finset.mem_filter.mp hi).2)
        simp [hne, b2z]
    have hsumY :
        (wsY.map (fun u => b2z ((wiresOf gs (oneEach x y)).getD u false))).sum = h y := by
      have h1 : wsY.map (fun u => b2z ((wiresOf gs (oneEach x y)).getD u false)) =
          ((List.finRange m).filter (fun j => decide (h j = 1))).map
            (fun j => b2z (decide (j = y))) := by
        simp only [wsY, List.map_map]
        refine List.map_congr_left fun j _ => ?_
        dsimp only [Function.comp]
        rw [(hbase_in gs x y).2 j]
      rw [h1]
      have hnodup : ((List.finRange m).filter (fun j => decide (h j = 1))).Nodup :=
        (List.nodup_finRange m).filter _
      have htoF : ((List.finRange m).filter (fun j => decide (h j = 1))).toFinset =
          Finset.univ.filter (fun j : Fin m => h j = 1) := by ext j; simp
      rw [← List.sum_toFinset _ hnodup, htoF]
      by_cases hhy : h y = 1
      · rw [Finset.sum_eq_single y]
        · simp [hhy, b2z]
        · intro j _ hjy; simp [hjy, b2z]
        · intro hm; exact (hm (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hhy⟩)).elim
      · have hhy0 : h y = 0 := by
          rcases zmod2_cases (h y) with h0 | h1; exact h0; exact (hhy h1).elim
        rw [hhy0]
        apply Finset.sum_eq_zero
        intro j hj
        have hne : j ≠ y := fun heq => hhy (heq ▸ (Finset.mem_filter.mp hj).2)
        simp [hne, b2z]
    rw [hsumX, hsumY]
  have hstage1 : ∀ (k : ℕ) (hk : k ≤ qs.length),
      ∃ (gs : List Gate) (prodW : Fin k → ℕ),
        goodGates (n + m) gs ∧
        gs.countP nonlinear = k ∧
        (∀ p : Fin k, prodW p < (n + m) + gs.length) ∧
        (∀ p : Fin k, (depthsOf (n + m) gs).getD (prodW p) 0 ≤ 1) ∧
        (∀ (p : Fin k) (x : Fin n) (y : Fin m),
          b2z ((wiresOf gs (oneEach x y)).getD (prodW p) false) =
            let qp := qs.get ⟨p.val, by omega⟩
            (qp.1 x + qp.2.2.2 y) * (qp.2.2.1 x + qp.2.1 y)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], Fin.elim0, ⟨fun j hj => by simp at hj, fun _ h => by cases h⟩, rfl,
        fun p => Fin.elim0 p, fun p => Fin.elim0 p, fun p => Fin.elim0 p⟩
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨gs, prodW, hgood, hcnt, hlt, hdep, heval⟩
      let qk := qs.get ⟨k, by omega⟩
      rcases hbuild_aff gs qk.1 qk.2.2.2 hgood with
        ⟨gs1, w1, hlen1, hgood1, hcnt1, hw1, hdep1, hdpref1, hval1⟩
      rcases hbuild_aff gs1 qk.2.2.1 qk.2.1 hgood1 with
        ⟨gs2, w2, hlen2, hgood2, hcnt2, hw2, hdep2, hdpref2, hval2⟩
      have hThree := append_and2 (n + m) gs2 w1 w2 hgood2 (by omega) hw2
      let gs3 := gs2 ++ [⟨GateOp.and, [w1, w2]⟩]
      let out := (n + m) + gs2.length
      let prodW' : Fin (k + 1) → ℕ :=
        fun p => if hp : p.val < k then prodW ⟨p.val, hp⟩ else out
      refine ⟨gs3, prodW', hThree.2.1, by rw [hThree.2.2.1, hcnt2, hcnt1, hcnt], ?_, ?_, ?_⟩
      · intro p
        by_cases hp : p.val < k
        · simp only [prodW', dif_pos hp]
          have h1 := hlt ⟨p.val, hp⟩
          have hlen3 : gs3.length = gs2.length + 1 := by simp [gs3]
          omega
        · simp only [prodW', dif_neg hp]; exact hThree.2.2.2.1
      · intro p
        by_cases hp : p.val < k
        · simp only [prodW', dif_pos hp]
          rw [hThree.2.2.2.2.2.1 _ (by have := hlt ⟨p.val, hp⟩; omega),
            hdpref2 _ (by have := hlt ⟨p.val, hp⟩; omega),
            hdpref1 _ (hlt ⟨p.val, hp⟩)]
          exact hdep ⟨p.val, hp⟩
        · simp only [prodW', dif_neg hp]
          rw [hThree.2.2.2.2.1, hdpref2 w1 hw1, hdep1, hdep2]
          decide
      · intro p x y
        by_cases hp : p.val < k
        · simp only [prodW', dif_pos hp]
          have hltp := hlt ⟨p.val, hp⟩
          rw [(hThree.2.2.2.2.2.2 (oneEach x y) (oneEach_length x y)).1 _ (by omega),
            (hval2 x y).1 _ (by omega), (hval1 x y).1 _ hltp]
          exact heval ⟨p.val, hp⟩ x y
        · have hpk : p.val = k := by omega
          simp only [prodW', dif_neg hp]
          rw [(hThree.2.2.2.2.2.2 (oneEach x y) (oneEach_length x y)).2, b2z_and,
            (hval2 x y).1 w1 hw1, (hval1 x y).2, (hval2 x y).2]
          have hqeq : qs.get ⟨p.val, by omega⟩ = qk := by
            dsimp only [qk]; congr 1; exact Fin.ext (by dsimp only; omega)
          rw [hqeq]
  rcases hstage1 qs.length le_rfl with ⟨gs1, prodW, hgood1, hcnt1, hplt1, hpdep1, hpeval1⟩
  have hstage2 : ∀ (k : ℕ) (hk : k ≤ q),
      ∃ (gs : List Gate) (tap : Fin k → ℕ),
        gs1.length ≤ gs.length ∧
        goodGates (n + m) gs ∧
        gs.countP nonlinear = qs.length ∧
        (∀ p : Fin qs.length, (depthsOf (n + m) gs).getD (prodW p) 0 ≤ 1) ∧
        (∀ (p : Fin qs.length) (x : Fin n) (y : Fin m),
          b2z ((wiresOf gs (oneEach x y)).getD (prodW p) false) =
            let qp := qs.get p
            (qp.1 x + qp.2.2.2 y) * (qp.2.2.1 x + qp.2.1 y)) ∧
        (∀ j : Fin k, tap j < (n + m) + gs.length) ∧
        (∀ j : Fin k, (depthsOf (n + m) gs).getD (tap j) 0 ≤ 1) ∧
        (∀ (j : Fin k) (x : Fin n) (y : Fin m),
          b2z ((wiresOf gs (oneEach x y)).getD (tap j) false) =
            α ⟨j.val, by omega⟩ x + β ⟨j.val, by omega⟩ y +
              ∑ p : Fin qs.length, mask ⟨j.val, by omega⟩ p * evalQuad (qs.get p) x y) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨gs1, Fin.elim0, le_rfl, hgood1, hcnt1, hpdep1, hpeval1,
        fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨gs, tap, hlen, hgood, hcnt, hpdep, hpeval, htlt, htdep, hteval⟩
      let jk : Fin q := ⟨k, by omega⟩
      let α' : Fin n → F := fun x =>
        α jk x + ∑ p : Fin qs.length, mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)
      let β' : Fin m → F := fun y =>
        β jk y + ∑ p : Fin qs.length, mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)
      rcases hbuild_aff gs α' β' hgood with
        ⟨gsA, wA, hlenA, hgoodA, hcntA, hwA, hdepA, hdprefA, hvalA⟩
      let maskPs : List (Fin qs.length) :=
        (List.finRange qs.length).filter (fun p => decide (mask jk p = 1))
      let inW : List ℕ := wA :: maskPs.map prodW
      have hinW_lt : ∀ u ∈ inW, u < (n + m) + gsA.length := by
        intro u hu
        simp only [inW, List.mem_cons, List.mem_map] at hu
        rcases hu with rfl | ⟨p, _, rfl⟩
        · exact hwA
        · have := hplt1 p; omega
      have hinW_dep : ∀ u ∈ inW, (depthsOf (n + m) gsA).getD u 0 ≤ 1 := by
        intro u hu
        simp only [inW, List.mem_cons, List.mem_map] at hu
        rcases hu with rfl | ⟨p, _, rfl⟩
        · omega
        · rw [hdprefA (prodW p) (by have := hplt1 p; omega)]
          exact hpdep p
      rcases exists_xorList (n + m) gsA inW 1 hgoodA hinW_lt hinW_dep with
        ⟨gsB, out, hlenB, hgoodB, hcntB, houtB, hdepB, hdprefB, hvalB⟩
      let tap' : Fin (k + 1) → ℕ := fun j => if hj : j.val < k then tap ⟨j.val, hj⟩ else out
      refine ⟨gsB, tap', by omega, hgoodB, by rw [hcntB, hcntA, hcnt], ?_, ?_, ?_, ?_, ?_⟩
      · intro p
        have hltp := hplt1 p
        rw [hdprefB (prodW p) (by omega), hdprefA (prodW p) (by omega)]
        exact hpdep p
      · intro p x y
        have hltp := hplt1 p
        rw [(hvalB (oneEach x y) (oneEach_length x y)).1 (prodW p) (by omega),
          (hvalA x y).1 (prodW p) (by omega)]
        exact hpeval p x y
      · intro j
        by_cases hj : j.val < k
        · simp only [tap', dif_pos hj]; have := htlt ⟨j.val, hj⟩; omega
        · simp only [tap', dif_neg hj]; exact houtB
      · intro j
        by_cases hj : j.val < k
        · simp only [tap', dif_pos hj]
          have hltj := htlt ⟨j.val, hj⟩
          rw [hdprefB _ (by omega), hdprefA _ hltj]
          exact htdep ⟨j.val, hj⟩
        · simp only [tap', dif_neg hj]; exact hdepB
      · intro j x y
        by_cases hj : j.val < k
        · simp only [tap', dif_pos hj]
          have hltj := htlt ⟨j.val, hj⟩
          rw [(hvalB (oneEach x y) (oneEach_length x y)).1 _ (by omega),
            (hvalA x y).1 _ hltj]
          exact hteval ⟨j.val, hj⟩ x y
        · have hjk_eq : (⟨j.val, by omega⟩ : Fin q) = jk := Fin.ext (by dsimp only [jk]; omega)
          simp only [tap', dif_neg hj, hjk_eq]
          rw [(hvalB (oneEach x y) (oneEach_length x y)).2]
          simp only [inW, List.map_cons, List.sum_cons, List.map_map]
          rw [(hvalA x y).2]
          have hmap_eq :
              maskPs.map ((fun u => b2z ((wiresOf gsA (oneEach x y)).getD u false)) ∘ prodW) =
              maskPs.map (fun p =>
                let qp := qs.get p
                (qp.1 x + qp.2.2.2 y) * (qp.2.2.1 x + qp.2.1 y)) := by
            refine List.map_congr_left fun p _ => ?_
            dsimp only [Function.comp]
            have hltp := hplt1 p
            rw [(hvalA x y).1 (prodW p) (by omega)]
            exact hpeval p x y
          rw [hmap_eq]
          have hnodup : maskPs.Nodup := (List.nodup_finRange qs.length).filter _
          have htoF : maskPs.toFinset =
              Finset.univ.filter (fun p : Fin qs.length => mask jk p = 1) := by
            ext p; simp [maskPs]
          rw [← List.sum_toFinset _ hnodup, htoF]
          have hfilt_sum : ∑ p ∈ Finset.univ.filter (fun p : Fin qs.length => mask jk p = 1),
              ((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y) =
              ∑ p : Fin qs.length, mask jk p *
                (((qs.get p).1 x + (qs.get p).2.2.2 y) *
                  ((qs.get p).2.2.1 x + (qs.get p).2.1 y)) := by
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
              (fun p : Fin qs.length => mask jk p = 1)]
            have hleft : ∑ p ∈ Finset.univ.filter (fun p : Fin qs.length => mask jk p = 1),
                mask jk p * (((qs.get p).1 x + (qs.get p).2.2.2 y) *
                  ((qs.get p).2.2.1 x + (qs.get p).2.1 y)) =
                ∑ p ∈ Finset.univ.filter (fun p : Fin qs.length => mask jk p = 1),
                  ((qs.get p).1 x + (qs.get p).2.2.2 y) *
                    ((qs.get p).2.2.1 x + (qs.get p).2.1 y) := by
              refine Finset.sum_congr rfl fun p hp => ?_
              rw [(Finset.mem_filter.mp hp).2, one_mul]
            have hright : ∑ p ∈ Finset.univ.filter (fun p : Fin qs.length => ¬ mask jk p = 1),
                mask jk p * (((qs.get p).1 x + (qs.get p).2.2.2 y) *
                  ((qs.get p).2.2.1 x + (qs.get p).2.1 y)) = 0 := by
              apply Finset.sum_eq_zero
              intro p hp
              have hne : mask jk p ≠ 1 := (Finset.mem_filter.mp hp).2
              have h0 : mask jk p = 0 := by
                rcases zmod2_cases (mask jk p) with h | h; exact h; exact (hne h).elim
              rw [h0, zero_mul]
            rw [hleft, hright, add_zero]
          rw [hfilt_sum]
          dsimp only [α', β']
          have hsum_eq :
              (∑ p : Fin qs.length, mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)) +
              (∑ p : Fin qs.length, mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)) +
              ∑ p : Fin qs.length, mask jk p *
                (((qs.get p).1 x + (qs.get p).2.2.2 y) *
                  ((qs.get p).2.2.1 x + (qs.get p).2.1 y)) =
              ∑ p : Fin qs.length, mask jk p * evalQuad (qs.get p) x y := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p _ => ?_
            dsimp only [evalQuad]
            have h1 := zmod2_add_self (mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x))
            have hTwo := zmod2_add_self (mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y))
            calc mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x) +
                  mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y) +
                  mask jk p * (((qs.get p).1 x + (qs.get p).2.2.2 y) *
                    ((qs.get p).2.2.1 x + (qs.get p).2.1 y))
                = (mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x) +
                    mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)) +
                  (mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y) +
                    mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)) +
                  mask jk p * ((qs.get p).1 x * (qs.get p).2.1 y +
                    (qs.get p).2.2.1 x * (qs.get p).2.2.2 y) := by ring
              _ = mask jk p * ((qs.get p).1 x * (qs.get p).2.1 y +
                    (qs.get p).2.2.1 x * (qs.get p).2.2.2 y) := by
                    rw [h1, hTwo, zero_add, zero_add]
          calc (α jk x + ∑ p : Fin qs.length, mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)) +
                (β jk y + ∑ p : Fin qs.length, mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)) +
                ∑ p : Fin qs.length, mask jk p *
                  (((qs.get p).1 x + (qs.get p).2.2.2 y) *
                    ((qs.get p).2.2.1 x + (qs.get p).2.1 y))
              = α jk x + β jk y +
                  ((∑ p : Fin qs.length, mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)) +
                    (∑ p : Fin qs.length, mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)) +
                    ∑ p : Fin qs.length, mask jk p *
                      (((qs.get p).1 x + (qs.get p).2.2.2 y) *
                        ((qs.get p).2.2.1 x + (qs.get p).2.1 y))) := by ring
            _ = α jk x + β jk y + ∑ p : Fin qs.length, mask jk p * evalQuad (qs.get p) x y := by
                  rw [hsum_eq]
  rcases hstage2 q le_rfl with ⟨gs2, tap, _, hgood2, hcnt2, _, _, _, htdep2, hteval2⟩
  refine ⟨⟨gs2, 0⟩, tap, hgood2.1, hgood2.2, le_of_eq hcnt2, fun j => ⟨htdep2 j, hteval2 j⟩⟩

lemma matrix_rank_decomp {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (B : Matrix α β F) :
    ∃ (a : Fin B.rank → α → F) (b : Fin B.rank → β → F),
      B = ∑ k : Fin B.rank, Matrix.vecMulVec (a k) (b k) := by
  let bas := Module.finBasis F (LinearMap.range B.mulVecLin)
  let a : Fin B.rank → α → F := fun k => (bas k).1
  let b : Fin B.rank → β → F := fun k j =>
    bas.repr ⟨B.mulVecLin (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩ k
  refine ⟨a, b, ?_⟩
  ext i j
  have hcol : B.mulVecLin (Pi.single j 1) = ∑ k : Fin B.rank, (b k j) • (a k) := by
    have h1 := bas.sum_repr ⟨B.mulVecLin (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩
    have hTwo := congrArg Subtype.val h1
    rw [Submodule.coe_sum] at hTwo
    exact hTwo.symm
  have hi := congrFun hcol i
  have hlhs : B.mulVecLin (Pi.single j 1) i = B i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hlhs] at hi
  rw [hi, Matrix.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.vecMulVec_apply, mul_comm]

private lemma twoTerms {d r : ℕ} (a b : Fin r → Fin d → F) (hr : r ≤ 2) :
    ∃ u : Quad d d, ∀ i j, evalQuad u i j = ∑ p, a p i * b p j := by
  match r with
  | 0 => exact ⟨(0, 0, 0, 0), fun i j => by simp [evalQuad]⟩
  | 1 => exact ⟨(a 0, b 0, 0, 0), fun i j => by simp [evalQuad]⟩
  | 2 => exact ⟨(a 0, b 0, a 1, b 1), fun i j => by simp [evalQuad, Fin.sum_univ_two]⟩
  | k + 3 => omega

private lemma toQuad {d : ℕ} (A : Matrix (Fin d) (Fin d) F) (h : A.rank ≤ 2) :
    ∃ u : Quad d d, ∀ i j, evalQuad u i j = A i j := by
  obtain ⟨a, b, hab⟩ := matrix_rank_decomp A
  obtain ⟨u, hu⟩ := twoTerms a b h
  refine ⟨u, fun i j => ?_⟩
  simpa only [hu, Matrix.sum_apply, Matrix.vecMulVec_apply] using
    (congrArg (fun (M : Matrix (Fin d) (Fin d) F) => M i j) hab.symm)

private def padQuad {d : ℕ} (u : Quad d d) : Quad (d + 1) (d + 1) :=
  (Fin.cases 0 u.1, Fin.cases 0 u.2.1, Fin.cases 0 u.2.2.1, Fin.cases 0 u.2.2.2)

lemma synth {d : ℕ} {α ι κ : Type} [Fintype α] [Fintype ι] [Fintype κ]
    (coord : α ≃ Fin d) (R : ι → Matrix α α F) (Target : κ → Matrix α α F)
    (hr : ∀ i, (R i).rank ≤ 2) (hT : ∀ k, Target k ∈ Submodule.span F (Set.range R)) :
    ∃ (C : Circuit) (tap : κ → ℕ), ReadsBack ((d + 1) + (d + 1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ Fintype.card ι ∧
      ∀ k, (depths ((d + 1) + (d + 1)) C).getD (tap k) 0 ≤ 1 ∧
        Represents (mkTable coord (Target k)) ⟨C.gates, tap k⟩ := by
  classical
  have hcoef := fun k => (Submodule.mem_span_range_iff_exists_fun F).mp (hT k)
  choose c hc using hcoef
  have hq (p : ι) : ∃ u : Quad d d, ∀ i j, evalQuad u i j =
      R p (coord.symm i) (coord.symm j) := by
    apply toQuad ((R p).submatrix coord.symm coord.symm)
    simpa only [Matrix.rank_submatrix] using hr p
  choose u hu using hq
  let e := Fintype.equivFin ι
  let ek := Fintype.equivFin κ
  let qs := List.ofFn (fun p : Fin (Fintype.card ι) => padQuad (u (e.symm p)))
  have hlen : qs.length = Fintype.card ι := by simp [qs]
  let eqs : Fin qs.length ≃ ι := (finCongr hlen).trans e.symm
  have hget (p : Fin qs.length) : qs.get p = padQuad (u (eqs p)) := by
    simp [qs, eqs, List.get_eq_getElem, finCongr]
    rfl
  obtain ⟨C, tap, hrb, hfan, hcnt, hout⟩ := synth_depth1_quads (d + 1) (d + 1) (Fintype.card κ) qs
    (fun k p => c (ek.symm k) (eqs p)) (fun _ _ => 0) (fun _ _ => 0)
  refine ⟨C, fun k => tap (ek k), hrb, hfan, hcnt.trans hlen.le, fun k =>
    ⟨(hout (ek k)).1, fun x y => ?_⟩⟩
  apply b2z_inj
  change b2z ((wiresOf C.gates (oneEach x y)).getD (tap (ek k)) false) =
    b2z (mkTable coord (Target k) x y)
  rw [(hout (ek k)).2 x y]
  simp only [zero_add, Equiv.symm_apply_apply, hget]
  rw [eqs.sum_comp (fun p => c k p * evalQuad (padQuad (u p)) x y)]
  cases x using Fin.cases with
  | zero => simp [padQuad, evalQuad, mkTable, b2z]
  | succ i =>
    cases y using Fin.cases with
    | zero => simp [padQuad, evalQuad, mkTable, b2z]
    | succ j =>
      simp only [mkTable, Fin.cases_succ, b2z_decide_ne_zero]
      have huv (p : ι) : evalQuad (padQuad (u p)) i.succ j.succ =
          R p (coord.symm i) (coord.symm j) := by
        simpa only [padQuad, evalQuad, Fin.cases_succ] using hu p i j
      simpa only [huv, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        using congrArg (fun (M : Matrix α α F) => M (coord.symm i) (coord.symm j)) (hc k)


def sel {a b : Type} [DecidableEq b] (e : a → b) : Matrix b a F :=
  Matrix.of fun i j => if i = e j then 1 else 0

def layer {a b t : Type} [Fintype a] [Fintype b] [DecidableEq t]
    (e : a → t) (g : b → t) : Matrix a b F →ₗ[F] Matrix t t F where
  toFun X := sel e * X * (sel g).transpose
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

lemma layer_rank {a b t : Type} [Fintype a] [Fintype b] [Fintype t] [DecidableEq t]
    (e : a → t) (g : b → t) (X : Matrix a b F) : (layer e g X).rank ≤ X.rank := by
  classical
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

def symLayer {a b t : Type} [Fintype a] [Fintype b] [DecidableEq t]
    (e : a → t) (g : b → t) : Matrix a b F →ₗ[F] Matrix t t F :=
  layer e g + (Matrix.transposeLinearEquiv t t F F).toLinearMap.comp (layer e g)

lemma symLayer_apply {a b t : Type} [Fintype a] [Fintype b] [DecidableEq t]
    (e : a → t) (g : b → t) (X : Matrix a b F) (i j : t) :
    symLayer e g X i j = layer e g X i j + layer e g X j i := rfl

lemma symLayer_rank {a b t : Type} [Fintype a] [Fintype b] [Fintype t] [DecidableEq t]
    (e : a → t) (g : b → t) (X : Matrix a b F) (h : X.rank ≤ 1) :
    (symLayer e g X).rank ≤ 2 := by
  classical
  change (layer e g X + (layer e g X).transpose).rank ≤ 2
  refine (matrix_rank_add_le _ _).trans ?_
  rw [Matrix.rank_transpose]
  have := (layer_rank e g X).trans h
  omega

lemma layer_apply {a b t : Type} [Fintype a] [Fintype b] [DecidableEq t]
    (e : a → t) (g : b → t) (X : Matrix a b F) (i j : t) :
    layer e g X i j = ∑ p : a, ∑ q : b, if i = e p ∧ j = g q then X p q else 0 := by
  simp only [layer, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, sel,
    Matrix.transpose_apply, Matrix.of_apply]
  calc ∑ q : b, (∑ p : a, (if i = e p then (1 : F) else 0) * X p q) *
          (if j = g q then (1 : F) else 0)
      = ∑ q : b, ∑ p : a, (if i = e p then (1 : F) else 0) * X p q *
          (if j = g q then (1 : F) else 0) :=
        Finset.sum_congr rfl fun q _ => Finset.sum_mul ..
    _ = ∑ p : a, ∑ q : b, (if i = e p then (1 : F) else 0) * X p q *
          (if j = g q then (1 : F) else 0) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        split_ifs <;> simp_all

private lemma finrank_map_eq_of_inj {V W : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F V] [FiniteDimensional F W]
    {f : V →ₗ[F] W} (hf : Function.Injective f) (S : Submodule F V) :
    Module.finrank F (S.map f) = Module.finrank F S := by
  have h : LinearMap.range (f.comp S.subtype) = S.map f := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← h]
  exact LinearMap.finrank_range_of_inj (hf.comp Subtype.val_injective)

lemma fromBlocks_top_eq_layer {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I F) :
    Matrix.fromBlocks A (0 : Matrix I I F) 0 0 = layer Sum.inl Sum.inl A := by
  ext (i | i) (j | j)
  · simp only [Matrix.fromBlocks_apply₁₁, layer_apply, Sum.inl.injEq]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro q _ hq; simp [Ne.symm hq]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · intro p _ hp
      apply Finset.sum_eq_zero; intro q _; simp [Ne.symm hp]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · simp [layer_apply, Matrix.fromBlocks]
  · simp [layer_apply, Matrix.fromBlocks]
  · simp [layer_apply, Matrix.fromBlocks]

private lemma card_submodule_eq_two_pow {α : Type} [Fintype α] [DecidableEq α]
    (W : Submodule F (α → F)) [DecidablePred (fun v : α → F => v ∈ W)] :
    (Finset.univ.filter (fun v : α → F => v ∈ W)).card = 2 ^ Module.finrank F W := by
  classical
  let b := Module.finBasis F W
  have hcard : Fintype.card W = 2 ^ Module.finrank F W := by
    rw [Fintype.card_congr b.equivFun.toEquiv, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [← hcard, ← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun x => ⟨x.val, (Finset.mem_filter.mp x.property).2⟩
      invFun := fun x => ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private lemma exists_disjoint_subspace {α : Type} [Fintype α] [DecidableEq α]
    (A : (α → F) →ₗ[F] (α → F)) (hA : Function.Bijective A)
    (h1A : Function.Bijective ((LinearMap.id : (α → F) →ₗ[F] (α → F)) + A))
    (k : ℕ) (hk : 2 * k ≤ Fintype.card α) :
    ∃ S : Submodule F (α → F), Module.finrank F S = k ∧ S ⊓ S.map A = ⊥ := by
  classical
  induction k with
  | zero =>
    refine ⟨⊥, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨S, hSdim, hSdisj⟩ := ih (by omega)
    let W1 : Submodule F (α → F) := S ⊔ S.map A
    let eA := LinearEquiv.ofBijective A hA
    let e1A := LinearEquiv.ofBijective ((LinearMap.id : (α → F) →ₗ[F] (α → F)) + A) h1A
    let W2 : Submodule F (α → F) := W1.comap A
    let W3 : Submodule F (α → F) := W1.comap ((LinearMap.id : (α → F) →ₗ[F] (α → F)) + A)
    have hSA_dim : Module.finrank F (S.map A) = k := by
      rw [finrank_map_eq_of_inj hA.1 S, hSdim]
    have hW1_dim : Module.finrank F W1 = 2 * k := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq S (S.map A)
      rw [hSdisj, finrank_bot, add_zero, hSdim, hSA_dim] at h
      dsimp only [W1]
      omega
    have hW2_eq : W2 = W1.map eA.symm.toLinearMap := by
      ext v
      simp only [W2, Submodule.mem_comap, Submodule.mem_map, LinearEquiv.coe_coe]
      constructor
      · intro hv
        refine ⟨A v, hv, ?_⟩
        exact eA.symm_apply_apply v
      · rintro ⟨w, hw, rfl⟩
        change eA (eA.symm w) ∈ W1
        rwa [eA.apply_symm_apply]
    have hW3_eq : W3 = W1.map e1A.symm.toLinearMap := by
      ext v
      simp only [W3, Submodule.mem_comap, Submodule.mem_map, LinearEquiv.coe_coe]
      constructor
      · intro hv
        refine ⟨((LinearMap.id : (α → F) →ₗ[F] (α → F)) + A) v, hv, ?_⟩
        exact e1A.symm_apply_apply v
      · rintro ⟨w, hw, rfl⟩
        change e1A (e1A.symm w) ∈ W1
        rwa [e1A.apply_symm_apply]
    have hW2_dim : Module.finrank F W2 = 2 * k := by
      rw [hW2_eq, finrank_map_eq_of_inj eA.symm.injective W1, hW1_dim]
    have hW3_dim : Module.finrank F W3 = 2 * k := by
      rw [hW3_eq, finrank_map_eq_of_inj e1A.symm.injective W1, hW1_dim]
    let B1 := Finset.univ.filter (fun v : α → F => v ∈ W1)
    let B2 := Finset.univ.filter (fun v : α → F => v ∈ W2)
    let B3 := Finset.univ.filter (fun v : α → F => v ∈ W3)
    let bad := B1 ∪ (B2 ∪ B3)
    have hbad_le : bad.card ≤ 3 * 2 ^ (2 * k) := by
      have h1 : B1.card = 2 ^ (2 * k) := by rw [← hW1_dim]; exact card_submodule_eq_two_pow W1
      have hTwo : B2.card = 2 ^ (2 * k) := by rw [← hW2_dim]; exact card_submodule_eq_two_pow W2
      have hThree : B3.card = 2 ^ (2 * k) := by rw [← hW3_dim]; exact card_submodule_eq_two_pow W3
      have hu1 := Finset.card_union_le B1 (B2 ∪ B3)
      have hu2 := Finset.card_union_le B2 B3
      dsimp only [bad]
      omega
    have hlt : bad.card < (Finset.univ : Finset (α → F)).card := by
      rw [Finset.card_univ, Fintype.card_fun, ZMod.card]
      have hpow : 4 * 2 ^ (2 * k) ≤ 2 ^ Fintype.card α := by
        calc 4 * 2 ^ (2 * k) = 2 ^ (2 * k + 2) := by ring
          _ ≤ 2 ^ Fintype.card α := Nat.pow_le_pow_right (by omega) (by omega)
      have hpos : 0 < 2 ^ (2 * k) := Nat.pos_of_ne_zero (by positivity)
      omega
    have hex : ∃ v : α → F, v ∉ bad := by
      by_contra h
      push Not at h
      have hsub : (Finset.univ : Finset (α → F)) ⊆ bad := fun v _ => h v
      have := Finset.card_le_card hsub
      omega
    obtain ⟨v, hvbad⟩ := hex
    have hv1 : v ∉ W1 := fun h => hvbad (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have hv2 : v ∉ W2 := fun h => hvbad (Finset.mem_union_right _
      (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
    have hv3 : v ∉ W3 := fun h => hvbad (Finset.mem_union_right _
      (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
    have hvS : v ∉ S := fun h => hv1 (Submodule.mem_sup_left h)
    have hv0 : v ≠ 0 := fun h => hvS (h ▸ S.zero_mem)
    let S' : Submodule F (α → F) := S ⊔ Submodule.span F {v}
    have hinf_v : S ⊓ Submodule.span F {v} = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxS : x ∈ S := hx.1
      have hxv : x ∈ Submodule.span F {v} := hx.2
      rw [Submodule.mem_span_singleton] at hxv
      obtain ⟨c, rfl⟩ := hxv
      rcases zmod2_cases c with rfl | rfl
      · simp
      · simp only [one_smul] at hxS
        exact (hvS hxS).elim
    have hS'_dim : Module.finrank F S' = k + 1 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span F {v})
      rw [hinf_v, finrank_bot, add_zero, hSdim, finrank_span_singleton hv0] at h
      exact h
    have hS'_disj : S' ⊓ S'.map A = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx1 : x ∈ S ⊔ Submodule.span F {v} := hx.1
      have hx2 : x ∈ S'.map A := hx.2
      rw [Submodule.mem_sup] at hx1
      obtain ⟨s1, hs1, y1, hy1, rfl⟩ := hx1
      rw [Submodule.mem_span_singleton] at hy1
      obtain ⟨c1, rfl⟩ := hy1
      rw [Submodule.mem_map] at hx2
      obtain ⟨u, hu, huA⟩ := hx2
      rw [Submodule.mem_sup] at hu
      obtain ⟨s2, hs2, y2, hy2, rfl⟩ := hu
      rw [Submodule.mem_span_singleton] at hy2
      obtain ⟨c2, rfl⟩ := hy2
      rw [map_add, map_smul] at huA
      rcases zmod2_cases c1 with rfl | rfl <;> rcases zmod2_cases c2 with rfl | rfl
      · simp only [zero_smul, add_zero] at huA ⊢
        have hmem : s1 ∈ S ⊓ S.map A := ⟨hs1, ⟨s2, hs2, huA⟩⟩
        rw [hSdisj] at hmem
        exact hmem
      · exfalso
        simp only [zero_smul, add_zero, one_smul] at huA
        have hAv : A v = s1 + A s2 := by
          calc A v = (A s2 + A s2) + A v := by rw [vec_add_self, zero_add]
            _ = A s2 + (A s2 + A v) := by abel
            _ = A s2 + s1 := by rw [huA]
            _ = s1 + A s2 := add_comm _ _
        have hmem : A v ∈ W1 := by
          rw [hAv]
          exact Submodule.add_mem_sup hs1 ⟨s2, hs2, rfl⟩
        exact hv2 hmem
      · exfalso
        simp only [one_smul, zero_smul, add_zero] at huA
        have hv_eq : v = s1 + A s2 := by
          calc v = (s1 + s1) + v := by rw [vec_add_self, zero_add]
            _ = s1 + (s1 + v) := by abel
            _ = s1 + A s2 := by rw [← huA]
        have hmem : v ∈ W1 := by
          rw [hv_eq]
          exact Submodule.add_mem_sup hs1 ⟨s2, hs2, rfl⟩
        exact hv1 hmem
      · exfalso
        simp only [one_smul] at huA
        have hvAv : v + A v = s1 + A s2 := by
          calc v + A v = (s1 + s1) + v + A v := by rw [vec_add_self, zero_add]
            _ = s1 + ((s1 + v) + A v) := by abel
            _ = s1 + ((A s2 + A v) + A v) := by rw [← huA]
            _ = s1 + (A s2 + (A v + A v)) := by abel
            _ = s1 + A s2 := by rw [vec_add_self, add_zero]
        have hmem : ((LinearMap.id : (α → F) →ₗ[F] (α → F)) + A) v ∈ W1 := by
          change v + A v ∈ W1
          rw [hvAv]
          exact Submodule.add_mem_sup hs1 ⟨s2, hs2, rfl⟩
        exact hv3 hmem
    exact ⟨S', hS'_dim, hS'_disj⟩

private lemma plane_three_decomp {α : Type} [Fintype α] [DecidableEq α]
    (U W : Matrix α α F) (hU : U.rank = Fintype.card α)
    (hW : W.rank = Fintype.card α) (hUW : (U + W).rank = Fintype.card α) :
    ∃ P1 P2 P3 : Matrix α α F, P1 + P2 = U ∧ P2 + P3 = W ∧
      P1.rank + P2.rank + P3.rank ≤ (3 * Fintype.card α + Fintype.card α % 2) / 2 := by
  classical
  have hbij : ∀ M : Matrix α α F, M.rank = Fintype.card α → Function.Bijective M.mulVecLin := by
    intro M hM
    have hsur : Function.Surjective M.mulVecLin :=
      Matrix.mulVec_surjective_iff_rank_eq_card.mpr hM
    exact ⟨LinearMap.injective_iff_surjective.mpr hsur, hsur⟩
  have hUb := hbij U hU
  have hWb := hbij W hW
  have hUWb := hbij (U + W) hUW
  let eU := LinearEquiv.ofBijective U.mulVecLin hUb
  let A : (α → F) →ₗ[F] (α → F) := eU.symm.toLinearMap.comp W.mulVecLin
  have hA : Function.Bijective A := eU.symm.bijective.comp hWb
  have h1A_eq : (LinearMap.id : (α → F) →ₗ[F] (α → F)) + A =
      eU.symm.toLinearMap.comp (U + W).mulVecLin := by
    apply LinearMap.ext
    intro v
    change v + eU.symm (W.mulVecLin v) = eU.symm ((U + W).mulVecLin v)
    rw [Matrix.mulVecLin_add, LinearMap.add_apply, map_add]
    have heq : eU.symm (U.mulVecLin v) = v := eU.symm_apply_apply v
    rw [heq]
  have h1A : Function.Bijective ((LinearMap.id : (α → F) →ₗ[F] (α → F)) + A) := by
    rw [h1A_eq]
    exact eU.symm.bijective.comp hUWb
  let k := Fintype.card α / 2
  obtain ⟨S, hSdim, hSdisj⟩ := exists_disjoint_subspace A hA h1A k (by omega)
  let T : Submodule F (α → F) := S.map A
  have hTdim : Module.finrank F T = k := by
    rw [finrank_map_eq_of_inj hA.1 S, hSdim]
  obtain ⟨C, hC⟩ := (S ⊔ T).exists_isCompl
  have hS_compl : IsCompl S (T ⊔ C) := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have hxS : x ∈ S := hx.1
      have hxTC : x ∈ T ⊔ C := hx.2
      rw [Submodule.mem_sup] at hxTC
      obtain ⟨t, ht, c, hc, hxtc⟩ := hxTC
      have hcST : c ∈ S ⊔ T := by
        have hceq : c = x + t := by
          calc c = (t + t) + c := by rw [vec_add_self, zero_add]
            _ = t + (t + c) := by abel
            _ = t + x := by rw [hxtc]
            _ = x + t := add_comm _ _
        rw [hceq]
        exact Submodule.add_mem_sup hxS ht
      have hc0 : c = 0 := by
        have hmem : c ∈ (S ⊔ T) ⊓ C := ⟨hcST, hc⟩
        rw [hC.inf_eq_bot] at hmem
        exact hmem
      rw [hc0, add_zero] at hxtc
      have hxST : x ∈ S ⊓ T := ⟨hxS, hxtc ▸ ht⟩
      rw [hSdisj] at hxST
      exact hxST
    · rw [codisjoint_iff, ← sup_assoc, hC.sup_eq_top]
  have hT_compl : IsCompl T (S ⊔ C) := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have hxT : x ∈ T := hx.1
      have hxSC : x ∈ S ⊔ C := hx.2
      rw [Submodule.mem_sup] at hxSC
      obtain ⟨s, hs, c, hc, hxsc⟩ := hxSC
      have hcST : c ∈ S ⊔ T := by
        have hceq : c = s + x := by
          calc c = (s + s) + c := by rw [vec_add_self, zero_add]
            _ = s + (s + c) := by abel
            _ = s + x := by rw [hxsc]
        rw [hceq]
        exact Submodule.add_mem_sup hs hxT
      have hc0 : c = 0 := by
        have hmem : c ∈ (S ⊔ T) ⊓ C := ⟨hcST, hc⟩
        rw [hC.inf_eq_bot] at hmem
        exact hmem
      rw [hc0, add_zero] at hxsc
      have hxST : x ∈ S ⊓ T := ⟨hxsc ▸ hs, hxT⟩
      rw [hSdisj] at hxST
      exact hxST
    · rw [codisjoint_iff, ← sup_assoc, sup_comm T S, hC.sup_eq_top]
  let pS := S.projection (T ⊔ C) hS_compl
  let pT := T.projection (S ⊔ C) hT_compl
  let Xlin : (α → F) →ₗ[F] (α → F) := A.comp pS + pT
  let X : Matrix α α F := LinearMap.toMatrix' Xlin
  have hXlin : X.mulVecLin = Xlin := Matrix.toLin'_toMatrix' Xlin
  let P2 : Matrix α α F := U * X
  let P1 : Matrix α α F := U + P2
  let P3 : Matrix α α F := W + P2
  have hpS_mem : ∀ v : α → F, pS v ∈ S := by
    intro v
    have hv : v ∈ S ⊔ (T ⊔ C) := by rw [hS_compl.sup_eq_top]; trivial
    obtain ⟨s, hs, tc, htc, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, Submodule.projection_apply_of_mem_left hS_compl hs,
      Submodule.projection_apply_of_mem_right hS_compl htc, add_zero]
    exact hs
  have hpT_mem : ∀ v : α → F, pT v ∈ T := by
    intro v
    have hv : v ∈ T ⊔ (S ⊔ C) := by rw [hT_compl.sup_eq_top]; trivial
    obtain ⟨t, ht, sc, hsc, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, Submodule.projection_apply_of_mem_left hT_compl ht,
      Submodule.projection_apply_of_mem_right hT_compl hsc, add_zero]
    exact ht
  have hX_range : LinearMap.range Xlin ≤ T := by
    rintro _ ⟨v, rfl⟩
    apply T.add_mem
    · exact ⟨pS v, hpS_mem v, rfl⟩
    · exact hpT_mem v
  have hP2_rank : P2.rank ≤ k := by
    refine (Matrix.rank_mul_le_right U X).trans ?_
    change Module.finrank F (LinearMap.range X.mulVecLin) ≤ k
    rw [hXlin, ← hTdim]
    exact Submodule.finrank_mono hX_range
  have hP1_ker : T ≤ LinearMap.ker P1.mulVecLin := by
    intro t ht
    rw [LinearMap.mem_ker]
    have hXt : X.mulVecLin t = t := by
      rw [hXlin]
      change A (pS t) + pT t = t
      have hpS : pS t = 0 :=
        Submodule.projection_apply_of_mem_right hS_compl (Submodule.mem_sup_left ht)
      have hpT : pT t = t := Submodule.projection_apply_of_mem_left hT_compl ht
      rw [hpS, map_zero, zero_add, hpT]
    change (U + U * X).mulVecLin t = 0
    rw [Matrix.mulVecLin_add, LinearMap.add_apply, Matrix.mulVecLin_mul, LinearMap.comp_apply,
      hXt, vec_add_self]
  have hP1_rank : P1.rank ≤ Fintype.card α - k := by
    have hn := P1.mulVecLin.finrank_range_add_finrank_ker
    rw [Module.finrank_pi F] at hn
    have hk_le : k ≤ Module.finrank F (LinearMap.ker P1.mulVecLin) := by
      rw [← hTdim]
      exact Submodule.finrank_mono hP1_ker
    change Module.finrank F (LinearMap.range P1.mulVecLin) ≤ Fintype.card α - k
    omega
  have hP3_ker : S ≤ LinearMap.ker P3.mulVecLin := by
    intro s hs
    rw [LinearMap.mem_ker]
    have hXs : X.mulVecLin s = A s := by
      rw [hXlin]
      change A (pS s) + pT s = A s
      have hpS : pS s = s := Submodule.projection_apply_of_mem_left hS_compl hs
      have hpT : pT s = 0 :=
        Submodule.projection_apply_of_mem_right hT_compl (Submodule.mem_sup_left hs)
      rw [hpS, hpT, add_zero]
    have hUAs : U.mulVecLin (A s) = W.mulVecLin s := eU.apply_symm_apply (W.mulVecLin s)
    change (W + U * X).mulVecLin s = 0
    rw [Matrix.mulVecLin_add, LinearMap.add_apply, Matrix.mulVecLin_mul, LinearMap.comp_apply,
      hXs, hUAs, vec_add_self]
  have hP3_rank : P3.rank ≤ Fintype.card α - k := by
    have hn := P3.mulVecLin.finrank_range_add_finrank_ker
    rw [Module.finrank_pi F] at hn
    have hk_le : k ≤ Module.finrank F (LinearMap.ker P3.mulVecLin) := by
      rw [← hSdim]
      exact Submodule.finrank_mono hP3_ker
    change Module.finrank F (LinearMap.range P3.mulVecLin) ≤ Fintype.card α - k
    omega
  refine ⟨P1, P2, P3, ?_, ?_, ?_⟩
  · dsimp only [P1]; rw [add_assoc, mat_add_self, add_zero]
  · dsimp only [P3]; rw [add_comm P2, add_assoc, mat_add_self, add_zero]
  · omega

private lemma blockVec {J : Type} [Fintype J] [DecidableEq J] {B : J → Type} [∀ i, Fintype (B i)]
    (D : ∀ i, Matrix (B i) (B i) F) (v : ((i : J) × B i) → F) (i : J) (x : B i) :
    (Matrix.blockDiagonal' D).mulVec v ⟨i, x⟩ = (D i).mulVec (fun y => v ⟨i, y⟩) x := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j h
    exact Finset.sum_eq_zero fun y _ => by
      rw [Matrix.blockDiagonal'_apply_ne D _ _ h.symm, zero_mul]

private lemma blockDiag_full_rank {J : Type} [Fintype J] [DecidableEq J]
    {B : J → Type} [∀ i, Fintype (B i)]
    (D : ∀ i, Matrix (B i) (B i) F) (hD : ∀ i, (D i).rank = Fintype.card (B i)) :
    (Matrix.blockDiagonal' D).rank = Fintype.card ((i : J) × B i) := by
  apply Matrix.mulVec_surjective_iff_rank_eq_card.mp
  intro y
  have hs (i : J) : Function.Surjective (D i).mulVec :=
    Matrix.mulVec_surjective_iff_rank_eq_card.mpr (hD i)
  choose v hv using fun i : J => hs i (fun x => y ⟨i, x⟩)
  refine ⟨fun p => v p.1 p.2, ?_⟩
  funext ⟨i, x⟩
  rw [blockVec]
  exact congrFun (hv i) x


private lemma two_mul_rank_le_rank_fromBlocks {I : Type} [Fintype I]
    (A K : Matrix I I F) :
    2 * K.rank ≤ (Matrix.fromBlocks A K K.transpose (0 : Matrix I I F)).rank := by
  set X := Matrix.fromBlocks A K K.transpose (0 : Matrix I I F)
  let piBot : (I ⊕ I → F) →ₗ[F] (I → F) :=
    { toFun := fun v => v ∘ Sum.inr
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let injTop : (I → F) →ₗ[F] (I ⊕ I → F) :=
    { toFun := fun u => Sum.elim u 0
      map_add' := fun u v => by funext i; cases i <;> simp
      map_smul' := fun c u => by funext i; cases i <;> simp }
  have hinjTop : Function.Injective injTop := fun u v h => by
    funext i; exact congrFun h (Sum.inl i)
  have hinl (v : I ⊕ I → F) (i : I) :
      X.mulVec v (Sum.inl i) = A.mulVec (v ∘ Sum.inl) i + K.mulVec (v ∘ Sum.inr) i := by
    simp [X, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  have hinr (v : I ⊕ I → F) (i : I) :
      X.mulVec v (Sum.inr i) = K.transpose.mulVec (v ∘ Sum.inl) i := by
    simp [X, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  let colX := LinearMap.range X.mulVecLin
  let colK := LinearMap.range K.mulVecLin
  let colKT := LinearMap.range K.transpose.mulVecLin
  let φ : colX →ₗ[F] (I → F) := piBot.domRestrict colX
  have hrm := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : LinearMap.range φ = colKT := by
    ext y
    simp only [φ, colX, colKT, LinearMap.mem_range, LinearMap.domRestrict_apply,
      Subtype.exists, exists_prop, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      refine ⟨v ∘ Sum.inl, ?_⟩
      funext i; exact (hinr v i).symm
    · rintro ⟨u, rfl⟩
      refine ⟨X.mulVec (Sum.elim u 0), ⟨Sum.elim u 0, rfl⟩, ?_⟩
      funext i; exact hinr (Sum.elim u 0) i
  have hr : Module.finrank F (LinearMap.range φ) = K.rank := by
    rw [hrange]
    exact Matrix.rank_transpose K
  have hmem : ∀ y ∈ colK, injTop y ∈ colX := by
    rintro y ⟨u, rfl⟩
    refine ⟨Sum.elim 0 u, ?_⟩
    funext i
    cases i with
    | inl i =>
      change X.mulVec (Sum.elim 0 u) (Sum.inl i) = K.mulVec u i
      rw [hinl]
      have h0 : Sum.elim (0 : I → F) u ∘ Sum.inl = 0 := rfl
      have h1 : Sum.elim (0 : I → F) u ∘ Sum.inr = u := rfl
      rw [h0, h1, Matrix.mulVec_zero, Pi.zero_apply, zero_add]
    | inr i =>
      change X.mulVec (Sum.elim 0 u) (Sum.inr i) = 0
      rw [hinr]
      have h0 : Sum.elim (0 : I → F) u ∘ Sum.inl = 0 := rfl
      rw [h0, Matrix.mulVec_zero, Pi.zero_apply]
  let ψ : colK →ₗ[F] LinearMap.ker φ :=
    { toFun := fun y => ⟨⟨injTop y.1, hmem y.1 y.2⟩, by
        change piBot (injTop y.1) = 0; funext i; rfl⟩
      map_add' := fun x y => by ext i; cases i <;> simp [injTop]
      map_smul' := fun c x => by ext i; cases i <;> simp [injTop] }
  have hψinj : Function.Injective ψ := fun x y h =>
    Subtype.ext (hinjTop (congrArg (fun z => z.1.1) h))
  have hk : K.rank ≤ Module.finrank F (LinearMap.ker φ) :=
    LinearMap.finrank_le_finrank_of_injective hψinj
  change 2 * K.rank ≤ Module.finrank F colX
  omega


-- ===== own part: counting on a shortened code =====

private lemma shift_card_le {M N : Type} [AddCommGroup M] [AddCommGroup N] [DecidableEq N]
    (Pf : Finset M) (ψ : M → N) (v : M) (hψ : ∀ x, ψ (x + v) = ψ x + ψ v)
    (hv : ∀ x ∈ Pf, x + v ∈ Pf) (a : N) :
    (Pf.filter (fun x => ψ x = a)).card ≤ (Pf.filter (fun x => ψ x = a + ψ v)).card := by
  apply Finset.card_le_card_of_injOn (fun x => x + v)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    exact ⟨hv x hx.1, by rw [hψ, hx.2]⟩
  · intro x _ y _ h
    exact add_right_cancel h

private lemma info_set {E : Type} [Fintype E] [DecidableEq E] :
    ∀ (s : ℕ) (N : Submodule F (E → F)), s ≤ Module.finrank F N →
      ∃ J : Finset E, J.card = s ∧ ∀ u : E → F, ∃ v ∈ N, ∀ j ∈ J, v j = u j := by
  intro s
  induction s with
  | zero =>
    intro N _
    exact ⟨∅, rfl, fun u => ⟨0, N.zero_mem, fun j hj => absurd hj (Finset.notMem_empty j)⟩⟩
  | succ s ih =>
    intro N hN
    have hne : N ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hN
      omega
    obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hex : ∃ j0, x j0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (funext h)
    obtain ⟨j0, hj0⟩ := hex
    have hx1 : x j0 = 1 := (zmod2_cases (x j0)).resolve_left hj0
    have hdim : s ≤ Module.finrank F ↥(N ⊓ LinearMap.ker (LinearMap.proj j0 : (E → F) →ₗ[F] F)) := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq N
        (LinearMap.ker (LinearMap.proj j0 : (E → F) →ₗ[F] F))
      have hTwo := LinearMap.finrank_range_add_finrank_ker (LinearMap.proj j0 : (E → F) →ₗ[F] F)
      have hThree : Module.finrank F (LinearMap.range (LinearMap.proj j0 : (E → F) →ₗ[F] F)) ≤ 1 := by
        have h := Submodule.finrank_le (LinearMap.range (LinearMap.proj j0 : (E → F) →ₗ[F] F))
        rwa [Module.finrank_self] at h
      have h4 := Submodule.finrank_le (N ⊔ LinearMap.ker (LinearMap.proj j0 : (E → F) →ₗ[F] F))
      omega
    obtain ⟨J', hJ'c, hJ'⟩ := ih _ hdim
    have hj0J : j0 ∉ J' := by
      intro hmem
      obtain ⟨v, hv, hvJ⟩ := hJ' (fun _ => 1)
      have h0 : v j0 = 0 := LinearMap.mem_ker.mp hv.2
      have h1 := hvJ j0 hmem
      rw [h0] at h1
      exact zero_ne_one h1
    refine ⟨insert j0 J', by rw [Finset.card_insert_of_notMem hj0J, hJ'c], fun u => ?_⟩
    obtain ⟨v, hv, hvJ⟩ := hJ' (u + (u j0) • x)
    refine ⟨v + (u j0) • x, N.add_mem hv.1 (N.smul_mem _ hxN), ?_⟩
    intro j hj
    have h0 : v j0 = 0 := LinearMap.mem_ker.mp hv.2
    rcases Finset.mem_insert.mp hj with hjj | hjj
    · rw [hjj]
      show v j0 + u j0 * x j0 = u j0
      rw [h0, hx1, zero_add, mul_one]
    · show v j + u j0 * x j = u j
      rw [hvJ j hjj]
      show u j + u j0 * x j + u j0 * x j = u j
      rw [add_assoc, zmod2_add_self, add_zero]

private lemma code_count {E : Type} [Fintype E] [DecidableEq E] {l : ℕ} (d cst : Fin l → ℕ)
    (Ch : Submodule F ((E → F) × (Fin l → Fin 2 → F))) (J : Finset E)
    (h1 : ∀ x ∈ Ch, ∀ j ∈ J, x.1 j = 0)
    (hTwo : ∀ x ∈ Ch, (∑ i, if x.2 i = 0 then 0 else 2 * d i) ≤
      (Finset.univ.filter (fun j => ¬ x.1 j = 0)).card)
    (hThree : ∀ i, cst i = 0 ∨ (cst i = 2 * d i ∧ ∃ x ∈ Ch, ¬ x.2 i = 0) ∨
      (cst i = 3 * d i ∧ ∀ v : Fin 2 → F, ∃ x ∈ Ch, x.2 i = v)) :
    (∑ i, cst i) + J.card ≤ Fintype.card E := by
  classical
  let Pf : Finset ((E → F) × (Fin l → Fin 2 → F)) := Finset.univ.filter (fun x => x ∈ Ch)
  have hPf : ∀ x, x ∈ Pf ↔ x ∈ Ch := fun x => by simp [Pf]
  have hadd : ∀ v ∈ Ch, ∀ x ∈ Pf, x + v ∈ Pf := fun v hv x hx =>
    (hPf _).mpr (Ch.add_mem ((hPf x).mp hx) hv)
  have hnpos : 0 < Pf.card := Finset.card_pos.mpr ⟨0, (hPf 0).mpr Ch.zero_mem⟩
  have h11 : (1 : F) + 1 = 0 := by decide
  have hcoord : ∀ j : E, 2 * (Pf.filter (fun x => ¬ x.1 j = 0)).card +
      (if j ∈ J then Pf.card else 0) ≤ Pf.card := by
    intro j
    by_cases hj : j ∈ J
    · have hemp : Pf.filter (fun x => ¬ x.1 j = 0) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro x hx
        exact not_not.mpr (h1 x ((hPf x).mp hx) j hj)
      rw [hemp, if_pos hj]
      simp
    · rw [if_neg hj, add_zero]
      have hsplit : (Pf.filter (fun x => x.1 j = 0)).card +
          (Pf.filter (fun x => ¬ x.1 j = 0)).card = Pf.card :=
        Finset.card_filter_add_card_filter_not _
      by_cases hex : ∃ v ∈ Pf, ¬ v.1 j = 0
      · obtain ⟨v, hv, hvj⟩ := hex
        have hv1 : v.1 j = 1 := (zmod2_cases _).resolve_left hvj
        have hle := shift_card_le Pf (fun x => x.1 j) v (fun x => rfl)
          (hadd v ((hPf v).mp hv)) 1
        have e1 : Pf.filter (fun x => x.1 j = 1) = Pf.filter (fun x => ¬ x.1 j = 0) := by
          apply Finset.filter_congr
          intro x _
          rcases zmod2_cases (x.1 j) with h | h <;> simp [h]
        have e2 : Pf.filter (fun x => x.1 j = 1 + v.1 j) = Pf.filter (fun x => x.1 j = 0) := by
          apply Finset.filter_congr
          intro x _
          rw [hv1, h11]
        simp only [e1, e2] at hle
        omega
      · have hemp : Pf.filter (fun x => ¬ x.1 j = 0) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro x hx hne
          exact hex ⟨x, hx, hne⟩
        rw [hemp]
        simp
  have hW : (∑ x ∈ Pf, 2 * (Finset.univ.filter (fun j => ¬ x.1 j = 0)).card) + J.card * Pf.card ≤
      Fintype.card E * Pf.card := by
    have e : ∀ x ∈ Pf, 2 * (Finset.univ.filter (fun j => ¬ x.1 j = 0)).card =
        ∑ j : E, if ¬ x.1 j = 0 then 2 else 0 := by
      intro x _
      rw [Finset.card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> rfl
    rw [Finset.sum_congr rfl e, Finset.sum_comm]
    have e' : ∀ j : E, (∑ x ∈ Pf, if ¬ x.1 j = 0 then 2 else 0) =
        2 * (Pf.filter (fun x => ¬ x.1 j = 0)).card := by
      intro j
      rw [Finset.card_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> rfl
    have hJ : J.card * Pf.card = ∑ j : E, if j ∈ J then Pf.card else 0 := by
      simp
    rw [hJ, ← Finset.sum_add_distrib]
    calc (∑ j : E, ((∑ x ∈ Pf, if ¬ x.1 j = 0 then 2 else 0) + if j ∈ J then Pf.card else 0))
        ≤ ∑ j : E, Pf.card := Finset.sum_le_sum (fun j _ => by rw [e' j]; exact hcoord j)
      _ = Fintype.card E * Pf.card := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hcase : ∀ v : Fin 2 → F, v = 0 ∨ v = ![1, 0] ∨ v = ![0, 1] ∨ v = ![1, 1] := by decide
  have hRk : Pf.card * (∑ i, cst i) ≤ ∑ x ∈ Pf, 2 * (∑ i, if x.2 i = 0 then 0 else 2 * d i) := by
    have e : ∀ x ∈ Pf, 2 * (∑ i, if x.2 i = 0 then 0 else 2 * d i) =
        ∑ i, if x.2 i = 0 then 0 else 4 * d i := by
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs
      · rfl
      · ring
    rw [Finset.sum_congr rfl e, Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have e' : (∑ x ∈ Pf, if x.2 i = 0 then 0 else 4 * d i) =
        (Pf.filter (fun x => ¬ x.2 i = 0)).card * (4 * d i) := by
      rw [Finset.card_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x.2 i = 0
      · rw [if_pos hx, if_neg (not_not.mpr hx), zero_mul]
      · rw [if_neg hx, if_pos hx, one_mul]
    rw [e']
    have hsplit : (Pf.filter (fun x => x.2 i = 0)).card +
        (Pf.filter (fun x => ¬ x.2 i = 0)).card = Pf.card :=
      Finset.card_filter_add_card_filter_not _
    rcases hThree i with h | ⟨h, v, hv, hvi⟩ | ⟨h, hall⟩
    · rw [h]
      simp
    · have hle := shift_card_le Pf (fun x => x.2 i) v (fun x => rfl) (hadd v hv) 0
      have hsub : (Pf.filter (fun x => x.2 i = 0 + v.2 i)).card ≤
          (Pf.filter (fun x => ¬ x.2 i = 0)).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, by rw [hx.2, zero_add]; exact hvi⟩
      have hle' : (Pf.filter (fun x => x.2 i = 0)).card ≤
          (Pf.filter (fun x => x.2 i = 0 + v.2 i)).card := hle
      have hn2 : Pf.card ≤ 2 * (Pf.filter (fun x => ¬ x.2 i = 0)).card := by omega
      rw [h]
      calc Pf.card * (2 * d i) ≤ (2 * (Pf.filter (fun x => ¬ x.2 i = 0)).card) * (2 * d i) :=
            Nat.mul_le_mul_right _ hn2
        _ = (Pf.filter (fun x => ¬ x.2 i = 0)).card * (4 * d i) := by ring
    · obtain ⟨v1, hv1, e1⟩ := hall ![1, 0]
      obtain ⟨v2, hv2, e2⟩ := hall ![0, 1]
      obtain ⟨v3, hv3, e3⟩ := hall ![1, 1]
      have hle1 : (Pf.filter (fun x => x.2 i = 0)).card ≤
          (Pf.filter (fun x => x.2 i = ![1, 0])).card := by
        have hle := shift_card_le Pf (fun x => x.2 i) v1 (fun x => rfl) (hadd v1 hv1) 0
        simpa only [e1, zero_add] using hle
      have hle2 : (Pf.filter (fun x => x.2 i = 0)).card ≤
          (Pf.filter (fun x => x.2 i = ![0, 1])).card := by
        have hle := shift_card_le Pf (fun x => x.2 i) v2 (fun x => rfl) (hadd v2 hv2) 0
        simpa only [e2, zero_add] using hle
      have hle3 : (Pf.filter (fun x => x.2 i = 0)).card ≤
          (Pf.filter (fun x => x.2 i = ![1, 1])).card := by
        have hle := shift_card_le Pf (fun x => x.2 i) v3 (fun x => rfl) (hadd v3 hv3) 0
        simpa only [e3, zero_add] using hle
      have hsum : (Pf.filter (fun x => x.2 i = ![1, 0])).card +
          (Pf.filter (fun x => x.2 i = ![0, 1])).card +
          (Pf.filter (fun x => x.2 i = ![1, 1])).card ≤
          (Pf.filter (fun x => ¬ x.2 i = 0)).card := by
        rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro x _
        rcases hcase (x.2 i) with hc | hc | hc | hc <;> rw [hc] <;> decide
      have hn4 : 3 * Pf.card ≤ 4 * (Pf.filter (fun x => ¬ x.2 i = 0)).card := by omega
      rw [h]
      calc Pf.card * (3 * d i) = d i * (3 * Pf.card) := by ring
        _ ≤ d i * (4 * (Pf.filter (fun x => ¬ x.2 i = 0)).card) := Nat.mul_le_mul_left _ hn4
        _ = (Pf.filter (fun x => ¬ x.2 i = 0)).card * (4 * d i) := by ring
  have hh2 : (∑ x ∈ Pf, 2 * (∑ i, if x.2 i = 0 then 0 else 2 * d i)) ≤
      ∑ x ∈ Pf, 2 * (Finset.univ.filter (fun j => ¬ x.1 j = 0)).card :=
    Finset.sum_le_sum (fun x hx => Nat.mul_le_mul_left 2 (hTwo x ((hPf x).mp hx)))
  have hfin : Pf.card * ((∑ i, cst i) + J.card) ≤ Pf.card * Fintype.card E := by
    calc Pf.card * ((∑ i, cst i) + J.card) = Pf.card * (∑ i, cst i) + J.card * Pf.card := by ring
      _ ≤ Fintype.card E * Pf.card := by omega
      _ = Pf.card * Fintype.card E := by ring
  exact Nat.le_of_mul_le_mul_left hfin hnpos

-- ===== own part: the pencil, the target and the lower bound =====

def Kf {l : ℕ} (d : Fin l → ℕ) (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F)
    (z : Fin l → Fin 2 → F) :
    Matrix (Σ i : Fin l, Fin (2 * d i)) (Σ i : Fin l, Fin (2 * d i)) F :=
  Matrix.blockDiagonal' (fun i => z i 0 • U i + z i 1 • V i)

def Xf {l : ℕ} (d : Fin l → ℕ) (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F)
    (A : Matrix (Σ i : Fin l, Fin (2 * d i)) (Σ i : Fin l, Fin (2 * d i)) F)
    (z : Fin l → Fin 2 → F) :
    Matrix ((Σ i : Fin l, Fin (2 * d i)) ⊕ (Σ i : Fin l, Fin (2 * d i)))
      ((Σ i : Fin l, Fin (2 * d i)) ⊕ (Σ i : Fin l, Fin (2 * d i))) F :=
  Matrix.fromBlocks A (Kf d U V z) (Kf d U V z).transpose 0

private lemma Kf_add {l : ℕ} (d : Fin l → ℕ)
    (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F)
    (z z' : Fin l → Fin 2 → F) : Kf d U V (z + z') = Kf d U V z + Kf d U V z' := by
  ext ⟨i, x⟩ ⟨j, y⟩
  by_cases h : i = j
  · subst h
    simp only [Kf, Matrix.blockDiagonal'_apply_eq, Matrix.add_apply, Matrix.smul_apply,
      Pi.add_apply, smul_eq_mul]
    ring
  · simp only [Kf, Matrix.add_apply, Matrix.blockDiagonal'_apply_ne _ _ _ h, add_zero]

private lemma Kf_smul {l : ℕ} (d : Fin l → ℕ)
    (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F)
    (c : F) (z : Fin l → Fin 2 → F) : Kf d U V (c • z) = c • Kf d U V z := by
  ext ⟨i, x⟩ ⟨j, y⟩
  by_cases h : i = j
  · subst h
    simp only [Kf, Matrix.blockDiagonal'_apply_eq, Matrix.add_apply, Matrix.smul_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [Kf, Matrix.smul_apply, Matrix.blockDiagonal'_apply_ne _ _ _ h, smul_zero]

private lemma Kf_zero {l : ℕ} (d : Fin l → ℕ)
    (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F) : Kf d U V 0 = 0 := by
  have h := Kf_smul d U V 0 0
  rw [zero_smul, zero_smul] at h
  exact h

private lemma Xf_add {l : ℕ} (d : Fin l → ℕ)
    (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F)
    (A A' : Matrix (Σ i : Fin l, Fin (2 * d i)) (Σ i : Fin l, Fin (2 * d i)) F)
    (z z' : Fin l → Fin 2 → F) :
    Xf d U V (A + A') (z + z') = Xf d U V A z + Xf d U V A' z' := by
  unfold Xf
  rw [Matrix.fromBlocks_add, Kf_add, Matrix.transpose_add, add_zero]

private lemma Xf_smul {l : ℕ} (d : Fin l → ℕ)
    (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F)
    (c : F) (A : Matrix (Σ i : Fin l, Fin (2 * d i)) (Σ i : Fin l, Fin (2 * d i)) F)
    (z : Fin l → Fin 2 → F) :
    Xf d U V (c • A) (c • z) = c • Xf d U V A z := by
  unfold Xf
  rw [Matrix.fromBlocks_smul, Kf_smul, Matrix.transpose_smul, smul_zero]

private lemma Xf_zero {l : ℕ} (d : Fin l → ℕ)
    (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F) : Xf d U V 0 0 = 0 := by
  have h := Xf_smul d U V 0 0 0
  rw [zero_smul, zero_smul, zero_smul] at h
  exact h

private lemma Xf_split {l : ℕ} (d : Fin l → ℕ)
    (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F)
    (A : Matrix (Σ i : Fin l, Fin (2 * d i)) (Σ i : Fin l, Fin (2 * d i)) F)
    (z : Fin l → Fin 2 → F) :
    Xf d U V A z = Matrix.fromBlocks A 0 0 0 + Xf d U V 0 z := by
  unfold Xf
  rw [Matrix.fromBlocks_add, add_zero, zero_add, zero_add, add_zero]

private lemma Xf_zero_right {l : ℕ} (d : Fin l → ℕ)
    (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F)
    (A : Matrix (Σ i : Fin l, Fin (2 * d i)) (Σ i : Fin l, Fin (2 * d i)) F) :
    Xf d U V A 0 = Matrix.fromBlocks A 0 0 0 := by
  unfold Xf
  rw [Kf_zero, Matrix.transpose_zero]

def embTop (I : Type) [Fintype I] [DecidableEq I] : Matrix I I F →ₗ[F] Matrix (I ⊕ I) (I ⊕ I) F where
  toFun := fun A => Matrix.fromBlocks A 0 0 0
  map_add' := fun A B => by
    rw [Matrix.fromBlocks_add, add_zero]
  map_smul' := fun c A => by
    rw [Matrix.fromBlocks_smul, smul_zero]
    rfl

private lemma embTop_inj (I : Type) [Fintype I] [DecidableEq I] : Function.Injective (embTop I) := by
  intro A B h
  ext i j
  exact congrFun (congrFun h (Sum.inl i)) (Sum.inl j)

private lemma pencil_rank_ge2 {l : ℕ} (d : Fin l → ℕ)
    (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F)
    (hr : ∀ i, (U i).rank = 2 * d i ∧ (V i).rank = 2 * d i ∧ (U i + V i).rank = 2 * d i)
    (z : Fin l → Fin 2 → F) :
    (∑ i : Fin l, if z i = 0 then 0 else 2 * d i) ≤ (Kf d U V z).rank := by
  classical
  let Kz := Matrix.blockDiagonal' (fun i => z i 0 • U i + z i 1 • V i)
  let Sx := Finset.univ.filter (fun i : Fin l => ¬ z i = 0)
  let B (i : Sx) := Fin (2 * d i.val)
  let e : ((i : Sx) × B i) → ((i : Fin l) × Fin (2 * d i)) := fun p => ⟨p.1.val, p.2⟩
  let D (i : Sx) : Matrix (B i) (B i) F := z i.val 0 • U i.val + z i.val 1 • V i.val
  have hd (i : Sx) : (D i).rank = Fintype.card (B i) := by
    have hn := (Finset.mem_filter.mp i.property).2
    obtain ⟨hU, hW, hUW⟩ := hr i.val
    have hz : ¬ (z i.val 0 = 0 ∧ z i.val 1 = 0) := by
      rintro ⟨h0, h1⟩
      apply hn
      funext k
      fin_cases k
      · exact h0
      · exact h1
    rcases zmod2_cases (z i.val 0) with h1 | h1 <;>
      rcases zmod2_cases (z i.val 1) with hTwo | hTwo <;>
      simp_all [D, B]
  have hsub : Kz.submatrix e e = Matrix.blockDiagonal' D := by
    ext ⟨i, x⟩ ⟨j, y⟩
    by_cases h : i = j
    · subst j; simp [e, Kz, D]
    · have h' : i.val ≠ j.val := fun hij => h (Subtype.ext hij)
      simp only [Matrix.submatrix_apply, e, Kz,
        Matrix.blockDiagonal'_apply_ne _ _ _ h', Matrix.blockDiagonal'_apply_ne _ _ _ h]
  have hcard : Fintype.card ((i : Sx) × B i) =
      ∑ i : Fin l, if z i = 0 then 0 else 2 * d i := by
    rw [Fintype.card_sigma]
    simp only [B, Fintype.card_fin]
    rw [Finset.sum_coe_sort Sx (fun i => 2 * d i)]
    simp only [Sx, Finset.sum_filter, ite_not]
  calc (∑ i : Fin l, if z i = 0 then 0 else 2 * d i)
      = (Matrix.blockDiagonal' D).rank := hcard.symm.trans (blockDiag_full_rank D hd).symm
    _ ≤ Kz.rank := hsub ▸ Matrix.rank_submatrix_le Kz e e

private lemma lower_core {l : ℕ} (d : Fin l → ℕ)
    (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F)
    (hr : ∀ i, (U i).rank = 2 * d i ∧ (V i).rank = 2 * d i ∧ (U i + V i).rank = 2 * d i)
    (S : Submodule F (Matrix (Σ i : Fin l, Fin (2 * d i)) (Σ i : Fin l, Fin (2 * d i)) F))
    (Q : Submodule F (Fin l → Fin 2 → F))
    {E : Type} [Fintype E] [DecidableEq E]
    (R : E → Matrix ((Σ i : Fin l, Fin (2 * d i)) ⊕ (Σ i : Fin l, Fin (2 * d i)))
      ((Σ i : Fin l, Fin (2 * d i)) ⊕ (Σ i : Fin l, Fin (2 * d i))) F)
    (hR : ∀ j, (R j).rank ≤ 2)
    (hspan : ∀ A ∈ S, ∀ z ∈ Q, Xf d U V A z ∈ Submodule.span F (Set.range R))
    (cst : Fin l → ℕ)
    (hcst : ∀ i, cst i = 0 ∨ (cst i = 2 * d i ∧ ∃ z ∈ Q, ¬ z i = 0) ∨
      (cst i = 3 * d i ∧ ∀ v : Fin 2 → F, ∃ z ∈ Q, z i = v)) :
    Module.finrank F S + ∑ i, cst i ≤ Fintype.card E := by
  classical
  let I := Σ i : Fin l, Fin (2 * d i)
  let Mat := Matrix (I ⊕ I) (I ⊕ I) F
  let Φ : (E → F) →ₗ[F] Mat :=
    { toFun := fun c => ∑ j, c j • R j
      map_add' := fun a b => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a b => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum] }
  have hΦ : ∀ X : Mat, X ∈ Submodule.span F (Set.range R) → ∃ c : E → F, Φ c = X := fun X hX =>
    (Submodule.mem_span_range_iff_exists_fun F).mp hX
  let N0 : Submodule F (E → F) := Submodule.comap Φ (S.map (embTop I))
  have hN0 : Module.finrank F S ≤ Module.finrank F N0 := by
    have hle : S.map (embTop I) ≤ LinearMap.range Φ := by
      rintro _ ⟨A, hA, rfl⟩
      obtain ⟨c, hc⟩ := hΦ _ (hspan A hA 0 Q.zero_mem)
      refine ⟨c, ?_⟩
      rw [hc]
      exact Xf_zero_right d U V A
    have h1 : Submodule.map Φ N0 = S.map (embTop I) := by
      rw [Submodule.map_comap_eq]
      exact inf_eq_right.mpr hle
    have hTwo := Submodule.finrank_map_le Φ N0
    rw [h1, finrank_map_eq_of_inj (embTop_inj I) S] at hTwo
    exact hTwo
  obtain ⟨J, hJc, hJ⟩ := info_set (Module.finrank F S) N0 hN0
  let Ch : Submodule F ((E → F) × (Fin l → Fin 2 → F)) :=
    { carrier := {x | x.2 ∈ Q ∧ (∀ j ∈ J, x.1 j = 0) ∧ ∃ A ∈ S, Φ x.1 = Xf d U V A x.2}, add_mem' := by
        rintro x y ⟨hx1, hx2, A, hA, hxA⟩ ⟨hy1, hy2, B, hB, hyB⟩
        refine ⟨Q.add_mem hx1 hy1, fun j hj => ?_, A + B, S.add_mem hA hB, ?_⟩
        · show x.1 j + y.1 j = 0
          rw [hx2 j hj, hy2 j hj, add_zero]
        · show Φ (x.1 + y.1) = Xf d U V (A + B) (x.2 + y.2)
          rw [map_add, hxA, hyB, Xf_add]
      zero_mem' := ⟨Q.zero_mem, fun j _ => rfl, 0, S.zero_mem, by
        show Φ 0 = Xf d U V 0 0
        rw [map_zero, Xf_zero]⟩
      smul_mem' := by
        rintro c x ⟨hx1, hx2, A, hA, hxA⟩
        refine ⟨Q.smul_mem c hx1, fun j hj => ?_, c • A, S.smul_mem c hA, ?_⟩
        · show c * x.1 j = 0
          rw [hx2 j hj, mul_zero]
        · show Φ (c • x.1) = Xf d U V (c • A) (c • x.2)
          rw [map_smul, hxA, Xf_smul] }
  have hmemCh : ∀ x, x ∈ Ch ↔
      (x.2 ∈ Q ∧ (∀ j ∈ J, x.1 j = 0) ∧ ∃ A ∈ S, Φ x.1 = Xf d U V A x.2) := fun x => Iff.rfl
  have hlift : ∀ z ∈ Q, ∃ x ∈ Ch, x.2 = z := by
    intro z hz
    obtain ⟨c, hc⟩ := hΦ _ (hspan 0 S.zero_mem z hz)
    obtain ⟨v, hv, hvJ⟩ := hJ c
    obtain ⟨A', hA', hvA⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hv)
    refine ⟨(c + v, z), (hmemCh _).mpr ⟨hz, fun j hj => ?_, A', hA', ?_⟩, rfl⟩
    · show c j + v j = 0
      rw [hvJ j hj]
      exact zmod2_add_self _
    · show Φ (c + v) = Xf d U V A' z
      rw [map_add, hc, ← hvA, Xf_split d U V A' z]
      exact add_comm _ _
  have hcc := code_count d cst Ch J (fun x hx j hj => ((hmemCh x).mp hx).2.1 j hj) ?_ ?_
  · rw [hJc] at hcc
    omega
  · intro x hx
    obtain ⟨hx1, hx2, A, hA, hxA⟩ := (hmemCh x).mp hx
    have hk := pencil_rank_ge2 d U V hr x.2
    have h2k : 2 * (Kf d U V x.2).rank ≤ (Xf d U V A x.2).rank :=
      two_mul_rank_le_rank_fromBlocks A (Kf d U V x.2)
    have hsum : Φ x.1 = ∑ j ∈ Finset.univ.filter (fun j => ¬ x.1 j = 0), R j := by
      show ∑ j, x.1 j • R j = _
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      rcases zmod2_cases (x.1 j) with h | h <;> simp [h]
    have hrk : (Xf d U V A x.2).rank ≤
        2 * (Finset.univ.filter (fun j => ¬ x.1 j = 0)).card := by
      rw [← hxA, hsum]
      refine (matrix_rank_sum_le _ _).trans ?_
      calc (∑ j ∈ Finset.univ.filter (fun j => ¬ x.1 j = 0), (R j).rank)
          ≤ ∑ j ∈ Finset.univ.filter (fun j => ¬ x.1 j = 0), 2 :=
            Finset.sum_le_sum (fun j _ => hR j)
        _ = 2 * (Finset.univ.filter (fun j => ¬ x.1 j = 0)).card := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  · intro i
    rcases hcst i with h | ⟨h, z, hz, hzi⟩ | ⟨h, hall⟩
    · left
      exact h
    · right
      left
      obtain ⟨x, hx, rfl⟩ := hlift z hz
      exact ⟨h, x, hx, hzi⟩
    · right
      right
      refine ⟨h, fun v => ?_⟩
      obtain ⟨z, hz, hzv⟩ := hall v
      obtain ⟨x, hx, rfl⟩ := hlift z hz
      exact ⟨x, hx, hzv⟩

-- ===== own part: the upper bound =====

private lemma block_family {dd : ℕ} (U V : Matrix (Fin (2 * dd)) (Fin (2 * dd)) F)
    (hr : U.rank = 2 * dd ∧ V.rank = 2 * dd ∧ (U + V).rank = 2 * dd)
    (P : Submodule F (Fin 2 → F)) :
    ∃ (n : ℕ) (r : Fin n → Matrix (Fin (2 * dd)) (Fin (2 * dd)) F),
      n ≤ (if Module.finrank F P = 0 then 0 else
        if Module.finrank F P = 1 then 2 * dd else 3 * dd) ∧
      (∀ k, (r k).rank ≤ 1) ∧
      ∀ v ∈ P, v 0 • U + v 1 • V ∈ Submodule.span F (Set.range r) := by
  classical
  by_cases h0 : Module.finrank F P = 0
  · refine ⟨0, fun k => k.elim0, by rw [if_pos h0], fun k => k.elim0, fun v hv => ?_⟩
    have hb : P = ⊥ := Submodule.finrank_eq_zero.mp h0
    rw [hb] at hv
    have hv0 : v = 0 := (Submodule.mem_bot F).mp hv
    rw [hv0]
    simp
  by_cases h1 : Module.finrank F P = 1
  · obtain ⟨v0, _, hv0⟩ := finrank_eq_one_iff'.mp h1
    obtain ⟨a, b, hab⟩ := matrix_rank_decomp (v0.1 0 • U + v0.1 1 • V)
    refine ⟨(v0.1 0 • U + v0.1 1 • V).rank, fun k => Matrix.vecMulVec (a k) (b k), ?_,
      fun k => Matrix.rank_vecMulVec_le _ _, fun v hv => ?_⟩
    · rw [if_neg h0, if_pos h1]
      have h := Matrix.rank_le_card_width (v0.1 0 • U + v0.1 1 • V)
      rwa [Fintype.card_fin] at h
    · obtain ⟨c, hc⟩ := hv0 ⟨v, hv⟩
      have hvc : v = c • v0.1 := (congrArg Subtype.val hc).symm
      have hM : v 0 • U + v 1 • V = c • (v0.1 0 • U + v0.1 1 • V) := by
        rw [hvc]
        simp only [Pi.smul_apply, smul_eq_mul, smul_add, mul_smul]
      have hs : c • (∑ k, Matrix.vecMulVec (a k) (b k)) ∈
          Submodule.span F (Set.range (fun k => Matrix.vecMulVec (a k) (b k))) :=
        Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨k, rfl⟩)
      rw [hM]
      rwa [← hab] at hs
  · obtain ⟨P1, P2, P3, h12, h23, hrk⟩ := plane_three_decomp U V
      (by rw [hr.1, Fintype.card_fin]) (by rw [hr.2.1, Fintype.card_fin])
      (by rw [hr.2.2, Fintype.card_fin])
    rw [Fintype.card_fin] at hrk
    obtain ⟨a1, b1, hab1⟩ := matrix_rank_decomp P1
    obtain ⟨a2, b2, hab2⟩ := matrix_rank_decomp P2
    obtain ⟨a3, b3, hab3⟩ := matrix_rank_decomp P3
    let rr : Fin P1.rank ⊕ Fin P2.rank ⊕ Fin P3.rank → Matrix (Fin (2 * dd)) (Fin (2 * dd)) F :=
      Sum.elim (fun k => Matrix.vecMulVec (a1 k) (b1 k))
        (Sum.elim (fun k => Matrix.vecMulVec (a2 k) (b2 k))
          (fun k => Matrix.vecMulVec (a3 k) (b3 k)))
    let eq := Fintype.equivFin (Fin P1.rank ⊕ Fin P2.rank ⊕ Fin P3.rank)
    have hrr : ∀ p, (rr p).rank ≤ 1 := by
      rintro (k | k | k) <;> exact Matrix.rank_vecMulVec_le _ _
    refine ⟨Fintype.card (Fin P1.rank ⊕ Fin P2.rank ⊕ Fin P3.rank), fun k => rr (eq.symm k),
      ?_, fun k => hrr _, ?_⟩
    · rw [if_neg h0, if_neg h1]
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    · intro v _
      have hmem : ∀ p, rr p ∈ Submodule.span F (Set.range (fun k => rr (eq.symm k))) := fun p =>
        Submodule.subset_span ⟨eq p, by simp⟩
      have hP1 : P1 ∈ Submodule.span F (Set.range (fun k => rr (eq.symm k))) := by
        have h : (∑ k, Matrix.vecMulVec (a1 k) (b1 k)) ∈
            Submodule.span F (Set.range (fun k => rr (eq.symm k))) :=
          Submodule.sum_mem _ fun k _ => hmem (Sum.inl k)
        rwa [← hab1] at h
      have hP2 : P2 ∈ Submodule.span F (Set.range (fun k => rr (eq.symm k))) := by
        have h : (∑ k, Matrix.vecMulVec (a2 k) (b2 k)) ∈
            Submodule.span F (Set.range (fun k => rr (eq.symm k))) :=
          Submodule.sum_mem _ fun k _ => hmem (Sum.inr (Sum.inl k))
        rwa [← hab2] at h
      have hP3 : P3 ∈ Submodule.span F (Set.range (fun k => rr (eq.symm k))) := by
        have h : (∑ k, Matrix.vecMulVec (a3 k) (b3 k)) ∈
            Submodule.span F (Set.range (fun k => rr (eq.symm k))) :=
          Submodule.sum_mem _ fun k _ => hmem (Sum.inr (Sum.inr k))
        rwa [← hab3] at h
      rw [← h12, ← h23]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.add_mem _ hP1 hP2))
        (Submodule.smul_mem _ _ (Submodule.add_mem _ hP2 hP3))

def eL {l : ℕ} (d : Fin l → ℕ) (i : Fin l) :
    Fin (2 * d i) → (Σ i : Fin l, Fin (2 * d i)) ⊕ (Σ i : Fin l, Fin (2 * d i)) :=
  fun x => Sum.inl ⟨i, x⟩

def eR {l : ℕ} (d : Fin l → ℕ) (i : Fin l) :
    Fin (2 * d i) → (Σ i : Fin l, Fin (2 * d i)) ⊕ (Σ i : Fin l, Fin (2 * d i)) :=
  fun x => Sum.inr ⟨i, x⟩

private lemma layer_entry_zero {l : ℕ} (d : Fin l → ℕ) (i : Fin l)
    (M : Matrix (Fin (2 * d i)) (Fin (2 * d i)) F)
    (a b : (Σ i : Fin l, Fin (2 * d i)) ⊕ (Σ i : Fin l, Fin (2 * d i)))
    (h : ¬ ∃ x y, a = eL d i x ∧ b = eR d i y) :
    layer (eL d i) (eR d i) M a b = 0 := by
  rw [layer_apply]
  apply Finset.sum_eq_zero
  intro p _
  apply Finset.sum_eq_zero
  intro q _
  rw [if_neg]
  rintro ⟨h1, hTwo⟩
  exact h ⟨p, q, h1, hTwo⟩

private lemma layer_entry_same {l : ℕ} (d : Fin l → ℕ) (i : Fin l)
    (M : Matrix (Fin (2 * d i)) (Fin (2 * d i)) F) (x y : Fin (2 * d i)) :
    layer (eL d i) (eR d i) M (Sum.inl ⟨i, x⟩) (Sum.inr ⟨i, y⟩) = M x y := by
  rw [layer_apply, Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single y]
    · simp [eL, eR]
    · intro q _ hq
      simp [eL, eR, Ne.symm hq]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · intro p _ hp
    apply Finset.sum_eq_zero
    intro q _
    simp [eL, eR, Ne.symm hp]
  · intro h
    exact (h (Finset.mem_univ _)).elim

private lemma sum_layer_blocks {l : ℕ} (d : Fin l → ℕ)
    (D : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F) :
    (∑ i, layer (eL d i) (eR d i) (D i)) =
      Matrix.fromBlocks 0 (Matrix.blockDiagonal' D) 0 0 := by
  ext a b
  rw [Matrix.sum_apply]
  rcases a with ⟨i', x⟩ | ⟨i', x⟩
  · rcases b with ⟨j', y⟩ | ⟨j', y⟩
    · rw [Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
      apply Finset.sum_eq_zero
      intro i _
      apply layer_entry_zero
      rintro ⟨p, q, _, hTwo⟩
      cases hTwo
    · rw [Matrix.fromBlocks_apply₁₂, Finset.sum_eq_single i']
      · by_cases hij : i' = j'
        · subst hij
          rw [layer_entry_same, Matrix.blockDiagonal'_apply_eq]
        · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hij]
          apply layer_entry_zero
          rintro ⟨p, q, _, hTwo⟩
          exact hij (congrArg Sigma.fst (Sum.inr.inj hTwo)).symm
      · intro i _ hi
        apply layer_entry_zero
        rintro ⟨p, q, h1, _⟩
        exact hi (congrArg Sigma.fst (Sum.inl.inj h1)).symm
      · intro h
        exact (h (Finset.mem_univ _)).elim
  · have hz : ∀ i ∈ Finset.univ, layer (eL d i) (eR d i) (D i) (Sum.inr ⟨i', x⟩) b = 0 := by
      intro i _
      apply layer_entry_zero
      rintro ⟨p, q, h1, _⟩
      cases h1
    rw [Finset.sum_eq_zero hz]
    rcases b with b | b
    · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]

private lemma sum_symLayer_blocks {l : ℕ} (d : Fin l → ℕ)
    (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F) (z : Fin l → Fin 2 → F) :
    (∑ i, symLayer (eL d i) (eR d i) (z i 0 • U i + z i 1 • V i)) = Xf d U V 0 z := by
  have h1 : ∀ i ∈ Finset.univ, symLayer (eL d i) (eR d i) (z i 0 • U i + z i 1 • V i) =
      layer (eL d i) (eR d i) (z i 0 • U i + z i 1 • V i) +
        (layer (eL d i) (eR d i) (z i 0 • U i + z i 1 • V i)).transpose := fun i _ => rfl
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Matrix.transpose_sum,
    sum_layer_blocks d (fun i => z i 0 • U i + z i 1 • V i), Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_add]
  unfold Xf Kf
  simp only [Matrix.transpose_zero, add_zero, zero_add]

private lemma upper_core {l : ℕ} (d : Fin l → ℕ)
    (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F)
    (S : Submodule F (Matrix (Σ i : Fin l, Fin (2 * d i)) (Σ i : Fin l, Fin (2 * d i)) F))
    (Q : Submodule F (Fin l → Fin 2 → F))
    (hS : S = Submodule.span F {A | A ∈ S ∧ A.rank ≤ 2})
    (cst : Fin l → ℕ)
    (hfam : ∀ i, ∃ (n : ℕ) (r : Fin n → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F),
      n ≤ cst i ∧ (∀ k, (r k).rank ≤ 1) ∧
      ∀ z ∈ Q, z i 0 • U i + z i 1 • V i ∈ Submodule.span F (Set.range r))
    (t : ℕ) (ht : Module.finrank F S + ∑ i, cst i ≤ t) :
    let I := Σ i : Fin l, Fin (2 * d i)
    let T := Matrix I I F
    let w := Fintype.card (I ⊕ I)
    let coord := Fintype.equivFin (I ⊕ I)
    ∃ (C : Circuit) (tap : T → (Fin l → Fin 2 → F) → ℕ),
      ReadsBack ((w + 1) + (w + 1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
      ∀ A ∈ S, ∀ z ∈ Q,
        (depths ((w + 1) + (w + 1)) C).getD (tap A z) 0 ≤ 1 ∧
        Represents (mkTable coord (Xf d U V A z)) ⟨C.gates, tap A z⟩ := by
  classical
  intro I T w coord
  let GS := {A : T // A ∈ S ∧ A.rank ≤ 2}
  obtain ⟨ιS, fS, hfS_inj, hspanS, hliS⟩ :=
    exists_linearIndependent' F (Subtype.val : GS → T)
  letI : Finite ιS := Finite.of_injective fS hfS_inj
  letI : Fintype ιS := Fintype.ofFinite ιS
  have hS_span_eq : Submodule.span F (Set.range (Subtype.val ∘ fS)) = S := by
    rw [hspanS]
    conv_rhs => rw [hS]
    congr 1
    ext A
    constructor
    · rintro ⟨⟨A, hA⟩, rfl⟩; exact hA
    · intro hA; exact ⟨⟨A, hA⟩, rfl⟩
  have hcardS : Fintype.card ιS = Module.finrank F S := by
    have h := linearIndependent_iff_card_eq_finrank_span.mp hliS
    change Fintype.card ιS = Module.finrank F (Submodule.span F (Set.range (Subtype.val ∘ fS))) at h
    rw [hS_span_eq] at h
    exact h
  choose n r hn hrk hmem using hfam
  let GenIdx : Type := ιS ⊕ (Σ i : Fin l, Fin (n i))
  let Rgen : GenIdx → Matrix (I ⊕ I) (I ⊕ I) F
    | Sum.inl k => layer Sum.inl Sum.inl (fS k).val
    | Sum.inr ⟨i, k⟩ => symLayer (eL d i) (eR d i) (r i k)
  have hRgen_rk : ∀ idx : GenIdx, (Rgen idx).rank ≤ 2 := by
    rintro (k | ⟨i, k⟩)
    · exact (layer_rank _ _ _).trans (fS k).property.2
    · exact symLayer_rank _ _ _ (hrk i k)
  have hcard_gen : Fintype.card GenIdx ≤ t := by
    simp only [GenIdx, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, hcardS]
    have hle : (∑ i, n i) ≤ ∑ i, cst i := Finset.sum_le_sum (fun i _ => hn i)
    omega
  let SpanR := Submodule.span F (Set.range Rgen)
  have hspan_all : ∀ A ∈ S, ∀ z ∈ Q, Xf d U V A z ∈ SpanR := by
    intro A hA z hz
    rw [Xf_split]
    apply SpanR.add_mem
    · rw [fromBlocks_top_eq_layer]
      have hA_span : A ∈ Submodule.span F (Set.range (Subtype.val ∘ fS)) := by
        rw [hS_span_eq]; exact hA
      have hsub : Submodule.span F (Set.range (Subtype.val ∘ fS)) ≤
          SpanR.comap (layer (Sum.inl : I → I ⊕ I) Sum.inl) := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        exact Submodule.subset_span ⟨Sum.inl k, rfl⟩
      exact hsub hA_span
    · rw [← sum_symLayer_blocks]
      apply SpanR.sum_mem
      intro i _
      have hsub : Submodule.span F (Set.range (r i)) ≤
          SpanR.comap (symLayer (eL d i) (eR d i)) := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        exact Submodule.subset_span ⟨Sum.inr ⟨i, k⟩, rfl⟩
      exact hsub (hmem i z hz)
  let Target : T × (Fin l → Fin 2 → F) → Matrix (I ⊕ I) (I ⊕ I) F :=
    fun p => if p.1 ∈ S ∧ p.2 ∈ Q then Xf d U V p.1 p.2 else 0
  have hTarget : ∀ p : T × (Fin l → Fin 2 → F), Target p ∈ SpanR := by
    intro ⟨A, z⟩
    by_cases hA : A ∈ S ∧ z ∈ Q
    · simp only [Target, if_pos hA]; exact hspan_all A hA.1 z hA.2
    · simp only [Target, if_neg hA]; exact SpanR.zero_mem
  obtain ⟨C, tap, hRB, hfan, hcnt, hreps⟩ := synth coord Rgen Target hRgen_rk hTarget
  refine ⟨C, fun A z => tap (A, z), hRB, hfan, hcnt.trans hcard_gen, ?_⟩
  intro A hA z hz
  have hrp := hreps (A, z)
  simp only [Target, if_pos (And.intro hA hz)] at hrp
  exact hrp

-- ===== own part: assembly =====

private lemma main {l : ℕ} (d : Fin l → ℕ)
    (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F)
    (hr : ∀ i, (U i).rank = 2 * d i ∧ (V i).rank = 2 * d i ∧ (U i + V i).rank = 2 * d i)
    (S : Submodule F (Matrix (Σ i : Fin l, Fin (2 * d i)) (Σ i : Fin l, Fin (2 * d i)) F))
    (Q : Submodule F (Fin l → Fin 2 → F))
    (hS : S = Submodule.span F {A | A ∈ S ∧ A.rank ≤ 2}) (t : ℕ) :
    let I := Σ i : Fin l, Fin (2 * d i)
    let T := Matrix I I F
    let w := Fintype.card (I ⊕ I)
    let coord := Fintype.equivFin (I ⊕ I)
    let dimension := fun i : Fin l =>
      Module.finrank F (Submodule.span F {v : Fin 2 → F | ∃ z ∈ Q, z i = v})
    (∃ (C : Circuit) (tap : T → (Fin l → Fin 2 → F) → ℕ),
      ReadsBack ((w + 1) + (w + 1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
      ∀ A ∈ S, ∀ z ∈ Q,
        (depths ((w + 1) + (w + 1)) C).getD (tap A z) 0 ≤ 1 ∧
        Represents (mkTable coord (Xf d U V A z)) ⟨C.gates, tap A z⟩) ↔
    Module.finrank F S + ∑ i,
      (if dimension i = 0 then 0 else if dimension i = 1 then 2 * d i else 3 * d i) ≤ t := by
  classical
  intro I T w coord dimension
  let P : Fin l → Submodule F (Fin 2 → F) := fun i =>
    Q.map (LinearMap.proj i : (Fin l → Fin 2 → F) →ₗ[F] (Fin 2 → F))
  have hPmem : ∀ i (v : Fin 2 → F), v ∈ P i ↔ ∃ z ∈ Q, z i = v := fun i v => Iff.rfl
  have hdim : ∀ i, dimension i = Module.finrank F (P i) := by
    intro i
    have hset : {v : Fin 2 → F | ∃ z ∈ Q, z i = v} = ((P i : Submodule F (Fin 2 → F)) : Set (Fin 2 → F)) := by
      ext v
      exact (hPmem i v).symm
    show Module.finrank F (Submodule.span F {v : Fin 2 → F | ∃ z ∈ Q, z i = v}) = _
    rw [hset, Submodule.span_eq]
  simp only [hdim]
  constructor
  · rintro ⟨C, tap, hRB, hfan, hcnt, htap⟩
    let Target : ↥S × ↥Q → Matrix (I ⊕ I) (I ⊕ I) F := fun p => Xf d U V p.1.val p.2.val
    obtain ⟨D, hDcard, hDrk, hDspan⟩ := extractSpan coord Target C (fun p => tap p.1.val p.2.val)
      hRB hfan hcnt (fun p => htap p.1.val p.1.property p.2.val p.2.property)
    have hcore := lower_core d U V hr S Q (fun j : D => actualR coord C j.val)
      (fun j => hDrk j.val j.property)
      (fun A hA z hz => hDspan (⟨A, hA⟩, ⟨z, hz⟩))
      (fun i => if Module.finrank F (P i) = 0 then 0 else
        if Module.finrank F (P i) = 1 then 2 * d i else 3 * d i) ?_
    · rw [Fintype.card_coe] at hcore
      exact hcore.trans hDcard
    · intro i
      by_cases h0 : Module.finrank F (P i) = 0
      · left
        exact if_pos h0
      by_cases h1 : Module.finrank F (P i) = 1
      · right
        left
        refine ⟨by rw [if_neg h0, if_pos h1], ?_⟩
        by_contra hcon
        push_neg at hcon
        have hbot : P i = ⊥ := by
          rw [eq_bot_iff]
          rintro v hv
          obtain ⟨z, hz, rfl⟩ := (hPmem i v).mp hv
          exact (Submodule.mem_bot F).mpr (hcon z hz)
        rw [hbot, finrank_bot] at h1
        omega
      · right
        right
        refine ⟨by rw [if_neg h0, if_neg h1], ?_⟩
        have hle := Submodule.finrank_le (P i)
        rw [Module.finrank_fin_fun] at hle
        have hTwo : Module.finrank F (P i) = Module.finrank F (Fin 2 → F) := by
          rw [Module.finrank_fin_fun]
          omega
        have htop : P i = ⊤ := Submodule.eq_top_of_finrank_eq hTwo
        intro v
        have hv : v ∈ P i := by
          rw [htop]
          exact Submodule.mem_top
        exact (hPmem i v).mp hv
  · intro ht
    refine upper_core d U V S Q hS
      (fun i => if Module.finrank F (P i) = 0 then 0 else
        if Module.finrank F (P i) = 1 then 2 * d i else 3 * d i) ?_ t ht
    intro i
    obtain ⟨n, r, hn, hrk, hmem⟩ := block_family (U i) (V i) (hr i) (P i)
    exact ⟨n, r, hn, hrk, fun z hz => hmem (z i) ((hPmem i (z i)).mpr ⟨z, hz, rfl⟩)⟩

end PEqualNP.Outside.L_meta_33629

theorem PEqualNP.Outside.L_meta_33629 :
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
  let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    C.gates.foldl (fun (ds : List ℕ) g =>
      ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
      (List.replicate width 0)
  let F := ZMod 2
  ∀ (l : ℕ) (d : Fin l → ℕ),
    let I := Σ i : Fin l, Fin (2 * d i)
    let T := Matrix I I F
    let W := Fin l → Fin 2 → F
    ∀ (U V : (i : Fin l) → Matrix (Fin (2 * d i)) (Fin (2 * d i)) F),
      (∀ i, (U i).rank = 2*d i ∧ (V i).rank = 2*d i ∧
        (U i + V i).rank = 2*d i) →
      ∀ (S : Submodule F T) (Q : Submodule F W),
        S = Submodule.span F {A : T | A ∈ S ∧ A.rank ≤ 2} →
        let dimension := fun i : Fin l =>
          Module.finrank F (Submodule.span F {v : Fin 2 → F | ∃ z ∈ Q, z i = v})
        let cost := Module.finrank F S + ∑ i,
          if dimension i = 0 then 0 else if dimension i = 1 then 2*d i else 3*d i
        let K := fun (z : W) =>
          Matrix.blockDiagonal' (fun i => z i 0 • U i + z i 1 • V i)
        let w := Fintype.card (I ⊕ I)
        let coord := Fintype.equivFin (I ⊕ I)
        let table := fun (A : T) (z : W) (x y : Fin (w+1)) =>
          let X := Matrix.fromBlocks A (K z) (K z).transpose (0 : T)
          Fin.cases false (fun i => Fin.cases false (fun j =>
            decide (X (coord.symm i) (coord.symm j) ≠ 0)) y) x
        ∀ t : ℕ,
          (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : T → W → ℕ),
            PEqualNP.MetaComplexity.NestedCover.ReadsBack ((w+1)+(w+1)) C ∧
            (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
            ∀ A ∈ S, ∀ z ∈ Q,
              (depths ((w+1)+(w+1)) C).getD (tap A z) 0 ≤ 1 ∧
              PEqualNP.Represents.Represents (table A z) ⟨C.gates, tap A z⟩) ↔ cost ≤ t := by
  intro nonlinear depths F l d I T W U V hr S Q hS dimension cost K w coord table t
  exact PEqualNP.Outside.L_meta_33629.main d U V hr S Q hS t
