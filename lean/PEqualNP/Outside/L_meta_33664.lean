import Mathlib.Combinatorics.Hall.Finite
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33664

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
    rcases zmod2_cases (u i) with h1 | h1 <;> rcases zmod2_cases (v i) with h2 | h2 <;>
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
  obtain ⟨α2, β2, h2⟩ := hB
  refine ⟨fun a => α1 a + α2 a, fun b => β1 b + β2 b, fun a b => ?_⟩
  simp only [Matrix.add_apply, h1, h2]
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
    · intro i h1 h2; simp
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
    ∃ (D : Finset (Fin C.gates.length)), D ⊆ liveSet C ∧ D.card ≤ t ∧
      (∀ j ∈ D, (actualR coord C j).rank ≤ 2) ∧
      ∀ z, ∃ c : Fin C.gates.length → F, Target z = ∑ j ∈ D, c j • actualR coord C j := by
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
  refine ⟨shallowSet (n + n) C, hsub, ?_, ?_, ?_⟩
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
    exact ⟨c,htz⟩

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

private def IsProduct (w : ℕ) (gs : List Gate) (v : ℕ) : Prop :=
  ∃ j : Fin gs.length, nonlinear (gs.get j) = true ∧ v = w + j.val

private lemma product_prefix {w v : ℕ} {gs gs' : List Gate} (hp : gs <+: gs') :
    IsProduct w gs v → IsProduct w gs' v := by
  obtain ⟨tail, rfl⟩ := hp
  rintro ⟨j, hn, hv⟩
  refine ⟨⟨j.val, by simp; omega⟩, ?_, hv⟩
  simpa [List.get_eq_getElem, List.getElem_append_left, j.isLt] using hn

private lemma exists_xorList (w : ℕ) (gs : List Gate) (ws : List ℕ) (D : ℕ)
    (hgood : goodGates w gs) (hws : ∀ u ∈ ws, u < w + gs.length)
    (hdep : ∀ u ∈ ws, (depthsOf w gs).getD u 0 ≤ D) :
    ∃ (gs' : List Gate) (out : ℕ),
      (gs <+: gs') ∧ gs.length ≤ gs'.length ∧ goodGates w gs' ∧
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
    refine ⟨_, _, ⟨_, rfl⟩, h.1, h.2.1, h.2.2.1, h.2.2.2.1, by rw [h.2.2.2.2.1]; omega, h.2.2.2.2.2.1,
      fun x hx => ⟨(h.2.2.2.2.2.2 x hx).1, by rw [(h.2.2.2.2.2.2 x hx).2]; simp [b2z]⟩⟩
  | cons a t ih =>
    have ha : a < w + gs.length := hws a List.mem_cons_self
    have ha_dep : (depthsOf w gs).getD a 0 ≤ D := hdep a List.mem_cons_self
    rcases ih (fun u hu => hws u (List.mem_cons_of_mem a hu))
      (fun u hu => hdep u (List.mem_cons_of_mem a hu)) with
      ⟨gs1, out1, hpref, hlen1, hgood1, hcnt1, hout1, hdep1, hdpref1, hval1⟩
    have h2 := append_xor2 w gs1 a out1 hgood1 (by omega) hout1
    refine ⟨_, _, hpref.trans ⟨_, rfl⟩, by omega, h2.2.1, by rw [h2.2.2.1, hcnt1], h2.2.2.2.1, ?_, ?_, ?_⟩
    · rw [h2.2.2.2.2.1, hdpref1 a ha]
      exact max_le ha_dep hdep1
    · intro k hk
      rw [h2.2.2.2.2.2.1 k (by omega), hdpref1 k hk]
    · intro x hx
      refine ⟨fun k hk => by rw [(h2.2.2.2.2.2.2 x hx).1 k (by omega), (hval1 x hx).1 k hk], ?_⟩
      rw [(h2.2.2.2.2.2.2 x hx).2, b2z_xor, (hval1 x hx).1 a ha, (hval1 x hx).2]
      simp

private lemma synth_depth1_quads (n m q : ℕ) (qs : List (Quad n m))
    (mask : Fin q → Fin qs.length → F)
    (α : Fin q → Fin n → F) (β : Fin q → Fin m → F) :
    ∃ (C : Circuit) (tap : Fin q → ℕ),
      ReadsBack (n + m) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP nonlinear ≤ qs.length ∧
      (∃ prodW : Fin qs.length → ℕ, Function.Injective prodW ∧
        (∀ p, IsProduct (n+m) C.gates (prodW p)) ∧
        ∀ p x y, b2z ((wiresOf C.gates (oneEach x y)).getD (prodW p) false) =
          let qp := qs.get p
          (qp.1 x + qp.2.2.2 y) * (qp.2.2.1 x + qp.2.1 y)) ∧
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
        (gs <+: gs') ∧ gs.length ≤ gs'.length ∧ goodGates (n + m) gs' ∧
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
      ⟨gs', out, hpref, hlen, hgood', hcnt, hout, hdep, hdpref, hval⟩
    refine ⟨gs', out, hpref, hlen, hgood', hcnt, hout, by omega, hdpref, fun x y => ?_⟩
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
        Function.Injective prodW ∧ (∀ p, IsProduct (n+m) gs (prodW p)) ∧
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
        (fun p => Fin.elim0 p), (fun p => Fin.elim0 p), fun p => Fin.elim0 p, fun p => Fin.elim0 p, fun p => Fin.elim0 p⟩
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨gs, prodW, hgood, hcnt, hinj, hprod, hlt, hdep, heval⟩
      let qk := qs.get ⟨k, by omega⟩
      rcases hbuild_aff gs qk.1 qk.2.2.2 hgood with
        ⟨gs1, w1, hp1, hlen1, hgood1, hcnt1, hw1, hdep1, hdpref1, hval1⟩
      rcases hbuild_aff gs1 qk.2.2.1 qk.2.1 hgood1 with
        ⟨gs2, w2, hp2, hlen2, hgood2, hcnt2, hw2, hdep2, hdpref2, hval2⟩
      have h3 := append_and2 (n + m) gs2 w1 w2 hgood2 (by omega) hw2
      let gs3 := gs2 ++ [⟨GateOp.and, [w1, w2]⟩]
      let out := (n + m) + gs2.length
      let prodW' : Fin (k + 1) → ℕ :=
        fun p => if hp : p.val < k then prodW ⟨p.val, hp⟩ else out
      refine ⟨gs3, prodW', h3.2.1, by rw [h3.2.2.1, hcnt2, hcnt1, hcnt], ?_, ?_, ?_, ?_, ?_⟩
      · intro p r h
        by_cases hp : p.val < k <;> by_cases hr : r.val < k
        · simp only [prodW', dif_pos hp, dif_pos hr] at h
          exact Fin.ext (congrArg (Fin.val (n := k)) (hinj h))
        · simp only [prodW', dif_pos hp, dif_neg hr, out] at h
          have := hlt ⟨p.val,hp⟩
          omega
        · simp only [prodW', dif_neg hp, dif_pos hr, out] at h
          have := hlt ⟨r.val,hr⟩
          omega
        · exact Fin.ext (by omega)
      · intro p
        by_cases hp : p.val < k
        · simp only [prodW', dif_pos hp]
          exact product_prefix ((hp1.trans hp2).trans ⟨_,rfl⟩) (hprod _)
        · simp only [prodW', dif_neg hp]
          refine ⟨⟨gs2.length, by simp [gs3]⟩, ?_, rfl⟩
          simp [gs3, List.get_eq_getElem, nonlinear]
          decide
      · intro p
        by_cases hp : p.val < k
        · simp only [prodW', dif_pos hp]
          have h1 := hlt ⟨p.val, hp⟩
          have hlen3 : gs3.length = gs2.length + 1 := by simp [gs3]
          omega
        · simp only [prodW', dif_neg hp]; exact h3.2.2.2.1
      · intro p
        by_cases hp : p.val < k
        · simp only [prodW', dif_pos hp]
          rw [h3.2.2.2.2.2.1 _ (by have := hlt ⟨p.val, hp⟩; omega),
            hdpref2 _ (by have := hlt ⟨p.val, hp⟩; omega),
            hdpref1 _ (hlt ⟨p.val, hp⟩)]
          exact hdep ⟨p.val, hp⟩
        · simp only [prodW', dif_neg hp]
          rw [h3.2.2.2.2.1, hdpref2 w1 hw1, hdep1, hdep2]
          decide
      · intro p x y
        by_cases hp : p.val < k
        · simp only [prodW', dif_pos hp]
          have hltp := hlt ⟨p.val, hp⟩
          rw [(h3.2.2.2.2.2.2 (oneEach x y) (oneEach_length x y)).1 _ (by omega),
            (hval2 x y).1 _ (by omega), (hval1 x y).1 _ hltp]
          exact heval ⟨p.val, hp⟩ x y
        · have hpk : p.val = k := by omega
          simp only [prodW', dif_neg hp]
          rw [(h3.2.2.2.2.2.2 (oneEach x y) (oneEach_length x y)).2, b2z_and,
            (hval2 x y).1 w1 hw1, (hval1 x y).2, (hval2 x y).2]
          have hqeq : qs.get ⟨p.val, by omega⟩ = qk := by
            dsimp only [qk]; congr 1; exact Fin.ext (by dsimp only; omega)
          rw [hqeq]
  rcases hstage1 qs.length le_rfl with ⟨gs1, prodW, hgood1, hcnt1, hpinj, hpprod, hplt1, hpdep1, hpeval1⟩
  have hstage2 : ∀ (k : ℕ) (hk : k ≤ q),
      ∃ (gs : List Gate) (tap : Fin k → ℕ),
        (gs1 <+: gs) ∧ gs1.length ≤ gs.length ∧
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
      refine ⟨gs1, Fin.elim0, ⟨[],by simp⟩, le_rfl, hgood1, hcnt1, hpdep1, hpeval1,
        fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨gs, tap, hp0, hlen, hgood, hcnt, hpdep, hpeval, htlt, htdep, hteval⟩
      let jk : Fin q := ⟨k, by omega⟩
      let α' : Fin n → F := fun x =>
        α jk x + ∑ p : Fin qs.length, mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)
      let β' : Fin m → F := fun y =>
        β jk y + ∑ p : Fin qs.length, mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)
      rcases hbuild_aff gs α' β' hgood with
        ⟨gsA, wA, hpA, hlenA, hgoodA, hcntA, hwA, hdepA, hdprefA, hvalA⟩
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
        ⟨gsB, out, hpB, hlenB, hgoodB, hcntB, houtB, hdepB, hdprefB, hvalB⟩
      let tap' : Fin (k + 1) → ℕ := fun j => if hj : j.val < k then tap ⟨j.val, hj⟩ else out
      refine ⟨gsB, tap', (hp0.trans hpA).trans hpB, by omega, hgoodB, by rw [hcntB, hcntA, hcnt], ?_, ?_, ?_, ?_, ?_⟩
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
            have h2 := zmod2_add_self (mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y))
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
                    rw [h1, h2, zero_add, zero_add]
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
  rcases hstage2 q le_rfl with ⟨gs2, tap, hp2, _, hgood2, hcnt2, _, hpval, _, htdep2, hteval2⟩
  refine ⟨⟨gs2, 0⟩, tap, hgood2.1, hgood2.2, le_of_eq hcnt2,
    ⟨prodW,hpinj,fun p => product_prefix hp2 (hpprod p),hpval⟩, fun j => ⟨htdep2 j, hteval2 j⟩⟩

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
      (∃ e : ι ≃ ↥(liveSet C), ∀ p, actualR coord C (e p).val = R p) ∧
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
  obtain ⟨C, tap, hrb, hfan, hcnt, hproducts, hout⟩ := synth_depth1_quads (d + 1) (d + 1) (Fintype.card κ) qs
    (fun k p => c (ek.symm k) (eqs p)) (fun _ _ => 0) (fun _ _ => 0)
  obtain ⟨v, hvi, hv, hev⟩ := hproducts
  choose g hg hvg using hv
  let f (p : Fin qs.length) : ↥(liveSet C) := ⟨g p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg p⟩⟩
  have hf : Function.Injective f := by
    intro i j h
    apply hvi
    rw [hvg, hvg]
    exact congrArg (fun a : ↥(liveSet C) => (d+1)+(d+1)+a.val.val) h
  have hc' : Fintype.card (Fin qs.length) = Fintype.card ↥(liveSet C) := by
    apply Nat.le_antisymm (Fintype.card_le_of_injective f hf)
    simpa only [Fintype.card_fin, Fintype.card_coe, card_liveSet] using hcnt
  let eg := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hc'⟩)
  have hactual (p : Fin qs.length) : actualR coord C (g p) = R (eqs p) := by
    ext x y
    have hp (i j : Fin (d+1)) := hev p i j
    simp only [hvg, hget] at hp
    change b2z (xor (xor _ _) (xor _ _)) = _
    rw [b2z_xor,b2z_xor,b2z_xor]
    simp only [Circuit.eval]
    change b2z ((wiresOf _ _).getD _ _) + b2z ((wiresOf _ _).getD _ _) +
      (b2z ((wiresOf _ _).getD _ _) + b2z ((wiresOf _ _).getD _ _)) = _
    rw [hp,hp,hp,hp]
    simp only [padQuad, Fin.cases_succ, Fin.cases_zero, add_zero, zero_add, zero_mul]
    have h := hu (eqs p) (coord x) (coord y)
    simp only [Equiv.symm_apply_apply,evalQuad] at h
    rw [← h]
    generalize (u (eqs p)).1 (coord x) = A
    generalize (u (eqs p)).2.1 (coord y) = B
    generalize (u (eqs p)).2.2.1 (coord x) = E
    generalize (u (eqs p)).2.2.2 (coord y) = D
    revert A B E D
    decide
  have htracking : ∃ e : ι ≃ ↥(liveSet C), ∀ p, actualR coord C (e p).val = R p := by
    refine ⟨eqs.symm.trans eg,fun p => ?_⟩
    change actualR coord C (g (eqs.symm p)) = R p
    simpa only [Equiv.apply_symm_apply] using hactual (eqs.symm p)
  refine ⟨C, fun k => tap (ek k), hrb, hfan, hcnt.trans hlen.le, htracking, fun k =>
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

def dot {q : ℕ} (a z : Fin q → F) : F := ∑ j, a j * z j

lemma dot_comm {q : ℕ} (a z : Fin q → F) : dot a z = dot z a := by
  unfold dot
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma dot_zero_left {q : ℕ} (z : Fin q → F) : dot 0 z = 0 := by
  simp [dot]

lemma dot_zero_right {q : ℕ} (a : Fin q → F) : dot a 0 = 0 := by
  simp [dot]

lemma dot_add_left {q : ℕ} (a b z : Fin q → F) : dot (a + b) z = dot a z + dot b z := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dot_add_right {q : ℕ} (a z w : Fin q → F) : dot a (z + w) = dot a z + dot a w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dot_single_right {q : ℕ} (a : Fin q → F) (k : Fin q) :
    dot a (Pi.single k 1) = a k := by
  classical
  simp [dot, Pi.single_apply, mul_ite]

private lemma finrank_map_eq_of_inj {V W : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F V] [FiniteDimensional F W]
    {f : V →ₗ[F] W} (hf : Function.Injective f) (S : Submodule F V) :
    Module.finrank F (S.map f) = Module.finrank F S := by
  have h : LinearMap.range (f.comp S.subtype) = S.map f := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← h]
  exact LinearMap.finrank_range_of_inj (hf.comp Subtype.val_injective)

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
      have h2 : B2.card = 2 ^ (2 * k) := by rw [← hW2_dim]; exact card_submodule_eq_two_pow W2
      have h3 : B3.card = 2 ^ (2 * k) := by rw [← hW3_dim]; exact card_submodule_eq_two_pow W3
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

open Finset

abbrev BlockIndex {l : ℕ} (s : Fin l → ℕ) := (i : Fin l) × Fin (2*s i)
abbrev BlockM (n : ℕ) := Matrix (Fin (2*n)) (Fin (2*n)) F
abbrev Position {l : ℕ} (s : Fin l → ℕ) := (i : Fin l) × Fin (s i)
abbrev Slots {l q : ℕ} (s : Fin l → ℕ) (line : Fin l → Finset (Fin q → F)) :=
  (x : Position s) × ↥(line x.1)

private lemma lineFacts {q : ℕ} {a b : Fin q → F} (ha : a ≠ 0) (hb : b ≠ 0) (hn : a ≠ b) :
    a ≠ a+b ∧ b ≠ a+b ∧ ({a,b,a+b} : Finset _).card = 3 := by
  have h1 : a ≠ a+b := fun h => hb (add_left_cancel (show a+b = a+0 by simpa using h.symm))
  have h2 : b ≠ a+b := fun h => ha (add_right_cancel (show a+b = 0+b by simpa using h.symm))
  exact ⟨h1,h2,by simp [hn,h1,h2]⟩

private lemma rankPieces {n : ℕ} (P : BlockM n) (h : P.rank = n) :
    ∃ R : Fin n → BlockM n, (∀ j, (R j).rank ≤ 1) ∧ P = ∑ j, R j := by
  obtain ⟨a,b,hab⟩ := matrix_rank_decomp P
  let e := finCongr h
  refine ⟨fun j => Matrix.vecMulVec (a (e.symm j)) (b (e.symm j)),
    fun _ => Matrix.rank_vecMulVec_le _ _, ?_⟩
  exact hab.trans (e.symm.sum_comp _).symm

set_option maxHeartbeats 1200000 in
private lemma localPieces {q n : ℕ} (a b : Fin q → F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hn : a ≠ b) (U W : BlockM n) (hr : U.rank = 2*n ∧ W.rank = 2*n ∧ (U+W).rank = 2*n) :
    ∃ R : (Fin q → F) → Fin n → BlockM n, (∀ u j, (R u j).rank ≤ 1) ∧
      ∀ z, dot a z • U + dot b z • W =
        ∑ u ∈ ({a,b,a+b} : Finset _), ∑ j, dot u z • R u j := by
  classical
  obtain ⟨A,B,D,hAB,hBD,hsize⟩ := plane_three_decomp U W
    (by simpa only [Fintype.card_fin] using hr.1) (by simpa only [Fintype.card_fin] using hr.2.1) (by simpa only [Fintype.card_fin] using hr.2.2)
  simp only [Fintype.card_fin] at hsize
  have hAD : U+W = A+D := by rw [← hAB, ← hBD, ← add_assoc, add_assoc A B B, mat_add_self, add_zero]
  have h1 := matrix_rank_add_le A B
  have h2 := matrix_rank_add_le B D
  have h3 := matrix_rank_add_le A D
  rw [hAB,hr.1] at h1
  rw [hBD,hr.2.1] at h2
  rw [← hAD,hr.2.2] at h3
  obtain ⟨X,hX,eX⟩ := rankPieces (n := n) A (by omega)
  obtain ⟨Y,hY,eY⟩ := rankPieces (n := n) B (by omega)
  obtain ⟨Z,hZ,eZ⟩ := rankPieces (n := n) D (by omega)
  obtain ⟨ha',hb',_⟩ := lineFacts ha hb hn
  let R (u : Fin q → F) := if u = a then X else if u = b then Z else Y
  refine ⟨R, ?_, ?_⟩
  · intro u j
    dsimp only [R]
    split_ifs
    · exact hX j
    · exact hZ j
    · exact hY j
  intro z
  rw [Finset.sum_insert (show a ∉ ({b,a+b} : Finset _) by simp [hn,ha']),
    Finset.sum_insert (show b ∉ ({a+b} : Finset _) by simp [hb']), Finset.sum_singleton]
  simp only [R, if_true, if_pos rfl, if_neg (Ne.symm hn), if_neg (Ne.symm ha'), if_neg (Ne.symm hb'),
    ← Finset.smul_sum]
  rw [← eX, ← eY, ← eZ, ← hAB, ← hBD, dot_add_left, add_smul, smul_add, smul_add]
  abel

private lemma layer_wrong {l : ℕ} {s : Fin l → ℕ} {i : Fin l} (M : BlockM (s i))
    (x y : BlockIndex s) (h : x.1 ≠ i ∨ y.1 ≠ i) :
    layer (Sigma.mk i) (Sigma.mk i) M x y = 0 := by
  rw [layer_apply]
  apply Finset.sum_eq_zero
  intro p _
  apply Finset.sum_eq_zero
  intro r _
  exact if_neg (fun ⟨hx,hy⟩ => h.elim (fun hn => hn (congrArg Sigma.fst hx))
    (fun hn => hn (congrArg Sigma.fst hy)))

private lemma sum_layers {l : ℕ} {s : Fin l → ℕ} (M : (i : Fin l) → BlockM (s i)) :
    Matrix.blockDiagonal' M = ∑ i, layer (Sigma.mk i) (Sigma.mk i) (M i) := by
  classical
  ext ⟨i,x⟩ ⟨j,y⟩
  rw [Matrix.sum_apply, Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst j
      rw [Matrix.blockDiagonal'_apply_eq,layer_apply]
      simp [ite_and]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,layer_wrong _ _ _ (Or.inr (Ne.symm h))]
  · intro b _ h
    exact layer_wrong _ _ _ (Or.inl (Ne.symm h))
  · simp

set_option maxHeartbeats 1600000 in
private lemma allPieces {q l : ℕ} (s : Fin l → ℕ) (a b : Fin l → Fin q → F)
    (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (U W : (i : Fin l) → BlockM (s i))
    (hr : ∀ i, (U i).rank=2*s i ∧ (W i).rank=2*s i ∧ (U i+W i).rank=2*s i) :
    let line := fun i => ({a i,b i,a i+b i} : Finset _)
    ∃ R : Slots s line → Matrix (BlockIndex s) (BlockIndex s) F,
      (∀ p, (R p).rank ≤ 1) ∧ (∀ p x y, R p x y ≠ 0 → x.1 = p.1.1) ∧
      ∀ z, Matrix.blockDiagonal' (fun i => dot (a i) z • U i + dot (b i) z • W i) =
        ∑ p, dot p.2.val z • R p := by
  intro line
  classical
  choose T hT hdec using fun i => localPieces (a i) (b i) (hab i).1 (hab i).2.1
    (hab i).2.2 (U i) (W i) (hr i)
  let R (p : Slots s line) : Matrix (BlockIndex s) (BlockIndex s) F := layer (Sigma.mk p.1.1) (Sigma.mk p.1.1) (T p.1.1 p.2.val p.1.2)
  refine ⟨R, fun p => (layer_rank _ _ _).trans (hT _ _ _), ?_, ?_⟩
  · intro p x y h
    by_contra hn
    exact h (layer_wrong _ _ _ (Or.inl hn))
  · intro z
    rw [sum_layers, Fintype.sum_sigma, Fintype.sum_sigma]
    change (∑ i, _) = ∑ i : Fin l, ∑ j : Fin (s i), ∑ u : ↥(line i), _
    apply Finset.sum_congr rfl
    intro i _
    let emb : Fin (2*s i) → BlockIndex s := fun x => ⟨i,x⟩
    let E := layer emb emb
    change E _ = ∑ j : Fin (s i), ∑ u : ↥(line i), dot u.val z • E (T i u.val j)
    rw [hdec i]
    simp only [map_sum,map_smul, RingHom.id_apply]
    rw [Finset.sum_comm (s := line i) (t := univ)]
    apply Finset.sum_congr rfl
    intro j _
    exact (Finset.sum_coe_sort (line i) (fun u => dot u z • E (T i u j))).symm

private lemma pairEquiv {A : Type} [Fintype A] (m : A → A)
    (hm : Function.Involutive m) (hn : ∀ x, m x ≠ x) :
    ∃ (S : Finset A) (e : (↥S ⊕ ↥S) ≃ A), ∀ x, e (Sum.inr x) = m (e (Sum.inl x)) := by
  classical
  let ix := Fintype.equivFin A
  let S := univ.filter (fun x => ix x < ix (m x))
  let f : (↥S ⊕ ↥S) → A := Sum.elim Subtype.val (fun x => m x.val)
  have hlt (x : ↥S) : ix x.val < ix (m x.val) := (mem_filter.mp x.property).2
  have hi : Function.Injective f := by
    rintro (x|x) (y|y) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · change x.val = m y.val at h
      have H := hlt x
      rw [h,hm] at H
      exact (lt_asymm H (hlt y)).elim
    · change m x.val = y.val at h
      have H := hlt y
      rw [← h,hm] at H
      exact (lt_asymm H (hlt x)).elim
    · exact congrArg Sum.inr (Subtype.ext (hm.injective h))
  have hs : Function.Surjective f := by
    intro x
    rcases lt_or_gt_of_ne (fun h : ix x = ix (m x) => hn x (ix.injective h).symm) with h|h
    · exact ⟨Sum.inl ⟨x,mem_filter.mpr ⟨mem_univ _,h⟩⟩,rfl⟩
    · refine ⟨Sum.inr ⟨m x,mem_filter.mpr ⟨mem_univ _,by rwa [hm]⟩⟩,hm x⟩
  exact ⟨S,Equiv.ofBijective f ⟨hi,hs⟩,fun _ => rfl⟩

private lemma slotCount {q l : ℕ} (s : Fin l → ℕ) (line : Fin l → Finset (Fin q → F))
    (P : (Fin q → F) → Position s → Prop) [DecidableRel P] :
    (∑ u, (univ.filter fun x : Position s => u ∈ line x.1 ∧ P u x).card) =
      ∑ p : Slots s line, if P p.2.val p.1 then 1 else 0 := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm,Fintype.sum_sigma (f := fun p : Slots s line => if P p.2.val p.1 then 1 else 0)]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_coe_sort (line x.1) (fun u => if P u x then 1 else 0)]
  simp [ite_and, ← Finset.sum_filter]

private def forbidden {l : ℕ} {s : Fin l → ℕ} (near : Fin l → Fin l → Bool)
    (A : Matrix (BlockIndex s) (BlockIndex s) F) : Prop :=
  ∃ x y x' y', near x.1 x'.1 = false ∧ A x y ≠ 0 ∧ A x' y' ≠ 0

private lemma crossing_eq {l : ℕ} {s : Fin l → ℕ} {d : ℕ} (coord : BlockIndex s ≃ Fin d)
    (near : Fin l → Fin l → Bool) (C : Circuit) :
    let mix (j : Fin C.gates.length) (x y : BlockIndex s) :=
      let v (r c : Fin (d+1)) := (⟨C.gates,(d+1)+(d+1)+j.val⟩ : Circuit).eval (oneEach r c)
      xor (xor (v (coord x).succ (coord y).succ) (v (coord x).succ 0))
        (xor (v 0 (coord y).succ) (v 0 0))
    (∑ j, if nonlinear (C.gates.get j) then
      @ite ℕ (∃ x y x' y', near x.1 x'.1 = false ∧ mix j x y = true ∧ mix j x' y' = true)
        (Classical.propDecidable _) 1 0 else 0) =
      ∑ j : ↥(liveSet C), @ite ℕ (forbidden near (actualR coord C j.val)) (Classical.propDecidable _) 1 0 := by
  classical
  intro mix
  rw [Finset.sum_coe_sort (liveSet C) (fun j => if forbidden near (actualR coord C j) then 1 else 0),liveSet,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : nonlinear (C.gates.get j) = true
  · simp only [h,ite_true]
    congr 1
    apply propext
    have he (x y : BlockIndex s) : actualR coord C j x y ≠ 0 ↔ mix j x y = true := by
      change (if mix j x y then (1:F) else 0) ≠ 0 ↔ _
      cases mix j x y <;> decide
    simp only [forbidden,he]
  · simp only [if_neg h]

private lemma pairedCost {l : ℕ} {s : Fin l → ℕ}
    (near : Fin l → Fin l → Bool) (hrefl : ∀ i, near i i = true)
    (hsym : ∀ i j, near i j = near j i) (i j : Fin l)
    (X Y : Matrix (BlockIndex s) (BlockIndex s) F)
    (hX : ∀ x y, X x y ≠ 0 → x.1 = i) (hY : ∀ x y, Y x y ≠ 0 → x.1 = j)
    (h : forbidden near (X+Y)) : near i j = false := by
  obtain ⟨x,y,x',y',hn,h1,h2⟩ := h
  have hc (r c) (h : (X+Y) r c ≠ 0) : r.1 = i ∨ r.1 = j := by
    by_cases hx : X r c = 0
    · exact Or.inr (hY r c (fun hy => h (by simp [Matrix.add_apply,hx,hy])))
    · exact Or.inl (hX _ _ hx)
  rcases hc _ _ h1 with h|h <;> rcases hc _ _ h2 with h'|h' <;>
    rw [h,h'] at hn
  · simp [hrefl] at hn
  · exact hn
  · rwa [hsym] at hn
  · simp [hrefl] at hn

private lemma buildPaired {q l : ℕ} (s : Fin l → ℕ)
    (line : Fin l → Finset (Fin q → F)) (hl : ∀ i, (line i).card = 3)
    (near : Fin l → Fin l → Bool) (hrefl : ∀ i, near i i = true)
    (hsym : ∀ i j, near i j = near j i)
    (R : Slots s line → Matrix (BlockIndex s) (BlockIndex s) F)
    (hr : ∀ p, (R p).rank ≤ 1) (hrow : ∀ p x y, R p x y ≠ 0 → x.1 = p.1.1)
    (K : (Fin q → F) → Matrix (BlockIndex s) (BlockIndex s) F)
    (hK : ∀ z, K z = ∑ p, dot p.2.val z • R p)
    (mate : (Fin q → F) → Position s → Position s)
    (hm : ∀ u x, u ∈ line x.1 → u ∈ line (mate u x).1 ∧ mate u x ≠ x ∧ mate u (mate u x) = x)
    (t k : ℕ) (ht : 2*t=3*∑ i, s i)
    (hk : (∑ u, (univ.filter (fun x : Position s => u ∈ line x.1 ∧ near x.1 (mate u x).1 = false)).card) ≤ 2*k) :
    let w := Fintype.card (BlockIndex s)
    let coord := Fintype.equivFin (BlockIndex s)
    ∃ (C : Circuit) (tap : (Fin q → F) → ℕ), ReadsBack ((w+1)+(w+1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
      (∑ j : ↥(liveSet C), @ite ℕ (forbidden near (actualR coord C j.val)) (Classical.propDecidable _) 1 0) ≤ k ∧
      ∀ z, (depths ((w+1)+(w+1)) C).getD (tap z) 0 ≤ 1 ∧ Represents (mkTable coord (K z)) ⟨C.gates,tap z⟩ := by
  intro w coord
  classical
  let m (p : Slots s line) : Slots s line := ⟨mate p.2.val p.1,⟨p.2.val,(hm _ _ p.2.property).1⟩⟩
  have slotExt {x y : Slots s line} (h : x.1=y.1) (h' : x.2.val=y.2.val) : x=y := by
    obtain ⟨x,u⟩ := x
    obtain ⟨y,v⟩ := y
    dsimp at h
    subst y
    exact congrArg (Sigma.mk x) (Subtype.ext h')
  have hmi : Function.Involutive m := by
    rintro ⟨x,⟨u,hu⟩⟩
    exact slotExt (hm u x hu).2.2 rfl
  have hmn (p : Slots s line) : m p ≠ p := fun h => (hm _ _ p.2.property).2.1 (congrArg Sigma.fst h)
  obtain ⟨S,e,he⟩ := pairEquiv m hmi hmn
  let left (v : ↥S) := e (Sum.inl v)
  let right (v : ↥S) := e (Sum.inr v)
  have hmate (v : ↥S) : right v = m (left v) := he v
  have hback (v : ↥S) : m (right v) = left v := by rw [hmate,hmi]
  let B (v : ↥S) := R (left v) + R (right v)
  have hBr (v : ↥S) : (B v).rank ≤ 2 := (matrix_rank_add_le _ _).trans (by have := hr (left v); have := hr (right v); omega)
  have hspan (z) : K z ∈ Submodule.span F (Set.range B) := by
    rw [hK,← e.sum_comp (fun p => dot p.2.val z • R p),Fintype.sum_sum_type,← Finset.sum_add_distrib]
    apply Submodule.sum_mem
    intro v _
    change dot (left v).2.val z • _ + dot (right v).2.val z • _ ∈ _
    have hmask : (right v).2.val = (left v).2.val := by rw [hmate]
    rw [hmask,← smul_add]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v,rfl⟩)
  obtain ⟨C,tap,hRB,hfan,hcnt,⟨g,hg⟩,hout⟩ := synth coord B K hBr hspan
  have hcard := Fintype.card_congr e
  have hcSlots : Fintype.card (Slots s line) = (∑ i, s i)*3 := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe,hl,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      Position,Fintype.card_sigma,Fintype.card_fin]
    norm_cast
  rw [hcSlots,Fintype.card_sum,Nat.mul_comm] at hcard
  have hsz : Fintype.card ↥S = t := by omega
  rw [hsz] at hcnt
  refine ⟨C,tap,hRB,hfan,hcnt,?_,hout⟩
  rw [← g.sum_comp (fun j => if forbidden near (actualR coord C j.val) then 1 else 0)]
  simp only [hg]
  let cost (p : Slots s line) : ℕ := if near p.1.1 (m p).1.1 = false then 1 else 0
  have hcost (v : ↥S) : cost (right v) = cost (left v) := by
    dsimp only [cost]
    rw [hback,← hmate,hsym]
  have hcut : (∑ p : Slots s line, cost p) ≤ 2*k := by
    simpa only [slotCount s line (fun u x => near x.1 (mate u x).1 = false)] using hk
  rw [← e.sum_comp cost,Fintype.sum_sum_type] at hcut
  change (∑ v, cost (left v)) + (∑ v, cost (right v)) ≤ _ at hcut
  simp only [hcost] at hcut
  have hle : (∑ v, if forbidden near (B v) then 1 else 0) ≤ ∑ v, cost (left v) := by
    apply Finset.sum_le_sum
    intro v _
    by_cases hv : forbidden near (B v)
    · have h := pairedCost near hrefl hsym _ _ _ _ (hrow (left v)) (hrow (right v)) hv
      simp [hv,cost,← hmate,h]
    · simp [hv]
  omega

abbrev X (q : ℕ) := Fin q → F
abbrev BI {l : ℕ} (s : Fin l → ℕ) := (i : Fin l) × Fin (2*s i)
abbrev Block {l : ℕ} (s : Fin l → ℕ) (i : Fin l) := Matrix (Fin (2*s i)) (Fin (2*s i)) F


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


abbrev K2 := ZMod 2
abbrev Vec (q : ℕ) := Fin q → K2


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


private lemma plane_zero_not_mem {q : ℕ} {a b : Fin q → F}
    (hab : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) : (0 : Fin q → F) ∉ ({a, b, a + b} : Finset (Fin q → F)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨hab.1.symm, hab.2.1.symm, ?_⟩
  intro h
  exact hab.2.2 ((vec_add_eq_zero_iff a b).mp h.symm)

private lemma plane_closed_add {q : ℕ} {a b : Fin q → F}
    {u v : Fin q → F}
    (hu : u ∈ ({a, b, a + b} : Finset (Fin q → F)))
    (hv : v ∈ ({a, b, a + b} : Finset (Fin q → F))) :
    u + v = 0 ∨ u + v ∈ ({a, b, a + b} : Finset (Fin q → F)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv ⊢
  rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rw [hu, hv]
  · exact Or.inl (vec_add_self a)
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl (by rw [← add_assoc, vec_add_self, zero_add])))
  · exact Or.inr (Or.inr (Or.inr (add_comm b a)))
  · exact Or.inl (vec_add_self b)
  · exact Or.inr (Or.inl (by rw [add_comm a b, ← add_assoc, vec_add_self, zero_add]))
  · exact Or.inr (Or.inr (Or.inl (by rw [add_comm a b, add_assoc, vec_add_self, add_zero])))
  · exact Or.inr (Or.inl (by rw [add_assoc, vec_add_self, add_zero]))
  · exact Or.inl (vec_add_self (a + b))

private lemma idempotent_full {n : ℕ} (M : BlockM n) (h : M*M=M) (hr : M.rank = 2*n) : M=1 := by
  let hu := Matrix.mulVec_surjective_iff_isUnit.mp (Matrix.mulVec_surjective_iff_rank_eq_card.mpr
    (show M.rank = Fintype.card (Fin (2*n)) by simpa using hr))
  exact hu.mul_left_cancel (show M*M=M*1 by rwa [mul_one])

private lemma forcedSupport {q l : ℕ} {G : Type} [Fintype G] (s : Fin l → ℕ)
    (a b : Fin l → X q) (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (U W : (i : Fin l) → Block s i)
    (hr : ∀ i, (U i).rank=2*s i ∧ (W i).rank=2*s i ∧ (U i+W i).rank=2*s i)
    (m : G → X q) (hm : ∀ j, m j ≠ 0) (R : G → Matrix (BI s) (BI s) F)
    (hR : ∀ j, (R j).rank ≤ 2)
    (hrep : ∀ z, pencil s a b U W z = ∑ j ∈ active m z, R j)
    (ht : 2*Fintype.card G ≤ 3*∑ i, s i) :
    2*Fintype.card G = 3*∑ i, s i ∧
    ∀ j x y, R j x y ≠ 0 → m j ∈ plane (a x.1) (b x.1) ∧ m j ∈ plane (a y.1) (b y.1) := by
  classical
  obtain ⟨hle,L,T,hLT,hproj⟩ := compress s a b hab U W hr m hm R hR hrep
  refine ⟨Nat.le_antisymm ht hle,?_⟩
  have h1 (i) : L i = 1 ∧ T i = 1 := by
    obtain ⟨hL,hT,h⟩ := hLT i
    have hl := (L i).rank_le_card_width
    have ht' := (T i).rank_le_card_width
    simp only [Fintype.card_fin] at hl ht'
    exact ⟨idempotent_full _ hL (by omega), idempotent_full _ hT (by omega)⟩
  have hl : L=1 := funext fun i => (h1 i).1
  have ht' : T=1 := funext fun i => (h1 i).2
  simpa only [project,hl,ht',Matrix.blockDiagonal'_one,Matrix.one_mul,Matrix.mul_one] using hproj

private lemma plane_inter_unique {q : ℕ} {a b c d u v : X q}
    (hab : a≠0 ∧ b≠0 ∧ a≠b) (hcd : c≠0 ∧ d≠0 ∧ c≠d)
    (hne : plane a b ≠ plane c d) (hu : u ∈ plane a b) (hu' : u ∈ plane c d)
    (hv : v ∈ plane a b) (hv' : v ∈ plane c d) : u=v := by
  by_contra huv
  have hnU : u≠0 := fun h => plane_zero_not_mem hab (h ▸ hu)
  have hnV : v≠0 := fun h => plane_zero_not_mem hab (h ▸ hv)
  have hn : u+v≠0 := fun h => huv ((vec_add_eq_zero_iff _ _).mp h)
  have sub {a b : X q} (h : u ∈ plane a b) (h' : v ∈ plane a b) :
      plane u v ⊆ plane a b := by
    intro x hx
    simp only [plane,mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl|rfl
    · exact h
    · exact h'
    · exact (plane_closed_add h h').resolve_left hn
  have hc := (lineFacts hnU hnV huv).2.2
  apply hne
  have h1 : (plane a b).card = 3 := (lineFacts hab.1 hab.2.1 hab.2.2).2.2
  have h2 : (plane c d).card = 3 := (lineFacts hcd.1 hcd.2.1 hcd.2.2).2.2
  have h0 : (plane u v).card = 3 := hc
  exact (Finset.eq_of_subset_of_card_le (sub hu hv) (by omega)).symm.trans
    (Finset.eq_of_subset_of_card_le (sub hu' hv') (by omega))

private def byMask {q : ℕ} {G I : Type} [Fintype G] (m : G → X q) (R : G → Matrix I I F) (u : X q) :=
  ∑ j ∈ univ.filter (fun j => m j = u), R j

private lemma regroup {q : ℕ} {G I : Type} [Fintype G] (m : G → X q) (R : G → Matrix I I F) (z : X q) :
    ∑ j ∈ active m z, R j = ∑ u, dot u z • byMask m R u := by
  classical
  simp only [byMask,Finset.smul_sum,Finset.sum_filter,active]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (m j)]
  · rcases cases01 (dot (m j) z) with h|h <;> simp [h]
  · intro u _ hn
    simp [Ne.symm hn]
  · simp

private lemma maskData {q l : ℕ} {G : Type} [Fintype G] (s : Fin l → ℕ)
    (a b : Fin l → X q) (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (hi : Function.Injective (fun i => plane (a i) (b i)))
    (U W : (i : Fin l) → Block s i)
    (m : G → X q) (R : G → Matrix (BI s) (BI s) F)
    (hsp : ∀ j x y, R j x y ≠ 0 → m j ∈ plane (a x.1) (b x.1) ∧ m j ∈ plane (a y.1) (b y.1))
    (hrep : ∀ z, pencil s a b U W z = ∑ j ∈ active m z, R j) :
    let H := byMask m R
    let D := fun u i => (H u).submatrix (Sigma.mk i) (Sigma.mk i)
    (∀ u, H u = Matrix.blockDiagonal' (D u)) ∧
    (∀ u i, u ∉ plane (a i) (b i) → D u i = 0) ∧
    ∀ i, D (a i) i + D (a i+b i) i = U i ∧ D (b i) i + D (a i+b i) i = W i := by
  intro H D
  classical
  have hs (u) (x y : BI s) (h : H u x y ≠ 0) :
      u ∈ plane (a x.1) (b x.1) ∧ u ∈ plane (a y.1) (b y.1) := by
    change (byMask m R u) x y ≠ 0 at h
    simp only [byMask,Matrix.sum_apply] at h
    obtain ⟨j,hj,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact (Finset.mem_filter.mp hj).2 ▸ hsp j x y hn
  have hlin z : pencil s a b U W z = ∑ u, dot u z • H u := (hrep z).trans (regroup m R z)
  have hp (z) (x y : BI s) := congrArg (fun A : Matrix (BI s) (BI s) F => A x y) (hlin z)
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] at hp
  refine ⟨?_,?_,?_⟩
  · intro u
    ext x y
    by_cases hh : x.1=y.1
    · obtain ⟨i,x⟩ := x
      obtain ⟨j,y⟩ := y
      dsimp at hh
      subst j
      simp [D]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hh]
      by_contra hn
      obtain ⟨hx,hy⟩ := hs u x y hn
      have hu : u≠0 := fun h => plane_zero_not_mem (hab _) (h ▸ hx)
      have hk : ∃ k, u k ≠ 0 := by simpa [funext_iff] using hu
      obtain ⟨k,hk⟩ := hk
      have h := hp (Pi.single k 1) x y
      rw [pencil,Matrix.blockDiagonal'_apply_ne _ _ _ hh,Finset.sum_eq_single u] at h
      · rw [dot_single_right,(nz_one _).mp hk,one_mul] at h
        exact hn h.symm
      · intro v _ hv
        by_cases h0 : H v x y = 0
        · simp [h0]
        · obtain ⟨vx,vy⟩ := hs v x y h0
          exact (hv (plane_inter_unique (hab _) (hab _) (hi.ne hh) vx vy hx hy)).elim
      · simp
  · intro u i h
    ext x y
    exact Classical.byContradiction (fun hn => h (hs u ⟨i,x⟩ ⟨i,y⟩ hn).1)
  · intro i
    let P : Matrix (Fin 2) (Fin q) F := ![a i,b i]
    have hsur : Function.Surjective P.mulVec := by
      apply LinearIndependent.mulVec_surjective
      rw [Fintype.linearIndependent_iff]
      intro g hg k
      obtain ⟨ha,hb,hab⟩ := hab i
      rcases cases01 (g 0) with h0|h0 <;> rcases cases01 (g 1) with h1|h1 <;>
        simp [P,Fin.sum_univ_two,Matrix.row,h0,h1,vec_add_eq_zero_iff,ha,hb,hab] at hg
      fin_cases k <;> assumption
    obtain ⟨z,hz⟩ := hsur ![1,0]
    obtain ⟨w,hw⟩ := hsur ![0,1]
    have hz1 : dot (a i) z = 1 := congrFun hz 0
    have hz2 : dot (b i) z = 0 := congrFun hz 1
    have hw1 : dot (a i) w = 0 := congrFun hw 0
    have hw2 : dot (b i) w = 1 := congrFun hw 1
    have cut (t : X q) (x y : Fin (2*s i)) := hp t ⟨i,x⟩ ⟨i,y⟩
    have hcut (t : X q) (x y : Fin (2*s i)) :
        (dot (a i) t • U i + dot (b i) t • W i) x y =
          ∑ u ∈ plane (a i) (b i), dot u t * D u i x y := by
      rw [Finset.sum_subset (Finset.subset_univ (plane (a i) (b i))) (fun u _ hn => show dot u t * D u i x y = 0 by
        rw [show D u i x y = 0 from Classical.byContradiction (fun h => hn (hs _ _ _ h).1),mul_zero])]
      simpa [pencil,D] using cut t x y
    obtain ⟨h1,h2,_⟩ := lineFacts (hab i).1 (hab i).2.1 (hab i).2.2
    constructor <;> ext x y
    · simpa [plane,(hab i).2.2,h1,h2,dot_add_left,hz1,hz2] using (hcut z x y).symm
    · simpa [plane,(hab i).2.2,h1,h2,dot_add_left,hw1,hw2] using (hcut w x y).symm

private lemma rank_blocks_le {L : Type} [Fintype L] [DecidableEq L] {N : L → Type}
    [∀ i, Fintype (N i)] (D : (i : L) → Matrix (N i) (N i) F) :
    ∑ i, (D i).rank ≤ (Matrix.blockDiagonal' D).rank := by
  classical
  let B := Matrix.blockDiagonal' D
  let f : ((i : L) → LinearMap.range (D i).mulVecLin) →ₗ[F] LinearMap.range B.mulVecLin :=
    { toFun := fun x => ⟨(fun p => (x p.1).val p.2), by
        choose v hv using fun i => (x i).property
        refine ⟨fun p => v p.1 p.2, ?_⟩
        funext ⟨i,r⟩
        exact (blockVec D _ i r).trans (congrFun (hv i) r)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hi : Function.Injective f := by
    intro x y h
    funext i
    apply Subtype.ext
    funext r
    exact congrArg (fun z : LinearMap.range B.mulVecLin => z.val ⟨i,r⟩) h
  have h := LinearMap.finrank_le_finrank_of_injective hi
  rwa [Module.finrank_pi_fintype] at h

private lemma matchRows {l : ℕ} {G : Type} [Fintype G] (s : Fin l → ℕ)
    (D : (i : Fin l) → Block s i) (R : G → Matrix (BI s) (BI s) F)
    (hR : ∀ j, (R j).rank ≤ 2)
    (h : Matrix.blockDiagonal' D = ∑ j, R j) :
    ∃ f : ((i : Fin l) × Fin (D i).rank) → G × Fin 2,
      Function.Injective f ∧ ∀ p, ∃ x y : BI s, x.1 = p.1 ∧ R (f p).1 x y ≠ 0 := by
  classical
  let T := (i : Fin l) × Fin (D i).rank
  let visible (i : Fin l) (g : G) := ∃ x y : BI s, x.1=i ∧ R g x y ≠ 0
  let nb (p : T) := univ.filter (fun v : G × Fin 2 => visible p.1 v.1)
  suffices hall : ∀ A : Finset T, A.card ≤ (A.biUnion nb).card by
    obtain ⟨f,hf,hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' nb).mp hall
    exact ⟨f,hf,fun p => (mem_filter.mp (hmem p)).2⟩
  intro A
  let S := A.image Sigma.fst
  let N := univ.filter (fun g : G => ∃ i ∈ S, visible i g)
  have hnb : A.biUnion nb = N ×ˢ (univ : Finset (Fin 2)) := by
    ext ⟨g,c⟩
    simp only [nb,N,S,mem_biUnion,mem_product,mem_filter,mem_univ,true_and,and_true,mem_image]
    constructor
    · rintro ⟨p,hp,hv⟩
      exact ⟨p.1,⟨p,hp,rfl⟩,hv⟩
    · rintro ⟨_,⟨p,hp,rfl⟩,hv⟩
      exact ⟨p,hp,hv⟩
  let ix : ((i : ↥S) × Fin (2*s i.val)) → BI s := fun x => ⟨x.1.val,x.2⟩
  let P (g : G) := (R g).submatrix ix ix
  have hprod : Matrix.blockDiagonal' (fun i : ↥S => D i.val) = ∑ g ∈ N, P g := by
    have hsub : Matrix.blockDiagonal' (fun i : ↥S => D i.val) =
        (Matrix.blockDiagonal' D).submatrix ix ix := by
      ext ⟨i,x⟩ ⟨j,y⟩
      by_cases hi : i=j
      · subst j; simp [ix]
      · have hh : i.val≠j.val := fun h => hi (Subtype.ext h)
        simp only [ix,Matrix.submatrix_apply,Matrix.blockDiagonal'_apply_ne _ _ _ hi,
          Matrix.blockDiagonal'_apply_ne _ _ _ hh]
    rw [hsub,h]
    ext x y
    simp only [P,Matrix.submatrix_apply,Matrix.sum_apply]
    symm
    apply Finset.sum_subset (subset_univ _)
    intro g _ hg
    by_contra hn
    exact hg (mem_filter.mpr ⟨mem_univ _,x.1.val,x.1.property,ix x,ix y,rfl,hn⟩)
  have hdim := rank_blocks_le (fun i : ↥S => D i.val)
  rw [hprod] at hdim
  have hle := hdim.trans (matrix_rank_sum_le N P)
  have hlim : ∑ g ∈ N, (P g).rank ≤ N.card*2 := by
    calc _ ≤ ∑ _g ∈ N, 2 := sum_le_sum (fun g _ => (Matrix.rank_submatrix_le _ _ _).trans (hR g))
         _ = _ := by simp
  have hcard : A.card ≤ ∑ i : ↥S, (D i.val).rank := by
    let f (x : ↥A) : ((i : ↥S) × Fin (D i.val).rank) :=
      ⟨⟨x.val.1,mem_image_of_mem _ x.property⟩,x.val.2⟩
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (congrArg (fun p : ((i : ↥S) × Fin (D i.val).rank) =>
        (⟨p.1.val,p.2⟩ : T)) h)
    simpa using Fintype.card_le_of_injective f hf
  rw [hnb,Finset.card_product,card_univ,Fintype.card_fin]
  exact hcard.trans (hle.trans hlim)

private lemma pairRank {s a b c : ℕ} (h1 : 2*s ≤ a+c) (h2 : 2*s ≤ b+c)
    (h3 : 2*s ≤ a+b) : 3*s ≤ a+b+c ∧ (a+b+c=3*s → a=s ∧ b=s ∧ c=s) := by omega

private lemma allocate {q l : ℕ} {G : Type} [Fintype G] (s : Fin l → ℕ)
    (a b : Fin l → X q) (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (hi : Function.Injective (fun i => plane (a i) (b i)))
    (U W : (i : Fin l) → Block s i)
    (hr : ∀ i, (U i).rank=2*s i ∧ (W i).rank=2*s i ∧ (U i+W i).rank=2*s i)
    (m : G → X q) (R : G → Matrix (BI s) (BI s) F)
    (hR : ∀ j, (R j).rank ≤ 2) (hsize : 2*Fintype.card G = 3*∑ i, s i)
    (hsp : ∀ j x y, R j x y ≠ 0 → m j ∈ plane (a x.1) (b x.1) ∧ m j ∈ plane (a y.1) (b y.1))
    (hrep : ∀ z, pencil s a b U W z = ∑ j ∈ active m z, R j) :
    let line := fun i => plane (a i) (b i)
    ∃ e : Slots s line ≃ G × Fin 2, ∀ p, m (e p).1 = p.2.val ∧
      ∃ x y : BI s, x.1=p.1.1 ∧ R (e p).1 x y ≠ 0 := by
  intro line
  classical
  let H := byMask m R
  let D (u : X q) (i : Fin l) : Block s i := (H u).submatrix (fun r => ⟨i,r⟩) (fun r => ⟨i,r⟩)
  obtain ⟨hdiag,hout,hblock⟩ := maskData s a b hab hi U W m R hsp hrep
  let Gf (u : X q) := univ.filter (fun g : G => m g = u)
  have heq u : Matrix.blockDiagonal' (D u) = ∑ j : ↥(Gf u), R j.val := by
    rw [← hdiag,Finset.sum_coe_sort (Gf u) R]
    rfl
  choose f hf hv using fun u => matchRows s (D u) (fun j : ↥(Gf u) => R j.val)
    (fun j => hR j.val) (heq u)
  let d u i := (D u i).rank
  have hd u : ∑ i, d u i ≤ (Gf u).card * 2 := by
    simpa [Fintype.card_sigma,Fintype.card_prod,d] using Fintype.card_le_of_injective (f u) (hf u)
  have hcap : (∑ i, ∑ u, d u i) ≤ 3*∑ i, s i := by
    rw [Finset.sum_comm]
    refine (sum_le_sum (fun u _ => hd u)).trans_eq ?_
    rw [← Finset.sum_mul]
    have hc : ∑ u, (Gf u).card = Fintype.card G :=
      (Finset.card_eq_sum_card_fiberwise (f := m) (s := univ) (t := univ) (fun _ _ => mem_univ _)).symm.trans card_univ
    rw [hc,Nat.mul_comm,hsize]
  have hsum i : ∑ u, d u i = d (a i) i + d (b i) i + d (a i+b i) i := by
    rw [← Finset.sum_subset (subset_univ (line i)) (fun u _ h => show d u i = 0 by
      change (D u i).rank=0; rw [show D u i = 0 from hout _ _ h, Matrix.rank_zero])]
    obtain ⟨ha,hb,_⟩ := lineFacts (hab i).1 (hab i).2.1 (hab i).2.2
    simp [line,plane,(hab i).2.2,ha,hb,add_assoc]
  have hpair i := hblock i
  have hA (i) : 3*s i ≤ ∑ u, d u i ∧ ((∑ u, d u i) = 3*s i →
      d (a i) i=s i ∧ d (b i) i=s i ∧ d (a i+b i) i=s i) := by
    rw [hsum]
    apply pairRank
    · rw [← (hr i).1,← (hpair i).1]; apply matrix_rank_add_le
    · rw [← (hr i).2.1,← (hpair i).2]; apply matrix_rank_add_le
    · have h : U i+W i = D (a i) i+D (b i) i := by
        rw [← (hpair i).1,← (hpair i).2]
        calc _ = D (a i) i+D (b i) i+(D (a i+b i) i+D (a i+b i) i) := by abel
             _ = _ := by rw [mat_add_self,add_zero]
      rw [← (hr i).2.2,h]
      apply matrix_rank_add_le
  have hranks (u i) (hu : u ∈ line i) : d u i = s i := by
    have ht : (∑ v, d v i) = 3*s i := by
      by_contra hn
      have hlt := Finset.sum_lt_sum (s := (univ : Finset (Fin l))) (fun j _ => (hA j).1)
        ⟨i,mem_univ _,lt_of_le_of_ne (hA i).1 (Ne.symm hn)⟩
      rw [← Finset.mul_sum] at hlt
      omega
    obtain ⟨h1,h2,h3⟩ := (hA i).2 ht
    simp only [line,plane,mem_insert,mem_singleton] at hu
    rcases hu with rfl|rfl|rfl <;> assumption
  let pos (p : Slots s line) : (i : Fin l) × Fin (D p.2.val i).rank :=
    ⟨p.1.1,Fin.cast (hranks _ _ p.2.property).symm p.1.2⟩
  let g (p : Slots s line) : G × Fin 2 :=
    let v := f p.2.val (pos p)
    (v.1.val,v.2)
  have hmask (p : Slots s line) : m (g p).1 = p.2.val :=
    (mem_filter.mp (f p.2.val (pos p)).1.property).2
  have hg : Function.Injective g := by
    rintro ⟨⟨i,x⟩,⟨u,hu⟩⟩ ⟨⟨j,y⟩,⟨v,hv⟩⟩ h
    have hsame := (hmask _).symm.trans ((congrArg (fun t : G × Fin 2 => m t.1) h).trans (hmask _))
    change u=v at hsame
    subst v
    have he : pos ⟨⟨i,x⟩,⟨u,hu⟩⟩ = pos ⟨⟨j,y⟩,⟨u,hv⟩⟩ := by
      apply hf u
      apply Prod.ext
      · exact Subtype.ext (congrArg (fun w : G × Fin 2 => w.1) h)
      · exact congrArg (fun w : G × Fin 2 => w.2) h
    obtain rfl : i=j := congrArg Sigma.fst he
    have hxy : x.val = y.val := congrArg (fun p : (i : Fin l) × Fin (D u i).rank => p.2.val) he
    obtain rfl := Fin.ext hxy
    rfl
  have hl i : (line i).card=3 := (lineFacts (hab i).1 (hab i).2.1 (hab i).2.2).2.2
  have hc : Fintype.card (Slots s line) = Fintype.card (G × Fin 2) := by
    simp [Slots,Position,Fintype.card_sigma,Fintype.card_prod,hl]
    omega
  let e := Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg,hc⟩)
  exact ⟨e,fun p => ⟨hmask p,hv p.2.val (pos p)⟩⟩

private lemma mateOfAllocation {q l : ℕ} {G : Type} [Fintype G] (s : Fin l → ℕ)
    (line : Fin l → Finset (X q)) (near : Fin l → Fin l → Bool)
    (m : G → X q) (R : G → Matrix (BI s) (BI s) F)
    (e : Slots s line ≃ G × Fin 2) (he : ∀ p, m (e p).1=p.2.val ∧
      ∃ x y : BI s, x.1 = p.1.1 ∧ R (e p).1 x y ≠ 0) :
    ∃ mate : X q → Position s → Position s,
      (∀ u x, u ∈ line x.1 → u ∈ line (mate u x).1 ∧ mate u x ≠ x ∧ mate u (mate u x)=x) ∧
      (∑ u, (univ.filter fun x : Position s => u ∈ line x.1 ∧ near x.1 (mate u x).1 = false).card) ≤
        2 * ∑ j, @ite ℕ (forbidden near (R j)) (Classical.propDecidable _) 1 0 := by
  classical
  let sw (p : Slots s line) := e.symm ((e p).1,1-(e p).2)
  have hew (p) : e (sw p) = ((e p).1,1-(e p).2) := e.apply_symm_apply _
  have hsw (p) : sw (sw p)=p := by
    apply e.injective
    rw [hew,hew]
    have h (c : Fin 2) : 1-(1-c)=c := by revert c; decide
    simp [h]
  have hne (p) : sw p ≠ p := by
    intro h
    have heq := hew p
    rw [h] at heq
    have hh := congrArg Prod.snd heq
    exact (show ∀ c : Fin 2, c ≠ 1-c by decide) (e p).2 hh
  have hm (p) : (sw p).2.val = p.2.val := by rw [← (he _).1,hew]; exact (he p).1
  have hx {p r : Slots s line} (ha : p.1=r.1) (hb : p.2.val=r.2.val) : p=r := by
    obtain ⟨p,u⟩ := p
    obtain ⟨r,v⟩ := r
    dsimp at ha
    subst r
    exact congrArg (Sigma.mk p) (Subtype.ext hb)
  let mate (u : X q) (x : Position s) := if h : u ∈ line x.1 then (sw ⟨x,⟨u,h⟩⟩).1 else x
  have hmate (p : Slots s line) : mate p.2.val p.1 = (sw p).1 := by simp only [mate,dif_pos p.2.property]
  refine ⟨mate,?_,?_⟩
  · intro u x hu
    let p : Slots s line := ⟨x,⟨u,hu⟩⟩
    change p.2.val ∈ line (mate p.2.val p.1).1 ∧ mate p.2.val p.1 ≠ p.1 ∧
      mate p.2.val (mate p.2.val p.1) = p.1
    rw [hmate]
    refine ⟨hm p ▸ (sw p).2.property,fun h => hne p (hx h (hm p)),?_⟩
    calc mate p.2.val (sw p).1 = mate (sw p).2.val (sw p).1 := by rw [hm]
         _ = (sw (sw p)).1 := hmate _
         _ = _ := by rw [hsw]
  · rw [slotCount s line (fun u x => near x.1 (mate u x).1 = false)]
    let cost (p : Slots s line) : ℕ := if near p.1.1 (mate p.2.val p.1).1 = false then 1 else 0
    change ∑ p, cost p ≤ _
    have hcharge (p) : cost p ≤ if forbidden near (R (e p).1) then 1 else 0 := by
      dsimp only [cost]
      rw [hmate]
      split_ifs with h h' h'
      · rfl
      · exfalso
        obtain ⟨x,y,hx,hy⟩ := (he p).2
        obtain ⟨r,c,hr,hc⟩ := (he (sw p)).2
        rw [hew] at hc
        exact h' ⟨x,y,r,c,by rwa [hx,hr],hy,hc⟩
      · decide
      · rfl
    refine (sum_le_sum fun p _ => hcharge p).trans_eq ?_
    rw [e.sum_comp (fun v => if forbidden near (R v.1) then (1:ℕ) else 0),Fintype.sum_prod_type,Finset.mul_sum]
    apply sum_congr rfl
    intro j _
    by_cases h : forbidden near (R j) <;> simp [h]

private lemma readBank {q l : ℕ} (s : Fin l → ℕ)
    (a b : Fin l → X q) (hab : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (hi : Function.Injective (fun i => plane (a i) (b i)))
    (U W : (i : Fin l) → Block s i)
    (hr : ∀ i, (U i).rank=2*s i ∧ (W i).rank=2*s i ∧ (U i+W i).rank=2*s i)
    (near : Fin l → Fin l → Bool) (t k : ℕ) (ht : 2*t=3*∑ i, s i)
    (C : Circuit) (tap : X q → ℕ)
    (hRB : ReadsBack ((Fintype.card (BI s)+1)+(Fintype.card (BI s)+1)) C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hcnt : C.gates.countP nonlinear ≤ t)
    (hk : (∑ j : ↥(liveSet C), @ite ℕ (forbidden near (actualR (Fintype.equivFin (BI s)) C j.val))
      (Classical.propDecidable _) 1 0) ≤ k)
    (hout : ∀ z, (depths ((Fintype.card (BI s)+1)+(Fintype.card (BI s)+1)) C).getD (tap z) 0 ≤ 1 ∧
      Represents (mkTable (Fintype.equivFin (BI s)) (pencil s a b U W z)) ⟨C.gates,tap z⟩) :
    let line := fun i => plane (a i) (b i)
    ∃ mate : X q → Position s → Position s,
      (∀ u x, u ∈ line x.1 → u ∈ line (mate u x).1 ∧ mate u x ≠ x ∧ mate u (mate u x)=x) ∧
      (∑ u, (univ.filter fun x : Position s => u ∈ line x.1 ∧ near x.1 (mate u x).1 = false).card) ≤ 2*k := by
  classical
  intro line
  let R := actualR (Fintype.equivFin (BI s)) C
  obtain ⟨D,hsub,hsize,hR,hspan⟩ := extractSpan (Fintype.equivFin (BI s)) (pencil s a b U W)
    C tap hRB hfan hcnt hout
  obtain ⟨used,m,hud,hm,hrep⟩ := selectMask s a b U W D R hspan
  have hused := (card_le_card hud).trans hsize
  obtain ⟨hn,hsp⟩ := forcedSupport s a b hab U W hr (fun j : ↥used => m j.val)
    (fun j => hm _ j.property) (fun j => R j.val) (fun j => hR _ (hud j.property)) hrep
    (by rw [Fintype.card_coe]; omega)
  obtain ⟨e,he⟩ := allocate s a b hab hi U W hr (fun j : ↥used => m j.val)
    (fun j => R j.val) (fun j => hR _ (hud j.property)) hn hsp hrep
  obtain ⟨mate,h1,h2⟩ := mateOfAllocation s line near (fun j : ↥used => m j.val) (fun j => R j.val) e he
  have hcs : used = liveSet C := by
    apply Finset.eq_of_subset_of_card_le (hud.trans hsub)
    rw [Fintype.card_coe] at hn
    rw [card_liveSet]
    omega
  subst used
  exact ⟨mate,h1,h2.trans (Nat.mul_le_mul_left 2 hk)⟩

end PEqualNP.Outside.L_meta_33664

theorem PEqualNP.Outside.L_meta_33664 :
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
    Function.Injective line →
    ∀ (U W : (i : Fin l) → Matrix (Fin (2*s i)) (Fin (2*s i)) F),
      (∀ i, (U i).rank = 2*s i ∧ (W i).rank = 2*s i ∧ (U i + W i).rank = 2*s i) →
      let K := fun (z : V) =>
        Matrix.blockDiagonal' (fun i => dot (a i) z • U i + dot (b i) z • W i)
      ∀ t : ℕ, 2*t = 3*(∑ i, s i) →
        ∀ near : Fin l → Fin l → Bool, (∀ i, near i i = true) →
          (∀ i j, near i j = near j i) →
          let J := Σ i : Fin l, Fin (s i)
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
          let crossing := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
            ∑ j : Fin C.gates.length, if nonlinear (C.gates.get j) then
              @ite ℕ (∃ x y x' y' : I, near x.1 x'.1 = false ∧
                mixed C j x y = true ∧ mixed C j x' y' = true)
                (Classical.propDecidable _) 1 0 else 0
          ∀ k : ℕ,
            (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : V → ℕ),
              PEqualNP.MetaComplexity.NestedCover.ReadsBack width C ∧
              (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
              crossing C ≤ k ∧ ∀ z : V, (depths width C).getD (tap z) 0 ≤ 1 ∧
                PEqualNP.Represents.Represents (table z) ⟨C.gates,tap z⟩) ↔
              ∃ mate : V → J → J,
                (∀ u x, u ∈ line x.1 → u ∈ line (mate u x).1 ∧
                  mate u x ≠ x ∧ mate u (mate u x) = x) ∧
                (∑ u : V, (Finset.univ.filter (fun x : J =>
                  u ∈ line x.1 ∧ near x.1 (mate u x).1 = false)).card) ≤ 2*k) := by
  intro nonlinear depths F q l s V I M dot a b hab line hlines U W hr K t ht near hrefl hsym J w coord width table mixed crossing k
  constructor
  · intro H
    obtain ⟨C,tap,hrb,hfan,hcnt,hcost,htap⟩ := H
    apply PEqualNP.Outside.L_meta_33664.readBank s a b hab hlines U W hr near t k ht C tap hrb hfan hcnt _ htap
    exact (PEqualNP.Outside.L_meta_33664.crossing_eq coord near C).ge.trans hcost
  · rintro ⟨mate,hm,hk⟩
    obtain ⟨R,hR,hrow,hexp⟩ := PEqualNP.Outside.L_meta_33664.allPieces s a b hab U W hr
    have hl i := (PEqualNP.Outside.L_meta_33664.lineFacts (hab i).1 (hab i).2.1 (hab i).2.2).2.2
    obtain ⟨C,tap,hrb,hfan,hcnt,hcross,htap⟩ := PEqualNP.Outside.L_meta_33664.buildPaired
      s line hl near hrefl hsym R hR hrow K hexp mate hm t k ht hk
    exact ⟨C,tap,hrb,hfan,hcnt,(PEqualNP.Outside.L_meta_33664.crossing_eq coord near C).le.trans hcross,htap⟩
