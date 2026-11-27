import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_376_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def reads (g : Gate) (w : ℕ) : Prop :=
  (g.op = GateOp.not ∧ g.inputs.head? = some w) ∨
  (g.op ≠ GateOp.not ∧ w ∈ g.inputs)

def NormGate (g : Gate) : Prop :=
  (g.op = GateOp.not → g.inputs.length = 1) ∧
  (g.op ≠ GateOp.not → g.inputs.length = 2 ∧ g.inputs.Nodup)

theorem reads_iff_mem {g : Gate} (hn : NormGate g) (w : ℕ) :
    reads g w ↔ w ∈ g.inputs := by
  unfold reads
  by_cases hop : g.op = GateOp.not
  · have hlen := hn.1 hop
    rcases hg : g.inputs with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp [hg] at hlen
    · simp [hop, eq_comm]
    · simp [hg] at hlen
  · simp [hop]

def readGate (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

theorem foldl_snoc_keeps {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_initial {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_snoc_split {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).getD (init.length + j) d
      = F ((gs.take j).foldl (fun R g => R ++ [F R g]) init) gs[j] ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init) <+:
      gs.foldl (fun R g => R ++ [F R g]) init ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init).length = init.length + j := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [F R g]) init with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length F]; simp; omega
  have hpre : (P ++ [F P gs[j]]) <+: gs.foldl (fun R g => R ++ [F R g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_keeps F _ _
  refine ⟨?_, (List.prefix_append P _).trans hpre, hPl⟩
  rw [getD_of_initial hpre (by simp; omega), ← hPl]
  simp

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_snoc_length readGate C.gates x

theorem wires_low (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  getD_of_initial (foldl_snoc_keeps readGate C.gates x) hi false

theorem wires_past (C : Circuit) (x : List Bool) (i : ℕ) (hi : x.length + C.gates.length ≤ i) :
    (C.wires x).getD i false = false := by
  apply List.getD_eq_default
  rw [wires_length]; exact hi

theorem wires_gate (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N)
    (hback : ReadsBack N C) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (N + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  obtain ⟨value, pre, len⟩ := foldl_snoc_split readGate C.gates x j hj false
  have hval : (C.wires x).getD (N + j) false = readGate ((C.gates.take j).foldl (fun R g => R ++ [readGate R g]) x) C.gates[j] := by
    rw [← hx]; exact value
  rw [hval]
  unfold readGate
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt : i < N + j := by
    have hb := hback j hj i
    rw [gateAt, List.getD_eq_getElem _ _ hj] at hb
    exact hb hi
  have hpre_len : (List.foldl (fun R g => R ++ [readGate R g]) x (List.take j C.gates)).length = N + j := by
    rw [len, hx]
  exact (getD_of_initial pre (by omega) false).symm

theorem wires_snoc (gs : List Gate) (g : Gate) (y : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires y =
      (Circuit.mk gs 0).wires y ++ [readGate ((Circuit.mk gs 0).wires y) g] := by
  simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil, readGate]

theorem wires_snoc_getD_lt (gs : List Gate) (g : Gate) (y : List Bool) (i : ℕ)
    (hi : i < y.length + gs.length) :
    ((Circuit.mk (gs ++ [g]) 0).wires y).getD i false = ((Circuit.mk gs 0).wires y).getD i false := by
  rw [wires_snoc]
  have hlen : ((Circuit.mk gs 0).wires y).length = y.length + gs.length := wires_length _ _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < ((Circuit.mk gs 0).wires y).length)]

theorem wires_snoc_getD_eq (gs : List Gate) (g : Gate) (y : List Bool) :
    ((Circuit.mk (gs ++ [g]) 0).wires y).getD (y.length + gs.length) false =
      readGate ((Circuit.mk gs 0).wires y) g := by
  rw [wires_snoc]
  have hlen : ((Circuit.mk gs 0).wires y).length = y.length + gs.length := wires_length _ _
  rw [← hlen]
  simp [List.getD_eq_getElem?_getD]

def dropAt (u : ℕ) (x : List Bool) : List Bool :=
  x.take u ++ x.drop (u + 1)

theorem dropAt_length {u N : ℕ} {x : List Bool} (hx : x.length = N) (hu : u < N) :
    (dropAt u x).length = N - 1 := by
  unfold dropAt
  simp [List.length_take, List.length_drop, hx]
  omega

theorem dropAt_getD_lt {u : ℕ} {x : List Bool} {i : ℕ} (hi : i < u) :
    (dropAt u x).getD i false = x.getD i false := by
  unfold dropAt
  by_cases hix : i < x.length
  · have hlt : i < (x.take u).length := by simp; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, hi]
  · have hge : (x.take u ++ x.drop (u + 1)).length ≤ i := by
      simp [List.length_take, List.length_drop]; omega
    rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]

theorem dropAt_getD_ge {u : ℕ} {x : List Bool} {i : ℕ} (hu : u < x.length) (hi : u ≤ i) :
    (dropAt u x).getD i false = x.getD (i + 1) false := by
  unfold dropAt
  have htl : (x.take u).length = u := by simp; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : (x.take u).length ≤ i),
    htl, List.getElem?_drop]
  congr 2; omega

theorem dropAt_oneEach {n m : ℕ} (u : Fin (n + 1)) (a : Fin n) (c : Fin m) :
    dropAt u.val (oneEach (u.succAbove a) c) = oneEach a c := by
  have hl1 : (oneEach (u.succAbove a) c).length = n + 1 + m := by simp [oneEach]; omega
  have hl2 : (oneEach a c).length = n + m := by simp [oneEach]
  have hld : (dropAt u.val (oneEach (u.succAbove a) c)).length = n + m := by
    rw [dropAt_length hl1 (by omega)]; omega
  apply List.ext_getElem (by omega)
  intro i hi1 hi2
  have hg : ∀ (L : List Bool) (h : i < L.length), L[i] = L.getD i false := fun L h =>
    (List.getD_eq_getElem L false h).symm
  rw [hg _ hi1, hg _ hi2]
  have hoe : ∀ {p q : ℕ} (r : Fin p) (s : Fin q) (k : ℕ),
      (oneEach r s).getD k false = decide (k = r.val ∨ k = p + s.val) := by
    intro p q r s k
    unfold oneEach
    rw [List.getD_eq_getElem?_getD]
    by_cases h : k < p
    · rw [List.getElem?_append_left (by simpa using h)]
      simp only [List.getElem?_ofFn, h, ↓reduceDIte, Option.getD_some, Fin.ext_iff]
      simp [show k ≠ p + s.val by omega]
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_ofFn, List.getElem?_ofFn]
      by_cases h2 : k - p < q
      · simp only [h2, ↓reduceDIte, Option.getD_some, Fin.ext_iff]
        have hr : k ≠ r.val := by omega
        by_cases hs : k = p + s.val
        · simp [hs]
        · have hs' : k - p ≠ s.val := by omega
          simp [hr, hs, hs']
      · simp only [h2, ↓reduceDIte, Option.getD_none]
        have hr : k ≠ r.val := by omega
        have hs : k ≠ p + s.val := by omega
        simp [hr, hs]
  have hsa : (u.succAbove a).val = if a.val < u.val then a.val else a.val + 1 := by
    unfold Fin.succAbove
    by_cases h : a.castSucc < u
    · have h' : a.val < u.val := h
      simp [h, h']
    · have h' : ¬ a.val < u.val := h
      simp [h, h']
  by_cases hiu : i < u.val
  · rw [dropAt_getD_lt hiu, hoe, hoe, hsa]
    simp only [decide_eq_decide]
    split_ifs <;> omega
  · rw [dropAt_getD_ge (by omega) (by omega), hoe, hoe, hsa]
    simp only [decide_eq_decide]
    split_ifs <;> omega

inductive WireRef where
  | const (b : Bool)
  | wire (w : ℕ)
  deriving DecidableEq

def evalRef (ws : List Bool) : WireRef → Bool
  | .const b => b
  | .wire w => ws.getD w false

def shiftInit (N : ℕ) (u : ℕ) (w : ℕ) : WireRef :=
  if w < u then .wire w
  else if w = u then .const false
  else if w < N then .wire (w - 1)
  else .const false

def foldStep (M : ℕ) (st : List Gate × List WireRef) (g : Gate) : List Gate × List WireRef :=
  let gs := st.1
  let env := st.2
  let getR (w : ℕ) : WireRef := env.getD w (.const false)
  let nextW : ℕ := M + gs.length
  match g.op with
  | .not =>
    match g.inputs.head? with
    | none => (gs, env ++ [.const true])
    | some w =>
      match getR w with
      | .const b => (gs, env ++ [.const (!b)])
      | .wire w' => (gs ++ [⟨.not, [w']⟩], env ++ [.wire nextW])
  | .and =>
    match g.inputs with
    | [] => (gs, env ++ [.const true])
    | [w] => (gs, env ++ [getR w])
    | [w1, w2] =>
      match getR w1, getR w2 with
      | .const false, _ => (gs, env ++ [.const false])
      | _, .const false => (gs, env ++ [.const false])
      | .const true, r2 => (gs, env ++ [r2])
      | r1, .const true => (gs, env ++ [r1])
      | .wire a, .wire b =>
        if a = b then (gs, env ++ [.wire a])
        else (gs ++ [⟨.and, [a, b]⟩], env ++ [.wire nextW])
    | _ => (gs, env ++ [.const false])
  | .or =>
    match g.inputs with
    | [] => (gs, env ++ [.const false])
    | [w] => (gs, env ++ [getR w])
    | [w1, w2] =>
      match getR w1, getR w2 with
      | .const true, _ => (gs, env ++ [.const true])
      | _, .const true => (gs, env ++ [.const true])
      | .const false, r2 => (gs, env ++ [r2])
      | r1, .const false => (gs, env ++ [r1])
      | .wire a, .wire b =>
        if a = b then (gs, env ++ [.wire a])
        else (gs ++ [⟨.or, [a, b]⟩], env ++ [.wire nextW])
    | _ => (gs, env ++ [.const false])
  | _ => (gs, env ++ [.const false])

def FoldInv (N M u : ℕ) (C : Circuit) (j : ℕ) (st : List Gate × List WireRef) : Prop :=
  st.2.length = N + j ∧
  st.2.getD u (.const false) = .const false ∧
  (∀ r ∈ st.2, ∀ w, r = .wire w → w < M + st.1.length) ∧
  FanInTwo ⟨st.1, 0⟩ ∧
  (Monotone2 C → Monotone2 ⟨st.1, 0⟩) ∧
  ReadsBack M ⟨st.1, 0⟩ ∧
  (∀ g ∈ st.1, NormGate g) ∧
  (∀ x : List Bool, x.length = N → x.getD u false = false →
    ∀ w < N + j, evalRef ((Circuit.mk st.1 0).wires (dropAt u x)) (st.2.getD w (.const false)) =
      (C.wires x).getD w false)

theorem foldStep_preserves {N M u : ℕ} (hNM : N = M + 1) (hu : u < N)
    (C : Circuit) (hfan : FanInTwo C) (hback : ReadsBack N C)
    (j : ℕ) (hj : j < C.gates.length) (st : List Gate × List WireRef)
    (hinv : FoldInv N M u C j st) :
    let g := C.gates[j]
    let st' := foldStep M st g
    FoldInv N M u C (j + 1) st' ∧
    st'.1.length ≤ st.1.length + 1 ∧
    (∀ w < N + j, st'.2.getD w (.const false) = st.2.getD w (.const false)) ∧
    ((∃ w, reads g w ∧ ∃ b, st.2.getD w (.const false) = .const b) → st'.1.length = st.1.length) ∧
    (reads g u → g.op = .and → st'.2.getD (N + j) (.const false) = .const false) ∧
    (reads g u → g.op = .not → st'.2.getD (N + j) (.const false) = .const true) := by
  rcases st with ⟨gs, env⟩
  dsimp only [FoldInv] at hinv
  obtain ⟨hlen, hu0, hbd, hfan', hmono', hback', hnorm', heval⟩ := hinv
  have hgmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have hgf := hfan C.gates[j] hgmem
  have hg_op := hgf.1
  have hg_len := hgf.2
  have hget_lt : ∀ w ∈ C.gates[j].inputs, w < N + j := by
    intro w hw
    have hb := hback j hj w
    rw [gateAt, List.getD_eq_getElem _ _ hj] at hb
    exact hb hw
  have hbd_getD : ∀ w < N + j, ∀ a, env.getD w (.const false) = .wire a → a < M + gs.length := by
    intro w hw a ha
    have hmem : env.getD w (.const false) ∈ env := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem (by omega)
    exact hbd _ hmem a ha
  have hkeep_env : ∀ (r : WireRef) (w : ℕ), w < N + j → (env ++ [r]).getD w (.const false) = env.getD w (.const false) := by
    intro r w hw
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : w < env.length)]
  have hlast_env : ∀ (r : WireRef), (env ++ [r]).getD (N + j) (.const false) = r := by
    intro r
    rw [← hlen]
    simp [List.getD_eq_getElem?_getD]
  have hno_emit : ∀ (r : WireRef),
      (∀ a, r = .wire a → a < M + gs.length) →
      (∀ x : List Bool, x.length = N → x.getD u false = false →
        evalRef ((Circuit.mk gs 0).wires (dropAt u x)) r = (C.wires x).getD (N + j) false) →
      FoldInv N M u C (j + 1) (gs, env ++ [r]) := by
    intro r hr_bd hr_ev
    refine ⟨by simp [hlen]; omega, by rw [hkeep_env r u (by omega)]; exact hu0, ?_, hfan', hmono', hback', hnorm', ?_⟩
    · intro r' hr' w hw
      rcases List.mem_append.mp hr' with h1 | h2
      · exact hbd r' h1 w hw
      · rw [List.mem_singleton.mp h2] at hw; exact hr_bd w hw
    · intro x hx hxu w hw
      by_cases hlt : w < N + j
      · rw [hkeep_env r w hlt]; exact heval x hx hxu w hlt
      · have heq : w = N + j := by omega
        subst heq
        rw [hlast_env r]
        exact hr_ev x hx hxu
  have hemit : ∀ (g' : Gate),
      g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
      g'.inputs.length ≤ 2 →
      (Monotone2 C → g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
      (∀ a ∈ g'.inputs, a < M + gs.length) →
      NormGate g' →
      (∀ x : List Bool, x.length = N → x.getD u false = false →
        readGate ((Circuit.mk gs 0).wires (dropAt u x)) g' = (C.wires x).getD (N + j) false) →
      FoldInv N M u C (j + 1) (gs ++ [g'], env ++ [.wire (M + gs.length)]) := by
    intro g' hg'op hg'len hg'mono hg'rb hg'norm hg'ev
    refine ⟨by simp [hlen]; omega, by rw [hkeep_env _ u (by omega)]; exact hu0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r' hr' w hw
      rcases List.mem_append.mp hr' with h1 | h2
      · have := hbd r' h1 w hw; simp; omega
      · rw [List.mem_singleton.mp h2] at hw; injection hw with hw'; simp; omega
    · intro g1 hg1
      rcases List.mem_append.mp hg1 with h1 | h2
      · exact hfan' g1 h1
      · rw [List.mem_singleton.mp h2]; exact ⟨hg'op, hg'len⟩
    · intro hMC g1 hg1
      rcases List.mem_append.mp hg1 with h1 | h2
      · exact hmono' hMC g1 h1
      · rw [List.mem_singleton.mp h2]; exact ⟨hg'mono hMC, hg'len⟩
    · intro k hk a ha
      change k < (gs ++ [g']).length at hk
      change a ∈ ((gs ++ [g']).getD k ⟨GateOp.or, []⟩).inputs at ha
      by_cases hk' : k < gs.length
      · rw [List.getD_append _ _ _ _ hk'] at ha
        exact hback' k hk' a ha
      · have heq : k = gs.length := by simp at hk; omega
        subst heq
        rw [List.getD_append_right _ _ _ _ le_rfl] at ha
        simp only [Nat.sub_self, List.getD_cons_zero] at ha
        exact hg'rb a ha
    · intro g1 hg1
      rcases List.mem_append.mp hg1 with h1 | h2
      · exact hnorm' g1 h1
      · rw [List.mem_singleton.mp h2]; exact hg'norm
    · intro x hx hxu w hw
      have hdx : (dropAt u x).length = M := by rw [dropAt_length hx hu]; omega
      by_cases hlt : w < N + j
      · rw [hkeep_env _ w hlt]
        have h1 := heval x hx hxu w hlt
        cases hr : env.getD w (.const false) with
        | const b => rw [hr] at h1; exact h1
        | wire a =>
          have ha : a < M + gs.length := hbd_getD w hlt a hr
          rw [hr] at h1
          simp only [evalRef] at h1 ⊢
          rw [wires_snoc_getD_lt gs g' (dropAt u x) a (by omega)]
          exact h1
      · have heq : w = N + j := by omega
        subst heq
        rw [hlast_env]
        simp only [evalRef]
        rw [← hdx, wires_snoc_getD_eq gs g' (dropAt u x)]
        exact hg'ev x hx hxu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg_op
  rcases hg_op with hop | hop | hop
  · have hcases : C.gates[j].inputs = [] ∨ (∃ w, C.gates[j].inputs = [w]) ∨ (∃ w1 w2, C.gates[j].inputs = [w1, w2]) := by
      rcases hin0 : C.gates[j].inputs with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, t⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨w1, rfl⟩)
      · exact Or.inr (Or.inr ⟨w1, w2, rfl⟩)
      · rw [hin0] at hg_len; simp at hg_len
    rcases hcases with hin | ⟨w, hin⟩ | ⟨w1, w2, hin⟩
    · simp only [foldStep, hop, hin]
      refine ⟨hno_emit (.const true) (by simp) (fun x hx _ => by
        rw [wires_gate N C x hx hback j hj, hop, hin]; rfl),
        by omega, fun w hw => hkeep_env _ w hw, fun _ => by simp,
        fun hr => by simp [reads, hop, hin] at hr, fun _ h => by simp [hop] at h⟩
    · have hwlt : w < N + j := hget_lt w (by simp [hin])
      simp only [foldStep, hop, hin]
      refine ⟨hno_emit (env.getD w (.const false)) (hbd_getD w hwlt) (fun x hx hxu => by
        rw [wires_gate N C x hx hback j hj, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.and_true, Bool.or_false]; exact heval x hx hxu w hwlt),
        by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
        fun hr _ => by
          have hwu : u = w := by simpa [reads, hop, hin] using hr
          subst hwu; rw [hlast_env, hu0],
        fun _ h => by simp [hop] at h⟩
    · have hw1lt : w1 < N + j := hget_lt w1 (by simp [hin])
      have hw2lt : w2 < N + j := hget_lt w2 (by simp [hin])
      cases hr1 : env.getD w1 (.const false) with
      | const b1 =>
        cases b1 with
        | false =>
          simp only [foldStep, hop, hin, hr1]
          refine ⟨hno_emit (.const false) (by simp) (fun x hx hxu => by
            rw [wires_gate N C x hx hback j hj, hop, hin]
            have h1 := heval x hx hxu w1 hw1lt; rw [hr1] at h1
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.head?_cons, Option.getD_some]; rw [← h1]; simp [evalRef]),
            by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
            fun _ _ => hlast_env _, fun _ h => by simp [hop] at h⟩
        | true =>
          cases hr2 : env.getD w2 (.const false) with
          | const b2 =>
            cases b2 with
            | false =>
              simp only [foldStep, hop, hin, hr1, hr2]
              refine ⟨hno_emit (.const false) (by simp) (fun x hx hxu => by
                rw [wires_gate N C x hx hback j hj, hop, hin]
                have h2 := heval x hx hxu w2 hw2lt; rw [hr2] at h2
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil]; rw [← h2]; simp [evalRef]),
                by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
                fun _ _ => hlast_env _, fun _ h => by simp [hop] at h⟩
            | true =>
              simp only [foldStep, hop, hin, hr1, hr2]
              refine ⟨hno_emit (.const true) (by simp) (fun x hx hxu => by
                rw [wires_gate N C x hx hback j hj, hop, hin]
                have h1 := heval x hx hxu w1 hw1lt; rw [hr1] at h1
                have h2 := heval x hx hxu w2 hw2lt; rw [hr2] at h2
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil]; rw [← h1, ← h2]; simp [evalRef]),
                by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
                fun hr _ => by
                  have hwu : u = w1 ∨ u = w2 := by simpa [reads, hop, hin] using hr
                  rcases hwu with rfl | rfl <;> (first | (rw [hu0] at hr1; cases hr1) | (rw [hu0] at hr2; cases hr2)),
                fun _ h => by simp [hop] at h⟩
          | wire b =>
            simp only [foldStep, hop, hin, hr1, hr2]
            refine ⟨hno_emit (.wire b) (fun a ha => by injection ha with h'; subst h'; exact hbd_getD w2 hw2lt b hr2)
              (fun x hx hxu => by
                rw [wires_gate N C x hx hback j hj, hop, hin]
                have h1 := heval x hx hxu w1 hw1lt; rw [hr1] at h1
                have h2 := heval x hx hxu w2 hw2lt; rw [hr2] at h2
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil]; rw [← h1, ← h2]; simp [evalRef]),
              by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
              fun hr _ => by
                have hwu : u = w1 ∨ u = w2 := by simpa [reads, hop, hin] using hr
                rcases hwu with rfl | rfl <;> (first | (rw [hu0] at hr1; cases hr1) | (rw [hu0] at hr2; cases hr2)),
              fun _ h => by simp [hop] at h⟩
      | wire a =>
        cases hr2 : env.getD w2 (.const false) with
        | const b2 =>
          cases b2 with
          | false =>
            simp only [foldStep, hop, hin, hr1, hr2]
            refine ⟨hno_emit (.const false) (by simp) (fun x hx hxu => by
              rw [wires_gate N C x hx hback j hj, hop, hin]
              have h2 := heval x hx hxu w2 hw2lt; rw [hr2] at h2
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil]; rw [← h2]; simp [evalRef]),
              by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
              fun _ _ => hlast_env _, fun _ h => by simp [hop] at h⟩
          | true =>
            simp only [foldStep, hop, hin, hr1, hr2]
            refine ⟨hno_emit (.wire a) (fun a' ha' => by injection ha' with h'; subst h'; exact hbd_getD w1 hw1lt a hr1)
              (fun x hx hxu => by
                rw [wires_gate N C x hx hback j hj, hop, hin]
                have h1 := heval x hx hxu w1 hw1lt; rw [hr1] at h1
                have h2 := heval x hx hxu w2 hw2lt; rw [hr2] at h2
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil]; rw [← h1, ← h2]; simp [evalRef]),
              by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
              fun hr _ => by
                have hwu : u = w1 ∨ u = w2 := by simpa [reads, hop, hin] using hr
                rcases hwu with rfl | rfl <;> (first | (rw [hu0] at hr1; cases hr1) | (rw [hu0] at hr2; cases hr2)),
              fun _ h => by simp [hop] at h⟩
        | wire b =>
          by_cases hab : a = b
          · subst hab
            simp only [foldStep, hop, hin, hr1, hr2, ↓reduceIte]
            refine ⟨hno_emit (.wire a) (fun a' ha' => by injection ha' with h'; subst h'; exact hbd_getD w1 hw1lt a hr1)
              (fun x hx hxu => by
                rw [wires_gate N C x hx hback j hj, hop, hin]
                have h1 := heval x hx hxu w1 hw1lt; rw [hr1] at h1
                have h2 := heval x hx hxu w2 hw2lt; rw [hr2] at h2
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil]; rw [← h1, ← h2]; simp [evalRef]),
              by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
              fun hr _ => by
                have hwu : u = w1 ∨ u = w2 := by simpa [reads, hop, hin] using hr
                rcases hwu with rfl | rfl <;> (first | (rw [hu0] at hr1; cases hr1) | (rw [hu0] at hr2; cases hr2)),
              fun _ h => by simp [hop] at h⟩
          · simp only [foldStep, hop, hin, hr1, hr2, hab, ↓reduceIte]
            refine ⟨hemit ⟨.and, [a, b]⟩ (by simp) (by simp) (fun _ => by simp)
              (fun z hz => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                rcases hz with hz | hz
                · rw [hz]; exact hbd_getD w1 hw1lt a hr1
                · rw [hz]; exact hbd_getD w2 hw2lt b hr2)
              ⟨by simp, fun _ => ⟨by simp, by simp [hab]⟩⟩
              (fun x hx hxu => by
                rw [wires_gate N C x hx hback j hj, hop, hin]
                have h1 := heval x hx hxu w1 hw1lt; rw [hr1] at h1
                have h2 := heval x hx hxu w2 hw2lt; rw [hr2] at h2
                simp only [readGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil]; rw [← h1, ← h2]; simp [evalRef]),
              by simp, fun w' hw' => hkeep_env _ w' hw',
              fun ⟨w, hrw, b', hb'⟩ => by
                have hmem : w = w1 ∨ w = w2 := by simpa [reads, hop, hin] using hrw
                rcases hmem with rfl | rfl <;> (first | (rw [hb'] at hr1; cases hr1) | (rw [hb'] at hr2; cases hr2)),
              fun hr _ => by
                have hwu : u = w1 ∨ u = w2 := by simpa [reads, hop, hin] using hr
                rcases hwu with rfl | rfl <;> (first | (rw [hu0] at hr1; cases hr1) | (rw [hu0] at hr2; cases hr2)),
              fun _ h => by simp [hop] at h⟩
  · have hcases : C.gates[j].inputs = [] ∨ (∃ w, C.gates[j].inputs = [w]) ∨ (∃ w1 w2, C.gates[j].inputs = [w1, w2]) := by
      rcases hin0 : C.gates[j].inputs with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, t⟩⟩⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨w1, rfl⟩)
      · exact Or.inr (Or.inr ⟨w1, w2, rfl⟩)
      · rw [hin0] at hg_len; simp at hg_len
    rcases hcases with hin | ⟨w, hin⟩ | ⟨w1, w2, hin⟩
    · simp only [foldStep, hop, hin]
      refine ⟨hno_emit (.const false) (by simp) (fun x hx _ => by
        rw [wires_gate N C x hx hback j hj, hop, hin]; rfl),
        by omega, fun w hw => hkeep_env _ w hw, fun _ => by simp,
        fun _ h => by simp [hop] at h, fun _ h => by simp [hop] at h⟩
    · have hwlt : w < N + j := hget_lt w (by simp [hin])
      simp only [foldStep, hop, hin]
      refine ⟨hno_emit (env.getD w (.const false)) (hbd_getD w hwlt) (fun x hx hxu => by
        rw [wires_gate N C x hx hback j hj, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.and_true, Bool.or_false]; exact heval x hx hxu w hwlt),
        by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
        fun _ h => by simp [hop] at h, fun _ h => by simp [hop] at h⟩
    · have hw1lt : w1 < N + j := hget_lt w1 (by simp [hin])
      have hw2lt : w2 < N + j := hget_lt w2 (by simp [hin])
      cases hr1 : env.getD w1 (.const false) with
      | const b1 =>
        cases b1 with
        | true =>
          simp only [foldStep, hop, hin, hr1]
          refine ⟨hno_emit (.const true) (by simp) (fun x hx hxu => by
            rw [wires_gate N C x hx hback j hj, hop, hin]
            have h1 := heval x hx hxu w1 hw1lt; rw [hr1] at h1
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.head?_cons, Option.getD_some]; rw [← h1]; simp [evalRef]),
            by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
            fun _ h => by simp [hop] at h, fun _ h => by simp [hop] at h⟩
        | false =>
          cases hr2 : env.getD w2 (.const false) with
          | const b2 =>
            cases b2 with
            | true =>
              simp only [foldStep, hop, hin, hr1, hr2]
              refine ⟨hno_emit (.const true) (by simp) (fun x hx hxu => by
                rw [wires_gate N C x hx hback j hj, hop, hin]
                have h2 := heval x hx hxu w2 hw2lt; rw [hr2] at h2
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil]; rw [← h2]; simp [evalRef]),
                by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
                fun _ h => by simp [hop] at h, fun _ h => by simp [hop] at h⟩
            | false =>
              simp only [foldStep, hop, hin, hr1, hr2]
              refine ⟨hno_emit (.const false) (by simp) (fun x hx hxu => by
                rw [wires_gate N C x hx hback j hj, hop, hin]
                have h1 := heval x hx hxu w1 hw1lt; rw [hr1] at h1
                have h2 := heval x hx hxu w2 hw2lt; rw [hr2] at h2
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil]; rw [← h1, ← h2]; simp [evalRef]),
                by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
                fun _ h => by simp [hop] at h, fun _ h => by simp [hop] at h⟩
          | wire b =>
            simp only [foldStep, hop, hin, hr1, hr2]
            refine ⟨hno_emit (.wire b) (fun a ha => by injection ha with h'; subst h'; exact hbd_getD w2 hw2lt b hr2)
              (fun x hx hxu => by
                rw [wires_gate N C x hx hback j hj, hop, hin]
                have h1 := heval x hx hxu w1 hw1lt; rw [hr1] at h1
                have h2 := heval x hx hxu w2 hw2lt; rw [hr2] at h2
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil]; rw [← h1, ← h2]; simp [evalRef]),
              by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
              fun _ h => by simp [hop] at h, fun _ h => by simp [hop] at h⟩
      | wire a =>
        cases hr2 : env.getD w2 (.const false) with
        | const b2 =>
          cases b2 with
          | true =>
            simp only [foldStep, hop, hin, hr1, hr2]
            refine ⟨hno_emit (.const true) (by simp) (fun x hx hxu => by
              rw [wires_gate N C x hx hback j hj, hop, hin]
              have h2 := heval x hx hxu w2 hw2lt; rw [hr2] at h2
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil]; rw [← h2]; simp [evalRef]),
              by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
              fun _ h => by simp [hop] at h, fun _ h => by simp [hop] at h⟩
          | false =>
            simp only [foldStep, hop, hin, hr1, hr2]
            refine ⟨hno_emit (.wire a) (fun a' ha' => by injection ha' with h'; subst h'; exact hbd_getD w1 hw1lt a hr1)
              (fun x hx hxu => by
                rw [wires_gate N C x hx hback j hj, hop, hin]
                have h1 := heval x hx hxu w1 hw1lt; rw [hr1] at h1
                have h2 := heval x hx hxu w2 hw2lt; rw [hr2] at h2
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil]; rw [← h1, ← h2]; simp [evalRef]),
              by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
              fun _ h => by simp [hop] at h, fun _ h => by simp [hop] at h⟩
        | wire b =>
          by_cases hab : a = b
          · subst hab
            simp only [foldStep, hop, hin, hr1, hr2, ↓reduceIte]
            refine ⟨hno_emit (.wire a) (fun a' ha' => by injection ha' with h'; subst h'; exact hbd_getD w1 hw1lt a hr1)
              (fun x hx hxu => by
                rw [wires_gate N C x hx hback j hj, hop, hin]
                have h1 := heval x hx hxu w1 hw1lt; rw [hr1] at h1
                have h2 := heval x hx hxu w2 hw2lt; rw [hr2] at h2
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil]; rw [← h1, ← h2]; simp [evalRef]),
              by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
              fun _ h => by simp [hop] at h, fun _ h => by simp [hop] at h⟩
          · simp only [foldStep, hop, hin, hr1, hr2, hab, ↓reduceIte]
            refine ⟨hemit ⟨.or, [a, b]⟩ (by simp) (by simp) (fun _ => by simp)
              (fun z hz => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                rcases hz with hz | hz
                · rw [hz]; exact hbd_getD w1 hw1lt a hr1
                · rw [hz]; exact hbd_getD w2 hw2lt b hr2)
              ⟨by simp, fun _ => ⟨by simp, by simp [hab]⟩⟩
              (fun x hx hxu => by
                rw [wires_gate N C x hx hback j hj, hop, hin]
                have h1 := heval x hx hxu w1 hw1lt; rw [hr1] at h1
                have h2 := heval x hx hxu w2 hw2lt; rw [hr2] at h2
                simp only [readGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil]; rw [← h1, ← h2]; simp [evalRef]),
              by simp, fun w' hw' => hkeep_env _ w' hw',
              fun ⟨w, hrw, b', hb'⟩ => by
                have hmem : w = w1 ∨ w = w2 := by simpa [reads, hop, hin] using hrw
                rcases hmem with rfl | rfl <;> (first | (rw [hb'] at hr1; cases hr1) | (rw [hb'] at hr2; cases hr2)),
              fun _ h => by simp [hop] at h, fun _ h => by simp [hop] at h⟩
  · cases hhd : C.gates[j].inputs.head? with
    | none =>
      have hin : C.gates[j].inputs = [] := List.head?_eq_none_iff.mp hhd
      simp only [foldStep, hop, hhd]
      refine ⟨hno_emit (.const true) (by simp) (fun x hx _ => by
        rw [wires_gate N C x hx hback j hj, hop, hin]; rfl),
        by omega, fun w hw => hkeep_env _ w hw, fun _ => by simp,
        fun _ h => by simp [hop] at h, fun _ _ => hlast_env _⟩
    | some w =>
      have hwmem : w ∈ C.gates[j].inputs := List.mem_of_head? hhd
      have hwlt : w < N + j := hget_lt w hwmem
      obtain ⟨tl, hcons⟩ : ∃ tl, C.gates[j].inputs = w :: tl := List.head?_eq_some_iff.mp hhd
      cases hr : env.getD w (.const false) with
      | const b =>
        simp only [foldStep, hop, hhd, hr]
        refine ⟨hno_emit (.const (!b)) (by simp) (fun x hx hxu => by
          rw [wires_gate N C x hx hback j hj, hop, hcons]
          have h1 := heval x hx hxu w hwlt; rw [hr] at h1
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.head?_cons, Option.getD_some]; rw [← h1]; simp [evalRef]),
          by omega, fun w' hw' => hkeep_env _ w' hw', fun _ => by simp,
          fun _ h => by simp [hop] at h,
          fun hru _ => by
            have hwu : w = u := by
              simp only [reads, hop, hhd, true_and, ne_eq, not_true_eq_false, false_and, or_false] at hru
              exact Option.some.inj hru
            subst hwu
            rw [hu0] at hr; injection hr with hb; subst hb; exact hlast_env _⟩
      | wire a =>
        simp only [foldStep, hop, hhd, hr]
        refine ⟨hemit ⟨.not, [a]⟩ (by simp) (by simp)
          (fun hMC => by
            have hm := (hMC _ hgmem).1
            simp [hop] at hm)
          (fun z hz => by rw [List.mem_singleton.mp hz]; exact hbd_getD w hwlt a hr)
          ⟨fun _ => by simp, fun h => absurd rfl h⟩
          (fun x hx hxu => by
            rw [wires_gate N C x hx hback j hj, hop, hcons]
            have h1 := heval x hx hxu w hwlt; rw [hr] at h1
            simp only [readGate, GateOp.eval, List.map_cons, List.map_nil, List.head?_cons, Option.getD_some]; rw [← h1]; simp [evalRef]),
          by simp, fun w' hw' => hkeep_env _ w' hw',
          (fun ⟨w', hrw', b', hb'⟩ => by
            have hw'eq : w = w' := by
              simp only [reads, hop, hhd, true_and, ne_eq, not_true_eq_false, false_and, or_false] at hrw'
              exact Option.some.inj hrw'
            subst hw'eq; rw [hb'] at hr; exact nomatch hr),
          (fun _ h => by simp at h),
          (fun hru _ => by
            have hwu : w = u := by
              simp only [reads, hop, hhd, true_and, ne_eq, not_true_eq_false, false_and, or_false] at hru
              exact Option.some.inj hru
            subst hwu; rw [hu0] at hr; exact nomatch hr)⟩

def foldPrefix (N M u : ℕ) (C : Circuit) : ℕ → List Gate × List WireRef
  | 0 => ([], (List.range N).map (shiftInit N u))
  | j + 1 => foldStep M (foldPrefix N M u C j) (C.gates.getD j ⟨.or, []⟩)

theorem foldPrefix_inv {N M u : ℕ} (hNM : N = M + 1) (hu : u < N)
    (C : Circuit) (hfan : FanInTwo C) (hback : ReadsBack N C)
    (K : Finset (Fin C.gates.length))
    (hK : ∀ j ∈ K, reads (C.gates.get j) u ∨
      ∃ i : Fin C.gates.length, i < j ∧ reads (C.gates.get i) u ∧
        ((C.gates.get i).op = GateOp.and ∨ (C.gates.get i).op = GateOp.not) ∧
        reads (C.gates.get j) (N + i.val)) :
    ∀ k ≤ C.gates.length,
      FoldInv N M u C k (foldPrefix N M u C k) ∧
      (foldPrefix N M u C k).1.length + (K.filter (fun j => j.val < k)).card ≤ k ∧
      (∀ i : Fin C.gates.length, i.val < k → reads (C.gates.get i) u →
        ((C.gates.get i).op = .and ∨ (C.gates.get i).op = .not) →
        ∃ b, (foldPrefix N M u C k).2.getD (N + i.val) (.const false) = .const b) := by
  intro k hk
  induction k with
  | zero =>
    refine ⟨?_, by simp [foldPrefix], fun i hi => by omega⟩
    refine ⟨by simp [foldPrefix], ?_, ?_, by simp [foldPrefix, FanInTwo], fun _ => by simp [foldPrefix, Monotone2],
      by simp [foldPrefix, ReadsBack], by simp [foldPrefix], ?_⟩
    · simp [foldPrefix, List.getD_eq_getElem?_getD, hu, shiftInit]
    · intro r hr w hw
      simp only [foldPrefix, List.mem_map, List.mem_range] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      unfold shiftInit at hw
      split_ifs at hw <;> (cases hw; omega)
    · intro x hx hxu w hw
      rw [wires_low C x w (by omega)]
      simp only [foldPrefix, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (by omega : w < N), Option.map_some, Option.getD_some,
        Circuit.wires, List.foldl_nil]
      unfold shiftInit
      split_ifs with h1 h2 h3
      · simp only [evalRef]; exact dropAt_getD_lt h1
      · subst h2; simp only [evalRef]; exact hxu.symm
      · simp only [evalRef]
        have hge := dropAt_getD_ge (u := u) (x := x) (i := w - 1) (by omega) (by omega)
        rw [Nat.sub_add_cancel (by omega)] at hge
        exact hge
      · omega
  | succ k ih =>
    obtain ⟨hinv, hcnt, hconst⟩ := ih (by omega)
    have hkl : k < C.gates.length := by omega
    have hget : C.gates.getD k ⟨.or, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hkl
    have hstep := foldStep_preserves hNM hu C hfan hback k hkl (foldPrefix N M u C k) hinv
    have hfp : foldPrefix N M u C (k + 1) = foldStep M (foldPrefix N M u C k) C.gates[k] := by
      simp only [foldPrefix, hget]
    rw [hfp]
    refine ⟨hstep.1, ?_, ?_⟩
    · let kFin : Fin C.gates.length := ⟨k, hkl⟩
      have hfilt : K.filter (fun j => j.val < k + 1) =
          if kFin ∈ K then insert kFin (K.filter (fun j => j.val < k))
          else K.filter (fun j => j.val < k) := by
        ext j
        by_cases hkm : kFin ∈ K <;> simp only [hkm, ↓reduceIte, Finset.mem_filter, Finset.mem_insert]
        · constructor
          · intro ⟨hjK, hjk⟩
            by_cases he : j = kFin
            · exact Or.inl he
            · exact Or.inr ⟨hjK, by have : j.val ≠ k := fun h => he (Fin.ext h); omega⟩
          · rintro (rfl | ⟨hjK, hjk⟩)
            · exact ⟨hkm, by simp [kFin]⟩
            · exact ⟨hjK, by omega⟩
        · constructor
          · intro ⟨hjK, hjk⟩
            refine ⟨hjK, ?_⟩
            have hne : j ≠ kFin := fun h => hkm (h ▸ hjK)
            have : j.val ≠ k := fun h => hne (Fin.ext h)
            omega
          · intro ⟨hjK, hjk⟩; exact ⟨hjK, by omega⟩
      rw [hfilt]
      split_ifs with hkm
      · have hnot : kFin ∉ K.filter (fun j => j.val < k) := by simp [kFin]
        rw [Finset.card_insert_of_notMem hnot]
        have hzero : (foldStep M (foldPrefix N M u C k) C.gates[k]).1.length = (foldPrefix N M u C k).1.length := by
          apply hstep.2.2.2.1
          rcases hK kFin hkm with hru | ⟨i, hik, hriu, hiop, hrji⟩
          · exact ⟨u, by simpa [kFin] using hru, false, hinv.2.1⟩
          · obtain ⟨b, hb⟩ := hconst i hik hriu hiop
            exact ⟨N + i.val, by simpa [kFin] using hrji, b, hb⟩
        omega
      · have hle := hstep.2.1
        omega
    · intro i hik hriu hiop
      by_cases hilt : i.val < k
      · rw [hstep.2.2.1 (N + i.val) (by omega)]
        exact hconst i hilt hriu hiop
      · have hieq : i.val = k := by omega
        have hi_get : C.gates.get i = C.gates[k] := by
          rw [List.get_eq_getElem]; congr 1
        rw [hi_get] at hriu hiop
        rw [hieq]
        rcases hiop with hand | hnot
        · exact ⟨false, hstep.2.2.2.2.1 hriu hand⟩
        · exact ⟨true, hstep.2.2.2.2.2 hriu hnot⟩

def shiftDel (p : ℕ) (w : ℕ) : ℕ :=
  if w < p then w else w - 1

def delGate (M : ℕ) (i₀ : ℕ) (C : Circuit) : Circuit :=
  let p := M + i₀
  let mapG (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftDel p)⟩
  ⟨(C.gates.take i₀ ++ C.gates.drop (i₀ + 1)).map mapG, shiftDel p C.output⟩

theorem delGate_size {M i₀ : ℕ} {C : Circuit} (hi₀ : i₀ < C.gates.length) :
    (delGate M i₀ C).size = C.size - 1 := by
  unfold delGate Circuit.size
  simp [List.length_take, List.length_drop]
  omega

theorem delGate_preserves {M : ℕ} (C : Circuit) (i₀ : Fin C.gates.length)
    (hfan : FanInTwo C) (hback : ReadsBack M C) (hnorm : ∀ g ∈ C.gates, NormGate g)
    (hout : M + i₀.val ≠ C.output)
    (hdead : ∀ j : Fin C.gates.length, i₀ < j → M + i₀.val ∉ (C.gates.get j).inputs) :
    let D := delGate M i₀.val C
    D.size + 1 = C.size ∧
    FanInTwo D ∧
    (Monotone2 C → Monotone2 D) ∧
    ReadsBack M D ∧
    (∀ g ∈ D.gates, NormGate g) ∧
    (∀ y : List Bool, y.length = M → D.eval y = C.eval y) := by
  let p := M + i₀.val
  let mapG (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftDel p)⟩
  let gs' := C.gates.take i₀.val ++ C.gates.drop (i₀.val + 1)
  have hlen_gs' : gs'.length = C.gates.length - 1 := by
    simp [gs', List.length_take, List.length_drop]; omega
  have hlenD : (delGate M i₀.val C).gates.length = C.gates.length - 1 := by
    change (gs'.map mapG).length = _; simp [hlen_gs']
  have hno_read : ∀ (j : ℕ) (hj : j < C.gates.length), p ∉ C.gates[j].inputs := by
    intro j hj hmem
    by_cases hlt : i₀.val < j
    · exact hdead ⟨j, hj⟩ hlt (by simpa [List.get_eq_getElem] using hmem)
    · have hb := hback j hj p
      rw [gateAt, List.getD_eq_getElem _ _ hj] at hb
      have := hb hmem
      omega
  have hgs'_get : ∀ (k : ℕ) (hk : k < gs'.length),
      gs'[k] = C.gates[if k < i₀.val then k else k + 1]'(by split_ifs <;> omega) := by
    intro k hk
    have htl : (C.gates.take i₀.val).length = i₀.val := by simp
    by_cases hki : k < i₀.val
    · simp only [gs', hki, ↓reduceIte]
      rw [List.getElem_append_left (by omega : k < (C.gates.take i₀.val).length), List.getElem_take]
    · simp only [gs', hki, ↓reduceIte]
      rw [List.getElem_append_right (by omega : (C.gates.take i₀.val).length ≤ k), List.getElem_drop]
      congr 1; omega
  have hgs'_mem : ∀ g ∈ gs', g ∈ C.gates := by
    intro g hg
    rcases List.mem_append.mp hg with h1 | h2
    · exact List.mem_of_mem_take h1
    · exact List.mem_of_mem_drop h2
  have hRB : ReadsBack M (delGate M i₀.val C) := by
    intro k hk w hw
    change k < (gs'.map mapG).length at hk
    have hk' : k < gs'.length := by simpa using hk
    have hgk : gateAt (delGate M i₀.val C) k = mapG gs'[k] := by
      unfold gateAt delGate
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk'), List.getElem_map]
    rw [hgk] at hw
    simp only [mapG, List.mem_map] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    rw [hgs'_get k hk'] at ha
    let idx := if k < i₀.val then k else k + 1
    have hidx : idx < C.gates.length := by dsimp [idx]; split_ifs <;> omega
    have hba := hback idx hidx a
    rw [gateAt, List.getD_eq_getElem _ _ hidx] at hba
    have halt : a < M + idx := hba ha
    have hne : a ≠ p := fun h => hno_read idx hidx (h ▸ ha)
    unfold shiftDel
    dsimp [idx] at halt
    split_ifs at halt ⊢ <;> omega
  have hNorm : ∀ g ∈ (delGate M i₀.val C).gates, NormGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have hg0C : g0 ∈ C.gates := hgs'_mem g0 hg0
    obtain ⟨j, hj, hgj⟩ := List.mem_iff_getElem.mp hg0C
    have hnr := hno_read j hj; rw [hgj] at hnr
    have hn0 := hnorm g0 hg0C
    refine ⟨fun hop => by simp [hn0.1 hop], fun hop => ⟨by simp [(hn0.2 hop).1], ?_⟩⟩
    apply List.Nodup.map_on _ (hn0.2 hop).2
    intro a ha b hb heq
    have hap : a ≠ p := fun h => hnr (h ▸ ha)
    have hbp : b ≠ p := fun h => hnr (h ▸ hb)
    unfold shiftDel at heq
    split_ifs at heq <;> omega
  refine ⟨by rw [delGate_size i₀.isLt]; have := i₀.isLt; unfold Circuit.size; omega, ?_, ?_, hRB, hNorm, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have hf := hfan g0 (hgs'_mem g0 hg0)
    exact ⟨hf.1, by simp [hf.2]⟩
  · intro hMC g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have hm := hMC g0 (hgs'_mem g0 hg0)
    exact ⟨hm.1, by simp [hm.2]⟩
  · intro y hy
    have hw_eq : ∀ w : ℕ, w ≠ p →
        ((delGate M i₀.val C).wires y).getD (shiftDel p w) false = (C.wires y).getD w false := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwp
        by_cases hlo : w < M
        · have hsd : shiftDel p w = w := by simp [shiftDel, show w < p by omega]
          rw [hsd, wires_low _ y w (by omega), wires_low _ y w (by omega)]
        by_cases hhi : M + C.gates.length ≤ w
        · have hsd : M + (delGate M i₀.val C).gates.length ≤ shiftDel p w := by
            rw [hlenD]; unfold shiftDel; split_ifs <;> omega
          rw [wires_past _ y _ (by omega), wires_past _ y _ (by omega)]
        let j := w - M
        have hj : j < C.gates.length := by omega
        have hwj : w = M + j := by omega
        have hji : j ≠ i₀.val := by omega
        let k := if j < i₀.val then j else j - 1
        have hk : k < gs'.length := by dsimp [k]; split_ifs <;> omega
        have hsd : shiftDel p w = M + k := by
          unfold shiftDel; dsimp [k]; split_ifs <;> omega
        rw [hsd, hwj]
        have hkD : k < (delGate M i₀.val C).gates.length := by rw [hlenD]; omega
        rw [wires_gate M (delGate M i₀.val C) y hy hRB k hkD]
        rw [wires_gate M C y hy hback j hj]
        have hgk : (delGate M i₀.val C).gates[k]'hkD = mapG C.gates[j] := by
          change (gs'.map mapG)[k]'(by rw [List.length_map]; exact hk) = mapG C.gates[j]
          rw [List.getElem_map, hgs'_get k hk]
          congr 2
          dsimp [k]; split_ifs <;> omega
        rw [hgk]
        simp only [mapG, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a ha
        have halt : a < M + j := by
          have hb := hback j hj a
          rw [gateAt, List.getD_eq_getElem _ _ hj] at hb
          exact hb ha
        have hap : a ≠ p := fun h => hno_read j hj (h ▸ ha)
        exact ih a (by omega) hap
    exact hw_eq C.output (Ne.symm hout)

theorem prune_dead {M : ℕ} : ∀ (sz : ℕ) (C : Circuit), C.size = sz →
    FanInTwo C → ReadsBack M C → (∀ g ∈ C.gates, NormGate g) →
    ∃ D : Circuit,
      D.size ≤ C.size ∧
      FanInTwo D ∧
      (Monotone2 C → Monotone2 D) ∧
      ReadsBack M D ∧
      (∀ g ∈ D.gates, NormGate g) ∧
      (∀ y : List Bool, y.length = M → D.eval y = C.eval y) ∧
      (∀ i : Fin D.gates.length, M + i.val ≠ D.output →
        ∃ j : Fin D.gates.length, i < j ∧ reads (D.gates.get j) (M + i.val)) := by
  intro sz
  induction sz using Nat.strong_induction_on with
  | ind sz ih =>
    intro C hsz hfan hback hnorm
    by_cases hlive : ∀ i : Fin C.gates.length, M + i.val ≠ C.output →
        ∃ j : Fin C.gates.length, i < j ∧ reads (C.gates.get j) (M + i.val)
    · exact ⟨C, le_rfl, hfan, id, hback, hnorm, fun _ _ => rfl, hlive⟩
    · push Not at hlive
      obtain ⟨i₀, hout, hdead⟩ := hlive
      have hdead' : ∀ j : Fin C.gates.length, i₀ < j → M + i₀.val ∉ (C.gates.get j).inputs := by
        intro j hij hmem
        have hn := hnorm (C.gates.get j) (List.get_mem _ _)
        exact hdead j hij ((reads_iff_mem hn _).mpr hmem)
      have hdel := delGate_preserves C i₀ hfan hback hnorm hout hdead'
      obtain ⟨hsz', hfan', hmono', hback', hnorm', hev'⟩ := hdel
      obtain ⟨D, hDsz, hDfan, hDmono, hDback, hDnorm, hDev, hDlive⟩ :=
        ih (delGate M i₀.val C).size (by omega) (delGate M i₀.val C) rfl hfan' hback' hnorm'
      exact ⟨D, by omega, hDfan, fun hMC => hDmono (hmono' hMC), hDback, hDnorm,
        fun y hy => (hDev y hy).trans (hev' y hy), hDlive⟩

theorem main_aux : ∀ (n m : ℕ) (A : Fin (n + 1) → Fin m → Bool) (u : Fin (n + 1))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (K : Finset (Fin C.gates.length)),
  let N := n + 1 + m
  let reads := fun (g : PEqualNP.CircuitLowerBounds.Gate) (w : ℕ) =>
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some w) ∨
    (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ w ∈ g.inputs)
  PEqualNP.MetaComplexity.FanInTwo C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack N C →
  PEqualNP.Represents.Represents A C →
  (∃ x : List Bool, x.length = N ∧ x.getD u.val false = false ∧ C.eval x = false) →
  (∀ j ∈ K, reads (C.gates.get j) u.val ∨
    ∃ i : Fin C.gates.length, i < j ∧ reads (C.gates.get i) u.val ∧
      ((C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      reads (C.gates.get j) (N + i.val)) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
    D.size + K.card ≤ C.size ∧
    PEqualNP.Represents.Represents (fun a c => A (u.succAbove a) c) D ∧
    PEqualNP.MetaComplexity.FanInTwo D ∧
    (PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.Monotone2 D) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) D ∧
    (∀ g ∈ D.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) ∧
      (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not →
        g.inputs.length = 2 ∧ g.inputs.Nodup)) ∧
    (∀ i : Fin D.gates.length, n + m + i.val ≠ D.output →
      ∃ j : Fin D.gates.length, i < j ∧ reads (D.gates.get j) (n + m + i.val)) := by
  intro n m A u C K N _ hfan hback hrep ⟨xf, hxf_len, hxf_u, hxf_eval⟩ hK
  let M := n + m
  have hNM : N = M + 1 := by dsimp [N, M]; omega
  have huN : u.val < N := by dsimp [N]; omega
  obtain ⟨hinv, hcnt, _⟩ := foldPrefix_inv hNM huN C hfan hback K hK C.gates.length le_rfl
  have hfilt_eq : K.filter (fun j => j.val < C.gates.length) = K := by
    ext j; simp
  rw [hfilt_eq] at hcnt
  set st := foldPrefix N M u.val C C.gates.length with hst
  obtain ⟨hlen, _, _, hfan1, hmono1, hback1, hnorm1, heval1⟩ := hinv
  have hout_eval : ∀ x : List Bool, x.length = N → x.getD u.val false = false →
      evalRef ((Circuit.mk st.1 0).wires (dropAt u.val x)) (st.2.getD C.output (.const false)) = C.eval x := by
    intro x hx hxu
    by_cases hlt : C.output < N + C.gates.length
    · exact heval1 x hx hxu C.output hlt
    · rw [List.getD_eq_default _ _ (by omega)]
      change false = (C.wires x).getD C.output false
      rw [wires_past C x C.output (by omega)]
  cases hout : st.2.getD C.output (.const false) with
  | const b =>
    cases b with
    | true =>
      exfalso
      have h1 := hout_eval xf hxf_len hxf_u
      rw [hout, hxf_eval] at h1
      exact Bool.false_ne_true h1.symm
    | false =>
      refine ⟨⟨[], M⟩, ?_, ?_, by simp [FanInTwo], fun _ => by simp [Monotone2],
        by simp [ReadsBack], by simp, fun i => i.elim0⟩
      · have hKle : K.card ≤ C.size := by
          have := Finset.card_le_univ K; rw [Fintype.card_fin] at this; exact this
        change 0 + K.card ≤ C.size; omega
      · intro a c
        have h1 := hout_eval (oneEach (u.succAbove a) c) (by simp [oneEach, N]; omega) (by
          unfold oneEach
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega), List.getElem?_ofFn]
          have hne : u ≠ u.succAbove a := (Fin.succAbove_ne u a).symm
          have hne' : (⟨u.val, u.isLt⟩ : Fin (n + 1)) ≠ u.succAbove a := hne
          simp [u.isLt, hne'])
        rw [hout, hrep (u.succAbove a) c] at h1
        change ((Circuit.mk [] M).wires (oneEach a c)).getD M false = A (u.succAbove a) c
        rw [wires_past _ _ M (by simp [oneEach, M])]
        exact h1
  | wire wout =>
    let C1 : Circuit := ⟨st.1, wout⟩
    have hC1_eval : ∀ y : List Bool, C1.eval y = ((Circuit.mk st.1 0).wires y).getD wout false :=
      fun _ => rfl
    obtain ⟨D, hDsz, hDfan, hDmono, hDback, hDnorm, hDev, hDlive⟩ :=
      prune_dead (M := M) C1.size C1 rfl hfan1 hback1 hnorm1
    have hC1_sz : C1.size = st.1.length := rfl
    refine ⟨D, by change D.size + K.card ≤ C.gates.length; omega, ?_,
      hDfan, fun hMC => hDmono (hmono1 hMC), hDback, hDnorm, hDlive⟩
    intro a c
    have h1 := hout_eval (oneEach (u.succAbove a) c) (by simp [oneEach, N]; omega) (by
      unfold oneEach
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega), List.getElem?_ofFn]
      have hne : u ≠ u.succAbove a := (Fin.succAbove_ne u a).symm
      have hne' : (⟨u.val, u.isLt⟩ : Fin (n + 1)) ≠ u.succAbove a := hne
      simp [u.isLt, hne'])
    rw [hout, dropAt_oneEach, hrep (u.succAbove a) c] at h1
    rw [hDev (oneEach a c) (by simp [oneEach, M]), hC1_eval]
    exact h1

end PEqualNP.Outside.L_lib_376_aux

theorem PEqualNP.Outside.L_lib_376 : ∀ (n m : ℕ) (A : Fin (n + 1) → Fin m → Bool) (u : Fin (n + 1))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (K : Finset (Fin C.gates.length)),
  let N := n + 1 + m
  let reads := fun (g : PEqualNP.CircuitLowerBounds.Gate) (w : ℕ) =>
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some w) ∨
    (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ w ∈ g.inputs)
  PEqualNP.MetaComplexity.FanInTwo C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack N C →
  PEqualNP.Represents.Represents A C →
  (∃ x : List Bool, x.length = N ∧ x.getD u.val false = false ∧ C.eval x = false) →
  (∀ j ∈ K, reads (C.gates.get j) u.val ∨
    ∃ i : Fin C.gates.length, i < j ∧ reads (C.gates.get i) u.val ∧
      ((C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      reads (C.gates.get j) (N + i.val)) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
    D.size + K.card ≤ C.size ∧
    PEqualNP.Represents.Represents (fun a c => A (u.succAbove a) c) D ∧
    PEqualNP.MetaComplexity.FanInTwo D ∧
    (PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.Monotone2 D) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) D ∧
    (∀ g ∈ D.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) ∧
      (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not →
        g.inputs.length = 2 ∧ g.inputs.Nodup)) ∧
    (∀ i : Fin D.gates.length, n + m + i.val ≠ D.output →
      ∃ j : Fin D.gates.length, i < j ∧ reads (D.gates.get j) (n + m + i.val)) :=
  PEqualNP.Outside.L_lib_376_aux.main_aux
