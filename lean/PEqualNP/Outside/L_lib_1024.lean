import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1024

open PEqualNP.CircuitLowerBounds

/-!
# Shared Circuit for a Weighted Hash Vote

We construct a family of shared circuits parameterized by an h x t binary matrix M,
a sign table sigma on t bits, and an exact integer rounding threshold tau in Fin (2*L).
The bucket map is b_M(u, v) = u xor M*v and the within-bucket address is a(u, v) = v.
-/

section CircuitInfra

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def Legal (n : ℕ) (gs : List Gate) : Prop :=
  (∀ i : Fin gs.length, ∀ v ∈ (gs.get i).inputs, v < n + i.val) ∧
  (∀ g ∈ gs, g.inputs.length ≤ 2 ∧
    (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))

noncomputable def gateCost (g : Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

noncomputable def costList (gs : List Gate) : ℕ :=
  gs.countP gateCost

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs ++ [g]) w = run gs w ++ [g.op.eval (g.inputs.map fun i => (run gs w).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
    omega

theorem getD_append_left_lt (l r : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ r).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_self (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + gs.length) :
    (run (gs ++ hs) w).getD i false = (run gs w).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_append_left_lt, ih]
    rw [run_length, List.length_append]
    omega

theorem run_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (run gs (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  have h1 := run_prefix [] gs (List.ofFn x) i (by simp [hi])
  simp only [List.nil_append, run_nil] at h1
  rw [h1, List.getD_eq_getElem _ _ (by simp [hi])]
  simp

theorem run_snoc_new (gs : List Gate) (g : Gate) (w : List Bool) :
    (run (gs ++ [g]) w).getD (w.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (run gs w).getD i false) := by
  rw [run_snoc, ← run_length gs w, getD_snoc_self]

theorem Legal_nil (n : ℕ) : Legal n [] := by
  refine ⟨fun i => Fin.elim0 i, fun g hg => ?_⟩
  simp at hg

theorem Legal_snoc {n : ℕ} {gs : List Gate} {g : Gate}
    (hgs : Legal n gs)
    (hin : ∀ v ∈ g.inputs, v < n + gs.length)
    (hlen : g.inputs.length ≤ 2)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)) :
    Legal n (gs ++ [g]) := by
  refine ⟨fun i v hv => ?_, fun g' hg' => ?_⟩
  · by_cases hi : i.val < gs.length
    · have hget : (gs ++ [g]).get i = gs.get ⟨i.val, hi⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left hi]
      rw [hget] at hv
      exact hgs.1 ⟨i.val, hi⟩ v hv
    · have heq : i.val = gs.length := by
        have := i.isLt
        simp at this
        omega
      have hget : (gs ++ [g]).get i = g := by
        simp [List.get_eq_getElem, heq]
      rw [hget] at hv
      rw [heq]
      exact hin v hv
  · simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hgs.2 g' hg'
    · exact ⟨hlen, hop⟩

theorem costList_nil : costList [] = 0 := rfl

theorem costList_append (gs hs : List Gate) :
    costList (gs ++ hs) = costList gs + costList hs := by
  simp [costList, List.countP_append]

theorem costList_snoc (gs : List Gate) (g : Gate) :
    costList (gs ++ [g]) = costList gs + if gateCost g then 1 else 0 := by
  simp [costList, List.countP_append]

def gConstFalse : Gate := ⟨.or, []⟩
def gConstTrue : Gate := ⟨.and, []⟩
def gNot (u : ℕ) : Gate := ⟨.not, [u]⟩
def gXnor (u v : ℕ) : Gate := ⟨.mod 2, [u, v]⟩
def gAnd (u v : ℕ) : Gate := ⟨.and, [u, v]⟩

theorem gateCost_gConstFalse : gateCost gConstFalse = false := by
  simp [gateCost, gConstFalse]

theorem gateCost_gConstTrue : gateCost gConstTrue = false := by
  simp [gateCost, gConstTrue]

theorem gateCost_gNot (u : ℕ) : gateCost (gNot u) = false := by
  simp [gateCost, gNot]

theorem gateCost_gXnor (u v : ℕ) : gateCost (gXnor u v) = false := by
  simp [gateCost, gXnor]

theorem gateCost_gAnd (u v : ℕ) : gateCost (gAnd u v) = true := by
  simp [gateCost, gAnd]

theorem eval_gXnor (a b : Bool) :
    GateOp.eval (.mod 2) [a, b] = !(xor a b) := by
  cases a <;> cases b <;> rfl

theorem eval_gAnd (a b : Bool) :
    GateOp.eval .and [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_gNot (a : Bool) :
    GateOp.eval .not [a] = !a := by
  cases a <;> rfl

def addConstFalse (n : ℕ) (gs : List Gate) : List Gate × ℕ :=
  (gs ++ [gConstFalse], n + gs.length)

def addConstTrue (n : ℕ) (gs : List Gate) : List Gate × ℕ :=
  (gs ++ [gConstTrue], n + gs.length)

def addAnd (n : ℕ) (gs : List Gate) (u v : ℕ) : List Gate × ℕ :=
  (gs ++ [gAnd u v], n + gs.length)

def addXor (n : ℕ) (gs : List Gate) (u v : ℕ) : List Gate × ℕ :=
  (gs ++ [gXnor u v, gNot (n + gs.length)], n + gs.length + 1)

theorem addConstFalse_spec {n : ℕ} {gs : List Gate} (hgs : Legal n gs) :
    let res := addConstFalse n gs
    (∃ hs, res.1 = gs ++ hs) ∧ Legal n res.1 ∧ costList res.1 = costList gs ∧
    res.2 < n + res.1.length ∧
    ∀ x : Fin n → Bool, (run res.1 (List.ofFn x)).getD res.2 false = false := by
  refine ⟨⟨[gConstFalse], rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact Legal_snoc hgs (by simp [gConstFalse]) (by simp [gConstFalse]) (Or.inr (Or.inl rfl))
  · simp [addConstFalse, costList_snoc, gateCost_gConstFalse]
  · simp [addConstFalse]
  · intro x
    have h := run_snoc_new gs gConstFalse (List.ofFn x)
    simp only [List.length_ofFn] at h
    simpa [addConstFalse, gConstFalse, GateOp.eval] using h

theorem addConstTrue_spec {n : ℕ} {gs : List Gate} (hgs : Legal n gs) :
    let res := addConstTrue n gs
    (∃ hs, res.1 = gs ++ hs) ∧ Legal n res.1 ∧ costList res.1 = costList gs ∧
    res.2 < n + res.1.length ∧
    ∀ x : Fin n → Bool, (run res.1 (List.ofFn x)).getD res.2 false = true := by
  refine ⟨⟨[gConstTrue], rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact Legal_snoc hgs (by simp [gConstTrue]) (by simp [gConstTrue]) (Or.inl rfl)
  · simp [addConstTrue, costList_snoc, gateCost_gConstTrue]
  · simp [addConstTrue]
  · intro x
    have h := run_snoc_new gs gConstTrue (List.ofFn x)
    simp only [List.length_ofFn] at h
    simpa [addConstTrue, gConstTrue, GateOp.eval] using h

theorem addAnd_spec {n : ℕ} {gs : List Gate} {u v : ℕ}
    (hgs : Legal n gs) (hu : u < n + gs.length) (hv : v < n + gs.length) :
    let res := addAnd n gs u v
    (∃ hs, res.1 = gs ++ hs) ∧ Legal n res.1 ∧ costList res.1 = costList gs + 1 ∧
    res.2 < n + res.1.length ∧
    ∀ x : Fin n → Bool, (run res.1 (List.ofFn x)).getD res.2 false =
      ((run gs (List.ofFn x)).getD u false && (run gs (List.ofFn x)).getD v false) := by
  refine ⟨⟨[gAnd u v], rfl⟩, ?_, ?_, ?_, ?_⟩
  · refine Legal_snoc hgs ?_ (by simp [gAnd]) (Or.inl rfl)
    intro w hw
    simp [gAnd] at hw
    rcases hw with rfl | rfl <;> assumption
  · simp [addAnd, costList_snoc, gateCost_gAnd]
  · simp [addAnd]
  · intro x
    have h := run_snoc_new gs (gAnd u v) (List.ofFn x)
    simp only [List.length_ofFn] at h
    simpa [addAnd, gAnd, eval_gAnd] using h

theorem addXor_spec {n : ℕ} {gs : List Gate} {u v : ℕ}
    (hgs : Legal n gs) (hu : u < n + gs.length) (hv : v < n + gs.length) :
    let res := addXor n gs u v
    (∃ hs, res.1 = gs ++ hs) ∧ Legal n res.1 ∧ costList res.1 = costList gs ∧
    res.2 < n + res.1.length ∧
    ∀ x : Fin n → Bool, (run res.1 (List.ofFn x)).getD res.2 false =
      xor ((run gs (List.ofFn x)).getD u false) ((run gs (List.ofFn x)).getD v false) := by
  have h1 : Legal n (gs ++ [gXnor u v]) := by
    refine Legal_snoc hgs ?_ (by simp [gXnor]) (Or.inr (Or.inr (Or.inl rfl)))
    intro w hw
    simp [gXnor] at hw
    rcases hw with rfl | rfl <;> assumption
  have h2 : Legal n ((gs ++ [gXnor u v]) ++ [gNot (n + gs.length)]) := by
    refine Legal_snoc h1 ?_ (by simp [gNot]) (Or.inr (Or.inr (Or.inr ⟨rfl, by simp [gNot]⟩)))
    intro w hw
    simp [gNot] at hw
    subst hw
    simp
  have hcat : gs ++ [gXnor u v, gNot (n + gs.length)] = (gs ++ [gXnor u v]) ++ [gNot (n + gs.length)] := by
    simp
  refine ⟨⟨[gXnor u v, gNot (n + gs.length)], rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [addXor, hcat]; exact h2
  · rw [addXor, hcat, costList_snoc, costList_snoc, gateCost_gNot, gateCost_gXnor]
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  · simp only [addXor, List.length_append, List.length_cons, List.length_nil]; omega
  · intro x
    dsimp only [addXor]
    rw [hcat]
    have hn : n + gs.length + 1 = (List.ofFn x).length + (gs ++ [gXnor u v]).length := by
      simp only [List.length_ofFn, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hn, run_snoc_new]
    simp only [gNot, List.map_cons, List.map_nil, eval_gNot]
    have hmid : (run (gs ++ [gXnor u v]) (List.ofFn x)).getD (n + gs.length) false =
        !(xor ((run gs (List.ofFn x)).getD u false) ((run gs (List.ofFn x)).getD v false)) := by
      have hm := run_snoc_new gs (gXnor u v) (List.ofFn x)
      simp only [List.length_ofFn] at hm
      simpa [gXnor, eval_gXnor] using hm
    rw [hmid, Bool.not_not]

def addXorListLoop (n : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, acc)
  | u :: us =>
    let r := addXor n gs acc u
    addXorListLoop n r.1 r.2 us

def addXorList (n : ℕ) (gs : List Gate) (ws : List ℕ) : List Gate × ℕ :=
  let r0 := addConstFalse n gs
  addXorListLoop n r0.1 r0.2 ws

theorem addXorListLoop_spec {n : ℕ} (ws : List ℕ) (gs : List Gate) (acc : ℕ)
    (hgs : Legal n gs) (hacc : acc < n + gs.length)
    (hws : ∀ u ∈ ws, u < n + gs.length) :
    let res := addXorListLoop n gs acc ws
    (∃ hs, res.1 = gs ++ hs) ∧ Legal n res.1 ∧ costList res.1 = costList gs ∧
    res.2 < n + res.1.length ∧
    ∀ x : Fin n → Bool, (run res.1 (List.ofFn x)).getD res.2 false =
      ws.foldl (fun a u => xor a ((run gs (List.ofFn x)).getD u false))
        ((run gs (List.ofFn x)).getD acc false) := by
  induction ws generalizing gs acc with
  | nil =>
    exact ⟨⟨[], by simp [addXorListLoop]⟩, hgs, by simp [addXorListLoop], hacc, fun _ => rfl⟩
  | cons u us ih =>
    have hu : u < n + gs.length := hws u (by simp)
    have hr := addXor_spec hgs hacc hu
    rcases hr with ⟨⟨h1, heq1⟩, hleg1, hcost1, hout1, heval1⟩
    have hws' : ∀ w ∈ us, w < n + (addXor n gs acc u).1.length := by
      intro w hw
      have := hws w (by simp [hw])
      rw [heq1, List.length_append]
      omega
    have hih := ih (addXor n gs acc u).1 (addXor n gs acc u).2 hleg1 hout1 hws'
    rcases hih with ⟨⟨h2, heq2⟩, hleg2, hcost2, hout2, heval2⟩
    refine ⟨⟨h1 ++ h2, by rw [addXorListLoop, heq2, heq1, List.append_assoc]⟩, hleg2, ?_, hout2, ?_⟩
    · simp only [addXorListLoop, hcost2, hcost1]
    · intro x
      simp only [addXorListLoop, List.foldl_cons]
      rw [heval2 x, heval1 x]
      have hpre : ∀ w ∈ us, (run (addXor n gs acc u).1 (List.ofFn x)).getD w false =
          (run gs (List.ofFn x)).getD w false := fun w hw => by
        have hw_lt : w < n + gs.length := hws w (by simp [hw])
        rw [heq1]; exact run_prefix gs h1 (List.ofFn x) w (by simp [hw_lt])
      have hsame : ∀ (l : List ℕ), (∀ w ∈ l, (run (addXor n gs acc u).1 (List.ofFn x)).getD w false =
          (run gs (List.ofFn x)).getD w false) → ∀ a,
          l.foldl (fun b w => xor b ((run (addXor n gs acc u).1 (List.ofFn x)).getD w false)) a =
          l.foldl (fun b w => xor b ((run gs (List.ofFn x)).getD w false)) a := by
        intro l hl
        induction l with
        | nil => intro a; rfl
        | cons w l' ih =>
          intro a
          simp only [List.foldl_cons]
          rw [hl w (by simp)]
          exact ih (fun v hv => hl v (by simp [hv])) _
      exact hsame us hpre _

theorem addXorList_spec {n : ℕ} {gs : List Gate} {ws : List ℕ}
    (hgs : Legal n gs) (hws : ∀ u ∈ ws, u < n + gs.length) :
    let res := addXorList n gs ws
    (∃ hs, res.1 = gs ++ hs) ∧ Legal n res.1 ∧ costList res.1 = costList gs ∧
    res.2 < n + res.1.length ∧
    ∀ x : Fin n → Bool, (run res.1 (List.ofFn x)).getD res.2 false =
      ws.foldl (fun a u => xor a ((run gs (List.ofFn x)).getD u false)) false := by
  have h0 := addConstFalse_spec hgs
  rcases h0 with ⟨⟨h0s, heq0⟩, hleg0, hcost0, hout0, heval0⟩
  have hws0 : ∀ u ∈ ws, u < n + (addConstFalse n gs).1.length := by
    intro u hu
    have := hws u hu
    rw [heq0, List.length_append]
    omega
  have hl := addXorListLoop_spec ws (addConstFalse n gs).1 (addConstFalse n gs).2 hleg0 hout0 hws0
  rcases hl with ⟨⟨hls, heql⟩, hlegl, hcostl, houtl, hevall⟩
  refine ⟨⟨h0s ++ hls, by rw [addXorList, heql, heq0, List.append_assoc]⟩, hlegl, ?_, houtl, ?_⟩
  · simp only [addXorList, hcostl, hcost0]
  · intro x
    simp only [addXorList]
    rw [hevall x, heval0 x]
    have hpre : ∀ w ∈ ws, (run (addConstFalse n gs).1 (List.ofFn x)).getD w false =
        (run gs (List.ofFn x)).getD w false := fun w hw => by
      have hw_lt : w < n + gs.length := hws w hw
      rw [heq0]; exact run_prefix gs h0s (List.ofFn x) w (by simp [hw_lt])
    have hsame : ∀ (l : List ℕ), (∀ w ∈ l, (run (addConstFalse n gs).1 (List.ofFn x)).getD w false =
        (run gs (List.ofFn x)).getD w false) → ∀ a,
        l.foldl (fun b w => xor b ((run (addConstFalse n gs).1 (List.ofFn x)).getD w false)) a =
        l.foldl (fun b w => xor b ((run gs (List.ofFn x)).getD w false)) a := by
      intro l hl
      induction l with
      | nil => intro a; rfl
      | cons w l' ih =>
        intro a
        simp only [List.foldl_cons]
        rw [hl w (by simp)]
        exact ih (fun v hv => hl v (by simp [hv])) _
    exact hsame ws hpre false

end CircuitInfra

section MonomialsAndANF

def monoVals : List Bool → List Bool
  | [] => [true]
  | b :: bs => monoVals bs ++ (monoVals bs).map (fun m => m && b)

theorem monoVals_length (bs : List Bool) : (monoVals bs).length = 2 ^ bs.length := by
  induction bs with
  | nil => simp [monoVals]
  | cons b bs ih =>
    simp [monoVals, ih, Nat.pow_succ, Nat.mul_two]

def xorDot (cs vs : List Bool) : Bool :=
  (List.zipWith (fun c v => c && v) cs vs).foldl xor false

theorem foldl_xor_init (l : List Bool) (a : Bool) :
    l.foldl xor a = xor a (l.foldl xor false) := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [ih (xor a b), ih b, Bool.xor_assoc]

theorem xorDot_append {c1 c2 v1 v2 : List Bool} (h : c1.length = v1.length) :
    xorDot (c1 ++ c2) (v1 ++ v2) = xor (xorDot c1 v1) (xorDot c2 v2) := by
  simp only [xorDot, List.zipWith_append h, List.foldl_append]
  rw [foldl_xor_init]

theorem xorDot_map_and (cs vs : List Bool) (b : Bool) :
    xorDot cs (vs.map (fun m => m && b)) = (xorDot cs vs && b) := by
  cases b with
  | true =>
    simp
  | false =>
    simp only [Bool.and_false]
    suffices ∀ l1 l2 : List Bool,
        (List.zipWith (fun c v => c && v) l1 (l2.map (fun _ => false))).foldl xor false = false by
      exact this cs vs
    intro l1 l2
    induction l1 generalizing l2 with
    | nil => simp
    | cons c l1 ih =>
      cases l2 with
      | nil => simp
      | cons v l2 =>
        simp only [List.map_cons, List.zipWith_cons_cons, Bool.and_false, List.foldl_cons, Bool.false_xor]
        exact ih l2

theorem anf_exists : ∀ (m : ℕ) (g : (Fin m → Bool) → Bool),
    ∃ cs : List Bool, cs.length = 2 ^ m ∧
      ∀ y : Fin m → Bool, g y = xorDot cs (monoVals (List.ofFn y)) := by
  intro m
  induction m with
  | zero =>
    intro g
    refine ⟨[g Fin.elim0], by simp, fun y => ?_⟩
    have hy : y = Fin.elim0 := funext fun i => Fin.elim0 i
    subst hy
    simp [monoVals, xorDot]
  | succ m ih =>
    intro g
    let g0 : (Fin m → Bool) → Bool := fun y' => g (Fin.cons false y')
    let g1 : (Fin m → Bool) → Bool := fun y' => xor (g (Fin.cons false y')) (g (Fin.cons true y'))
    obtain ⟨c0, hc0_len, hc0⟩ := ih g0
    obtain ⟨c1, hc1_len, hc1⟩ := ih g1
    refine ⟨c0 ++ c1, ?_, ?_⟩
    · simp [hc0_len, hc1_len, Nat.pow_succ, Nat.mul_two]
    · intro y
      let b : Bool := y 0
      let y' : Fin m → Bool := fun i => y i.succ
      have hy : y = Fin.cons b y' := by
        funext i
        refine Fin.cases rfl (fun _ => rfl) i
      have hof : List.ofFn y = b :: List.ofFn y' := by
        rw [List.ofFn_succ]
      rw [hof, monoVals]
      have hlen : c0.length = (monoVals (List.ofFn y')).length := by
        rw [hc0_len, monoVals_length, List.length_ofFn]
      rw [xorDot_append hlen, xorDot_map_and, ← hc0 y', ← hc1 y']
      rw [hy]
      cases b <;> simp [g0, g1]

def selectWires : List Bool → List ℕ → List ℕ
  | [], _ => []
  | _, [] => []
  | c :: cs, w :: ws => if c then w :: selectWires cs ws else selectWires cs ws

theorem mem_selectWires {cs : List Bool} {ws : List ℕ} {w : ℕ}
    (hw : w ∈ selectWires cs ws) : w ∈ ws := by
  induction cs generalizing ws with
  | nil => simp [selectWires] at hw
  | cons c cs ih =>
    cases ws with
    | nil => simp [selectWires] at hw
    | cons u ws =>
      simp only [selectWires] at hw
      split_ifs at hw with hc
      · simp only [List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · exact Or.inl rfl
        · exact Or.inr (ih hw)
      · exact List.mem_cons_of_mem u (ih hw)

theorem foldl_xor_selectWires (f : ℕ → Bool) (cs : List Bool) (ws : List ℕ) (a : Bool) :
    (selectWires cs ws).foldl (fun acc w => xor acc (f w)) a =
      xor a (xorDot cs (ws.map f)) := by
  induction cs generalizing ws a with
  | nil => simp [selectWires, xorDot]
  | cons c cs ih =>
    cases ws with
    | nil => simp [selectWires, xorDot]
    | cons u ws =>
      simp only [selectWires, List.map_cons, xorDot, List.zipWith_cons_cons, List.foldl_cons,
        Bool.false_xor]
      rw [foldl_xor_init]
      cases c with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.false_xor]
        simpa [xorDot] using ih ws a
      | true =>
        simp only [↓reduceIte, List.foldl_cons, Bool.true_and]
        rw [ih ws (xor a (f u)), Bool.xor_assoc]
        rfl

def addAndEach (n : ℕ) (gs : List Gate) (v : ℕ) : List ℕ → List Gate × List ℕ
  | [] => (gs, [])
  | m :: ms =>
    let r1 := addAnd n gs m v
    let r2 := addAndEach n r1.1 v ms
    (r2.1, r1.2 :: r2.2)

theorem addAndEach_spec {n : ℕ} (ms : List ℕ) (gs : List Gate) (v : ℕ)
    (hgs : Legal n gs) (hv : v < n + gs.length)
    (hms : ∀ m ∈ ms, m < n + gs.length) :
    let res := addAndEach n gs v ms
    (∃ hs, res.1 = gs ++ hs) ∧ Legal n res.1 ∧
    costList res.1 = costList gs + ms.length ∧
    res.2.length = ms.length ∧
    (∀ w ∈ res.2, w < n + res.1.length) ∧
    ∀ x : Fin n → Bool,
      res.2.map (fun w => (run res.1 (List.ofFn x)).getD w false) =
        ms.map (fun m => (run gs (List.ofFn x)).getD m false && (run gs (List.ofFn x)).getD v false) := by
  induction ms generalizing gs with
  | nil =>
    exact ⟨⟨[], by simp [addAndEach]⟩, hgs, by simp [addAndEach], by simp [addAndEach],
      by simp [addAndEach], fun _ => rfl⟩
  | cons m ms ih =>
    have hm : m < n + gs.length := hms m (by simp)
    have hr1 := addAnd_spec hgs hm hv
    rcases hr1 with ⟨⟨h1, heq1⟩, hleg1, hcost1, hout1, heval1⟩
    have hv1 : v < n + (addAnd n gs m v).1.length := by rw [heq1, List.length_append]; omega
    have hms1 : ∀ u ∈ ms, u < n + (addAnd n gs m v).1.length := by
      intro u hu
      have := hms u (by simp [hu])
      rw [heq1, List.length_append]
      omega
    have hih := ih (addAnd n gs m v).1 hleg1 hv1 hms1
    rcases hih with ⟨⟨h2, heq2⟩, hleg2, hcost2, hlen2, hmem2, heval2⟩
    refine ⟨⟨h1 ++ h2, by rw [addAndEach, heq2, heq1, List.append_assoc]⟩, hleg2, ?_, ?_, ?_, ?_⟩
    · simp only [addAndEach, hcost2, hcost1, List.length_cons]
      omega
    · simp [addAndEach, hlen2]
    · intro w hw
      dsimp only [addAndEach] at *
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · rw [heq2, List.length_append]
        omega
      · exact hmem2 w hw
    · intro x
      simp only [addAndEach, List.map_cons]
      congr 1
      · rw [heq2]
        rw [run_prefix _ h2 (List.ofFn x) _ (by simp [hout1])]
        exact heval1 x
      · rw [heval2 x]
        apply List.map_congr_left
        intro u hu
        have hu0 : u < n + gs.length := hms u (by simp [hu])
        rw [heq1]
        rw [run_prefix gs h1 (List.ofFn x) u (by simp [hu0])]
        rw [run_prefix gs h1 (List.ofFn x) v (by simp [hv])]

def addMonomials (n : ℕ) (gs : List Gate) : List ℕ → List Gate × List ℕ
  | [] =>
    let r0 := addConstTrue n gs
    (r0.1, [r0.2])
  | v :: vs =>
    let r1 := addMonomials n gs vs
    let r2 := addAndEach n r1.1 v r1.2
    (r2.1, r1.2 ++ r2.2)

theorem addMonomials_spec {n : ℕ} (inWires : List ℕ) (gs : List Gate)
    (hgs : Legal n gs) (hin : ∀ v ∈ inWires, v < n + gs.length) :
    let res := addMonomials n gs inWires
    (∃ hs, res.1 = gs ++ hs) ∧ Legal n res.1 ∧
    costList res.1 = costList gs + (2 ^ inWires.length - 1) ∧
    res.2.length = 2 ^ inWires.length ∧
    (∀ w ∈ res.2, w < n + res.1.length) ∧
    ∀ x : Fin n → Bool,
      res.2.map (fun w => (run res.1 (List.ofFn x)).getD w false) =
        monoVals (inWires.map (fun u => (run gs (List.ofFn x)).getD u false)) := by
  induction inWires generalizing gs with
  | nil =>
    have h0 := addConstTrue_spec hgs
    rcases h0 with ⟨⟨h0s, heq0⟩, hleg0, hcost0, hout0, heval0⟩
    refine ⟨⟨h0s, by simp [addMonomials, heq0]⟩, hleg0, ?_, by simp [addMonomials], ?_, ?_⟩
    · simp [addMonomials, hcost0]
    · intro w hw; simp [addMonomials] at hw; subst hw; exact hout0
    · intro x
      simp only [addMonomials, List.map_cons, List.map_nil, monoVals]
      rw [heval0 x]
  | cons v vs ih =>
    have hv : v < n + gs.length := hin v (by simp)
    have hvs : ∀ u ∈ vs, u < n + gs.length := fun u hu => hin u (by simp [hu])
    have hr1 := ih gs hgs hvs
    rcases hr1 with ⟨⟨h1, heq1⟩, hleg1, hcost1, hlen1, hmem1, heval1⟩
    have hv1 : v < n + (addMonomials n gs vs).1.length := by
      rw [heq1, List.length_append]; omega
    have hr2 := addAndEach_spec (addMonomials n gs vs).2 (addMonomials n gs vs).1 v hleg1 hv1 hmem1
    rcases hr2 with ⟨⟨h2, heq2⟩, hleg2, hcost2, hlen2, hmem2, heval2⟩
    refine ⟨⟨h1 ++ h2, by dsimp only [addMonomials]; rw [heq2, heq1, List.append_assoc]⟩, hleg2, ?_, ?_, ?_, ?_⟩
    · simp only [addMonomials, hcost2, hcost1, hlen1, List.length_cons, Nat.pow_succ, Nat.mul_two]
      have hpos : 1 ≤ 2 ^ vs.length := Nat.one_le_pow _ _ (by omega)
      omega
    · simp [addMonomials, hlen1, hlen2, Nat.pow_succ, Nat.mul_two]
    · intro w hw
      dsimp only [addMonomials] at *
      simp only [List.mem_append] at hw
      rcases hw with hw | hw
      · have := hmem1 w hw
        rw [heq2, List.length_append]
        omega
      · exact hmem2 w hw
    · intro x
      simp only [addMonomials, List.map_append, List.map_cons, monoVals]
      have hleft : (addMonomials n gs vs).2.map
            (fun w => (run (addAndEach n (addMonomials n gs vs).1 v (addMonomials n gs vs).2).1 (List.ofFn x)).getD w false) =
          monoVals (vs.map (fun u => (run gs (List.ofFn x)).getD u false)) := by
        rw [← heval1 x]
        apply List.map_congr_left
        intro w hw
        rw [heq2]
        exact run_prefix _ h2 (List.ofFn x) w (by simp [hmem1 w hw])
      rw [hleft, heval2 x]
      congr 1
      have hv_eq : (run (addMonomials n gs vs).1 (List.ofFn x)).getD v false =
          (run gs (List.ofFn x)).getD v false := by
        rw [heq1]
        exact run_prefix gs h1 (List.ofFn x) v (by simp [hv])
      have hmap : (addMonomials n gs vs).2.map
            (fun m => (run (addMonomials n gs vs).1 (List.ofFn x)).getD m false &&
              (run (addMonomials n gs vs).1 (List.ofFn x)).getD v false) =
          ((addMonomials n gs vs).2.map
            (fun m => (run (addMonomials n gs vs).1 (List.ofFn x)).getD m false)).map
            (fun m => m && (run gs (List.ofFn x)).getD v false) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro m _
        simp only [Function.comp_apply, hv_eq]
      rw [hmap, heval1 x]

end MonomialsAndANF

section HashMapAndCircuit

abbrev Mat (h t : ℕ) := Fin h → Fin t → Bool

def addr {n h : ℕ} (hh : h ≤ n) (x : Fin n → Bool) : Fin (n - h) → Bool :=
  fun i => x ⟨h + i.val, by omega⟩

def dotBool {t : ℕ} (a b : Fin t → Bool) : Bool :=
  (List.finRange t).foldl (fun acc i => xor acc (a i && b i)) false

def bucketMap {n h : ℕ} (hh : h ≤ n) (M : Mat h (n - h)) (x : Fin n → Bool) : Fin h → Bool :=
  fun j => xor (x ⟨j.val, by omega⟩) (dotBool (M j) (addr hh x))

def v1 {t : ℕ} (a : Fin t → Bool) : Fin (t / 2) → Bool :=
  fun i => a ⟨i.val, by omega⟩

def v2 {t : ℕ} (a : Fin t → Bool) : Fin (t - t / 2) → Bool :=
  fun i => a ⟨t / 2 + i.val, by omega⟩

def joinVec {t : ℕ} (u : Fin (t / 2) → Bool) (z : Fin (t - t / 2) → Bool) : Fin t → Bool :=
  fun i => if hi : i.val < t / 2 then u ⟨i.val, hi⟩ else z ⟨i.val - t / 2, by omega⟩

theorem joinVec_v1_v2 {t : ℕ} (a : Fin t → Bool) :
    joinVec (v1 a) (v2 a) = a := by
  funext i
  simp only [joinVec, v1, v2]
  split_ifs with hi
  · rfl
  · congr 1
    apply Fin.ext
    change t / 2 + (i.val - t / 2) = i.val
    omega

theorem foldl_xor_unique {α : Type} [DecidableEq α] (l : List α) (a : α) (f : α → Bool)
    (hnd : l.Nodup) (ha : a ∈ l) (init : Bool) :
    l.foldl (fun acc u => xor acc (decide (a = u) && f u)) init = xor init (f a) := by
  induction l generalizing init with
  | nil => simp at ha
  | cons u l ih =>
    simp only [List.nodup_cons, List.mem_cons] at hnd ha
    simp only [List.foldl_cons]
    rcases ha with rfl | ha
    · have hzero : ∀ b, l.foldl (fun acc v => xor acc (decide (a = v) && f v)) b = b := by
        have hnot : a ∉ l := hnd.1
        clear ih hnd
        induction l with
        | nil => intro b; rfl
        | cons v l' ihl =>
          intro b
          have hne : a ≠ v := fun h => hnot (by simp [h])
          simp only [List.foldl_cons, decide_eq_false hne, Bool.false_and, Bool.xor_false]
          exact ihl (fun h => hnot (by simp [h])) b
      simp only [decide_true, Bool.true_and]
      exact hzero _
    · have hne : a ≠ u := fun h => hnd.1 (h ▸ ha)
      simp only [decide_eq_false hne, Bool.false_and, Bool.xor_false]
      exact ih hnd.2 ha init

theorem dotBool_eq_xorDot {t : ℕ} (a b : Fin t → Bool) :
    dotBool a b = xorDot (List.ofFn a) (List.ofFn b) := by
  simp only [dotBool, xorDot]
  have hzip : List.zipWith (fun c v => c && v) (List.ofFn a) (List.ofFn b) =
      (List.finRange t).map (fun i => a i && b i) := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp
  rw [hzip, List.foldl_map]

noncomputable def addBucketWires (n h : ℕ) (hh : h ≤ n) (M : Mat h (n - h))
    (gs : List Gate) : List (Fin h) → List Gate × List ℕ
  | [] => (gs, [])
  | j :: js =>
    let addrWires := (List.finRange (n - h)).map (fun i => h + i.val)
    let ws := j.val :: selectWires (List.ofFn (M j)) addrWires
    let r1 := addXorList n gs ws
    let r2 := addBucketWires n h hh M r1.1 js
    (r2.1, r1.2 :: r2.2)

theorem addBucketWires_spec {n h : ℕ} (hh : h ≤ n) (M : Mat h (n - h))
    (js : List (Fin h)) (gs : List Gate) (hgs : Legal n gs) :
    let res := addBucketWires n h hh M gs js
    (∃ hs, res.1 = gs ++ hs) ∧ Legal n res.1 ∧
    costList res.1 = costList gs ∧
    res.2.length = js.length ∧
    (∀ w ∈ res.2, w < n + res.1.length) ∧
    ∀ x : Fin n → Bool,
      res.2.map (fun w => (run res.1 (List.ofFn x)).getD w false) =
        js.map (fun j => bucketMap hh M x j) := by
  induction js generalizing gs with
  | nil =>
    exact ⟨⟨[], by simp [addBucketWires]⟩, hgs, by simp [addBucketWires], rfl, by simp [addBucketWires], fun _ => rfl⟩
  | cons j js ih =>
    let addrWires := (List.finRange (n - h)).map (fun i => h + i.val)
    let ws := j.val :: selectWires (List.ofFn (M j)) addrWires
    have hws : ∀ u ∈ ws, u < n + gs.length := by
      intro u hu
      simp only [ws, List.mem_cons] at hu
      rcases hu with rfl | hu
      · omega
      · have hm := mem_selectWires hu
        simp only [addrWires, List.mem_map, List.mem_finRange, true_and] at hm
        rcases hm with ⟨i, rfl⟩
        omega
    have hr1 := addXorList_spec hgs hws
    rcases hr1 with ⟨⟨h1, heq1⟩, hleg1, hcost1, hout1, heval1⟩
    have hr2 := ih (addXorList n gs ws).1 hleg1
    rcases hr2 with ⟨⟨h2, heq2⟩, hleg2, hcost2, hlen2, hmem2, heval2⟩
    refine ⟨⟨h1 ++ h2, by
      calc (addBucketWires n h hh M gs (j :: js)).1
          = (addBucketWires n h hh M (addXorList n gs ws).1 js).1 := rfl
        _ = (addXorList n gs ws).1 ++ h2 := heq2
        _ = (gs ++ h1) ++ h2 := congrArg (· ++ h2) heq1
        _ = gs ++ (h1 ++ h2) := List.append_assoc _ _ _⟩,
      hleg2, ?_, ?_, ?_, ?_⟩
    · calc costList (addBucketWires n h hh M gs (j :: js)).1
          = costList (addBucketWires n h hh M (addXorList n gs ws).1 js).1 := rfl
        _ = costList (addXorList n gs ws).1 := hcost2
        _ = costList gs := hcost1
    · calc (addBucketWires n h hh M gs (j :: js)).2.length
          = ((addXorList n gs ws).2 :: (addBucketWires n h hh M (addXorList n gs ws).1 js).2).length := rfl
        _ = (addBucketWires n h hh M (addXorList n gs ws).1 js).2.length + 1 := rfl
        _ = js.length + 1 := congrArg (· + 1) hlen2
        _ = (j :: js).length := rfl
    · intro w hw
      change w ∈ (addXorList n gs ws).2 :: (addBucketWires n h hh M (addXorList n gs ws).1 js).2 at hw
      change w < n + (addBucketWires n h hh M (addXorList n gs ws).1 js).1.length
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · rw [heq2, List.length_append]; omega
      · exact hmem2 w hw
    · intro x
      change ((addXorList n gs ws).2 :: (addBucketWires n h hh M (addXorList n gs ws).1 js).2).map
          (fun w => (run (addBucketWires n h hh M (addXorList n gs ws).1 js).1 (List.ofFn x)).getD w false) =
        (j :: js).map (fun j => bucketMap hh M x j)
      simp only [List.map_cons]
      congr 1
      · have hpre_lt : (addXorList n gs ws).2 < (List.ofFn x).length + (addXorList n gs ws).1.length := by
          rw [List.length_ofFn]; exact hout1
        rw [heq2, run_prefix _ h2 (List.ofFn x) _ hpre_lt, heval1 x]
        simp only [ws, List.foldl_cons, Bool.false_xor]
        rw [run_input gs x j.val (by omega)]
        rw [foldl_xor_selectWires]
        have hmap : addrWires.map (fun w => (run gs (List.ofFn x)).getD w false) =
            List.ofFn (addr hh x) := by
          apply List.ext_getElem
          · simp [addrWires]
          · intro i hi1 hi2
            simp only [addrWires, List.getElem_map, List.getElem_finRange, List.getElem_ofFn, addr]
            exact run_input gs x (h + i) (by simp [addrWires] at hi1; omega)
        rw [hmap, ← dotBool_eq_xorDot]
        rfl
      · exact heval2 x

noncomputable def addProdTerms {n t : ℕ} (σ : (Fin t → Bool) → Bool)
    (mono1Wires mono2Wires : List ℕ) (gs : List Gate) :
    List (Fin (t / 2) → Bool) → List Gate × List ℕ
  | [] => (gs, [])
  | u :: us =>
    let c1 := Classical.choose (anf_exists (t / 2) (fun y => decide (y = u)))
    let r1 := addXorList n gs (selectWires c1 mono1Wires)
    let c2 := Classical.choose (anf_exists (t - t / 2) (fun z => σ (joinVec u z)))
    let r2 := addXorList n r1.1 (selectWires c2 mono2Wires)
    let r3 := addAnd n r2.1 r1.2 r2.2
    let r4 := addProdTerms (n := n) σ mono1Wires mono2Wires r3.1 us
    (r4.1, r3.2 :: r4.2)

theorem addProdTerms_spec {n h : ℕ} (hh : h ≤ n) (σ : (Fin (n - h) → Bool) → Bool)
    (mono1Wires mono2Wires : List ℕ) (us : List (Fin ((n - h) / 2) → Bool))
    (gs : List Gate) (hgs : Legal n gs)
    (hm1_lt : ∀ w ∈ mono1Wires, w < n + gs.length)
    (hm2_lt : ∀ w ∈ mono2Wires, w < n + gs.length)
    (hm1_eval : ∀ x : Fin n → Bool,
      mono1Wires.map (fun w => (run gs (List.ofFn x)).getD w false) =
        monoVals (List.ofFn (v1 (addr hh x))))
    (hm2_eval : ∀ x : Fin n → Bool,
      mono2Wires.map (fun w => (run gs (List.ofFn x)).getD w false) =
        monoVals (List.ofFn (v2 (addr hh x)))) :
    let res := addProdTerms (n := n) σ mono1Wires mono2Wires gs us
    (∃ hs, res.1 = gs ++ hs) ∧ Legal n res.1 ∧
    costList res.1 = costList gs + us.length ∧
    res.2.length = us.length ∧
    (∀ w ∈ res.2, w < n + res.1.length) ∧
    ∀ x : Fin n → Bool,
      res.2.map (fun w => (run res.1 (List.ofFn x)).getD w false) =
        us.map (fun u => decide (v1 (addr hh x) = u) && σ (joinVec u (v2 (addr hh x)))) := by
  induction us generalizing gs with
  | nil =>
    exact ⟨⟨[], by simp [addProdTerms]⟩, hgs, by simp [addProdTerms], rfl, by simp [addProdTerms], fun _ => rfl⟩
  | cons u us ih =>
    let c1 := Classical.choose (anf_exists ((n - h) / 2) (fun y => decide (y = u)))
    have hc1 := Classical.choose_spec (anf_exists ((n - h) / 2) (fun y => decide (y = u)))
    let c2 := Classical.choose (anf_exists ((n - h) - (n - h) / 2) (fun z => σ (joinVec u z)))
    have hc2 := Classical.choose_spec (anf_exists ((n - h) - (n - h) / 2) (fun z => σ (joinVec u z)))
    have hr1 := addXorList_spec hgs (fun w hw => hm1_lt w (mem_selectWires hw)) (ws := selectWires c1 mono1Wires)
    rcases hr1 with ⟨⟨h1, heq1⟩, hleg1, hcost1, hout1, heval1⟩
    set r1 := addXorList n gs (selectWires c1 mono1Wires)
    have hm2_lt1 : ∀ w ∈ mono2Wires, w < n + r1.1.length := fun w hw => by
      have := hm2_lt w hw; rw [heq1, List.length_append]; omega
    have hr2 := addXorList_spec hleg1 (fun w hw => hm2_lt1 w (mem_selectWires hw)) (ws := selectWires c2 mono2Wires)
    rcases hr2 with ⟨⟨h2, heq2⟩, hleg2, hcost2, hout2, heval2⟩
    set r2 := addXorList n r1.1 (selectWires c2 mono2Wires)
    have hout1_2 : r1.2 < n + r2.1.length := by rw [heq2, List.length_append]; omega
    have hr3 := addAnd_spec hleg2 hout1_2 hout2
    rcases hr3 with ⟨⟨h3, heq3⟩, hleg3, hcost3, hout3, heval3⟩
    set r3 := addAnd n r2.1 r1.2 r2.2
    have hprefix3 : r3.1 = gs ++ (h1 ++ h2 ++ h3) := by
      calc r3.1 = r2.1 ++ h3 := heq3
        _ = (r1.1 ++ h2) ++ h3 := congrArg (· ++ h3) heq2
        _ = ((gs ++ h1) ++ h2) ++ h3 := congrArg (fun l => (l ++ h2) ++ h3) heq1
        _ = gs ++ (h1 ++ h2 ++ h3) := by simp [List.append_assoc]
    have hm1_lt3 : ∀ w ∈ mono1Wires, w < n + r3.1.length := fun w hw => by
      have := hm1_lt w hw; rw [hprefix3, List.length_append]; omega
    have hm2_lt3 : ∀ w ∈ mono2Wires, w < n + r3.1.length := fun w hw => by
      have := hm2_lt w hw; rw [hprefix3, List.length_append]; omega
    have hm1_eval3 : ∀ x : Fin n → Bool,
        mono1Wires.map (fun w => (run r3.1 (List.ofFn x)).getD w false) =
          monoVals (List.ofFn (v1 (addr hh x))) := by
      intro x
      rw [← hm1_eval x]
      apply List.map_congr_left
      intro w hw
      rw [hprefix3]
      exact run_prefix gs (h1 ++ h2 ++ h3) (List.ofFn x) w (by simp [hm1_lt w hw])
    have hm2_eval3 : ∀ x : Fin n → Bool,
        mono2Wires.map (fun w => (run r3.1 (List.ofFn x)).getD w false) =
          monoVals (List.ofFn (v2 (addr hh x))) := by
      intro x
      rw [← hm2_eval x]
      apply List.map_congr_left
      intro w hw
      rw [hprefix3]
      exact run_prefix gs (h1 ++ h2 ++ h3) (List.ofFn x) w (by simp [hm2_lt w hw])
    have hr4 := ih r3.1 hleg3 hm1_lt3 hm2_lt3 hm1_eval3 hm2_eval3
    rcases hr4 with ⟨⟨h4, heq4⟩, hleg4, hcost4, hlen4, hmem4, heval4⟩
    refine ⟨⟨(h1 ++ h2 ++ h3) ++ h4, by
      calc (addProdTerms (n := n) σ mono1Wires mono2Wires gs (u :: us)).1
          = (addProdTerms (n := n) σ mono1Wires mono2Wires r3.1 us).1 := rfl
        _ = r3.1 ++ h4 := heq4
        _ = (gs ++ (h1 ++ h2 ++ h3)) ++ h4 := congrArg (· ++ h4) hprefix3
        _ = gs ++ ((h1 ++ h2 ++ h3) ++ h4) := List.append_assoc _ _ _⟩,
      hleg4, ?_, ?_, ?_, ?_⟩
    · calc costList (addProdTerms (n := n) σ mono1Wires mono2Wires gs (u :: us)).1
          = costList (addProdTerms (n := n) σ mono1Wires mono2Wires r3.1 us).1 := rfl
        _ = costList r3.1 + us.length := hcost4
        _ = (costList r2.1 + 1) + us.length := congrArg (· + us.length) hcost3
        _ = (costList r1.1 + 1) + us.length := congrArg (fun k => (k + 1) + us.length) hcost2
        _ = (costList gs + 1) + us.length := congrArg (fun k => (k + 1) + us.length) hcost1
        _ = costList gs + (u :: us).length := by simp; omega
    · calc (addProdTerms (n := n) σ mono1Wires mono2Wires gs (u :: us)).2.length
          = (r3.2 :: (addProdTerms (n := n) σ mono1Wires mono2Wires r3.1 us).2).length := rfl
        _ = (addProdTerms (n := n) σ mono1Wires mono2Wires r3.1 us).2.length + 1 := rfl
        _ = us.length + 1 := congrArg (· + 1) hlen4
        _ = (u :: us).length := rfl
    · intro w hw
      change w ∈ r3.2 :: (addProdTerms (n := n) σ mono1Wires mono2Wires r3.1 us).2 at hw
      change w < n + (addProdTerms (n := n) σ mono1Wires mono2Wires r3.1 us).1.length
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · rw [heq4, List.length_append]; omega
      · exact hmem4 w hw
    · intro x
      change (r3.2 :: (addProdTerms (n := n) σ mono1Wires mono2Wires r3.1 us).2).map
          (fun w => (run (addProdTerms (n := n) σ mono1Wires mono2Wires r3.1 us).1 (List.ofFn x)).getD w false) =
        (u :: us).map (fun u => decide (v1 (addr hh x) = u) && σ (joinVec u (v2 (addr hh x))))
      simp only [List.map_cons]
      congr 1
      · rw [heq4, run_prefix _ h4 (List.ofFn x) _ (by simp [hout3]), heval3 x]
        have hr1_val : (run r2.1 (List.ofFn x)).getD r1.2 false = decide (v1 (addr hh x) = u) := by
          rw [heq2, run_prefix r1.1 h2 (List.ofFn x) r1.2 (by simp [hout1]), heval1 x]
          rw [foldl_xor_selectWires, Bool.false_xor, hm1_eval x, ← hc1.2 (v1 (addr hh x))]
        have hr2_val : (run r2.1 (List.ofFn x)).getD r2.2 false = σ (joinVec u (v2 (addr hh x))) := by
          rw [heval2 x, foldl_xor_selectWires, Bool.false_xor]
          have hm2_1 : mono2Wires.map (fun w => (run r1.1 (List.ofFn x)).getD w false) =
              monoVals (List.ofFn (v2 (addr hh x))) := by
            rw [← hm2_eval x]
            apply List.map_congr_left
            intro w hw
            rw [heq1]
            exact run_prefix gs h1 (List.ofFn x) w (by simp [hm2_lt w hw])
          rw [hm2_1, ← hc2.2 (v2 (addr hh x))]
        rw [hr1_val, hr2_val]
      · exact heval4 x

noncomputable def buildCircuitData {n h : ℕ} (hh : h ≤ n) (M : Mat h (n - h))
    (σ : (Fin (n - h) → Bool) → Bool) : Circuit × (Fin (h + 1) → ℕ) :=
  let t := n - h
  let t1 := t / 2
  let t2 := t - t1
  let rB := addBucketWires n h hh M [] (List.finRange h)
  let v1Wires := (List.finRange t1).map (fun i => h + i.val)
  let rM1 := addMonomials n rB.1 v1Wires
  let v2Wires := (List.finRange t2).map (fun i => h + t1 + i.val)
  let rM2 := addMonomials n rM1.1 v2Wires
  let us := (Finset.univ : Finset (Fin t1 → Bool)).toList
  let rP := addProdTerms (n := n) σ rM1.2 rM2.2 rM2.1 us
  let rS := addXorList n rP.1 rP.2
  let tap : Fin (h + 1) → ℕ := fun j =>
    if _hj : j.val < h then rB.2.getD j.val 0 else rS.2
  (⟨rS.1, rS.2⟩, tap)

theorem buildCircuitData_spec {n h : ℕ} (hh : h ≤ n) (M : Mat h (n - h))
    (σ : (Fin (n - h) → Bool) → Bool) :
    let data := buildCircuitData hh M σ
    let C := data.1
    let tap := data.2
    Legal n C.gates ∧
    costList C.gates ≤ 3 * 2 ^ ((n - h + 1) / 2) ∧
    (∀ j : Fin (h + 1), tap j < n + C.gates.length) ∧
    (∀ (x : Fin n → Bool) (j : Fin h),
      (C.wires (List.ofFn x)).getD (tap ⟨j.val, by omega⟩) false = bucketMap hh M x j) ∧
    (∀ (x : Fin n → Bool),
      (C.wires (List.ofFn x)).getD (tap ⟨h, by omega⟩) false = σ (addr hh x)) := by
  let t := n - h
  let t1 := t / 2
  let t2 := t - t1
  have hrB := addBucketWires_spec hh M (List.finRange h) [] (Legal_nil n)
  rcases hrB with ⟨⟨hB, heqB⟩, hlegB, hcostB, hlenB, hmemB, hevalB⟩
  set rB := addBucketWires n h hh M [] (List.finRange h)
  let v1Wires := (List.finRange t1).map (fun i => h + i.val)
  have hv1_lt : ∀ w ∈ v1Wires, w < n + rB.1.length := by
    intro w hw
    simp only [v1Wires, List.mem_map, List.mem_finRange, true_and] at hw
    rcases hw with ⟨i, rfl⟩
    omega
  have hrM1 := addMonomials_spec v1Wires rB.1 hlegB hv1_lt
  rcases hrM1 with ⟨⟨hM1, heqM1⟩, hlegM1, hcostM1, hlenM1, hmemM1, hevalM1⟩
  set rM1 := addMonomials n rB.1 v1Wires
  let v2Wires := (List.finRange t2).map (fun i => h + t1 + i.val)
  have hv2_lt : ∀ w ∈ v2Wires, w < n + rM1.1.length := by
    intro w hw
    simp only [v2Wires, List.mem_map, List.mem_finRange, true_and] at hw
    rcases hw with ⟨i, rfl⟩
    omega
  have hrM2 := addMonomials_spec v2Wires rM1.1 hlegM1 hv2_lt
  rcases hrM2 with ⟨⟨hM2, heqM2⟩, hlegM2, hcostM2, hlenM2, hmemM2, hevalM2⟩
  set rM2 := addMonomials n rM1.1 v2Wires
  have hm1_lt2 : ∀ w ∈ rM1.2, w < n + rM2.1.length := fun w hw => by
    have := hmemM1 w hw; rw [heqM2, List.length_append]; omega
  have hm1_eval2 : ∀ x : Fin n → Bool,
      rM1.2.map (fun w => (run rM2.1 (List.ofFn x)).getD w false) =
        monoVals (List.ofFn (v1 (addr hh x))) := by
    intro x
    have hpre : rM1.2.map (fun w => (run rM2.1 (List.ofFn x)).getD w false) =
        rM1.2.map (fun w => (run rM1.1 (List.ofFn x)).getD w false) := by
      apply List.map_congr_left
      intro w hw
      rw [heqM2]
      exact run_prefix rM1.1 hM2 (List.ofFn x) w (by simp [hmemM1 w hw])
    rw [hpre, hevalM1 x]
    congr 1
    apply List.ext_getElem
    · simp [v1Wires, List.length_ofFn, List.length_finRange, t1, t]
    · intro i hi1 hi2
      simp only [v1Wires, List.getElem_map, List.getElem_finRange, List.getElem_ofFn, v1, addr]
      exact run_input rB.1 x (h + i) (by simp [v1Wires] at hi1; omega)
  have hm2_eval2 : ∀ x : Fin n → Bool,
      rM2.2.map (fun w => (run rM2.1 (List.ofFn x)).getD w false) =
        monoVals (List.ofFn (v2 (addr hh x))) := by
    intro x
    rw [hevalM2 x]
    congr 1
    apply List.ext_getElem
    · simp [v2Wires, List.length_ofFn, List.length_finRange, t2, t1, t]
    · intro i hi1 hi2
      have hi_lt : h + t1 + i < n := by
        simp only [v2Wires, List.length_map, List.length_finRange] at hi1
        omega
      have hrun := run_input rM1.1 x (h + t1 + i) hi_lt
      have hext_fin : (⟨h + (t1 + i), by omega⟩ : Fin n) = ⟨h + t1 + i, hi_lt⟩ := by apply Fin.ext; change h + (t1 + i) = h + t1 + i; omega
      simp only [v2Wires, List.getElem_map, List.getElem_finRange, List.getElem_ofFn, v2, addr]
      rw [hext_fin]
      exact hrun
  let us := (Finset.univ : Finset (Fin t1 → Bool)).toList
  have hrP := addProdTerms_spec hh σ rM1.2 rM2.2 us rM2.1 hlegM2 hm1_lt2 hmemM2 hm1_eval2 hm2_eval2
  rcases hrP with ⟨⟨hP, heqP⟩, hlegP, hcostP, hlenP, hmemP, hevalP⟩
  set rP := addProdTerms (n := n) σ rM1.2 rM2.2 rM2.1 us
  have hrS := addXorList_spec hlegP hmemP
  rcases hrS with ⟨⟨hS, heqS⟩, hlegS, hcostS, houtS, hevalS⟩
  set rS := addXorList n rP.1 rP.2
  have hprefixB : rS.1 = rB.1 ++ (hM1 ++ hM2 ++ hP ++ hS) := by
    calc rS.1 = rP.1 ++ hS := heqS
      _ = (rM2.1 ++ hP) ++ hS := congrArg (· ++ hS) heqP
      _ = ((rM1.1 ++ hM2) ++ hP) ++ hS := congrArg (fun l => (l ++ hP) ++ hS) heqM2
      _ = (((rB.1 ++ hM1) ++ hM2) ++ hP) ++ hS := congrArg (fun l => ((l ++ hM2) ++ hP) ++ hS) heqM1
      _ = rB.1 ++ (hM1 ++ hM2 ++ hP ++ hS) := by simp [List.append_assoc]
  refine ⟨hlegS, ?_, ?_, ?_, ?_⟩
  · have hus_len : us.length = 2 ^ t1 := by
      simp [us]
    have hv1_len : v1Wires.length = t1 := by simp [v1Wires]
    have hv2_len : v2Wires.length = t2 := by simp [v2Wires]
    have ht_le : t1 ≤ t2 := by omega
    have hpow_le : 2 ^ t1 ≤ 2 ^ t2 := Nat.pow_le_pow_right (by omega) ht_le
    have ht2_eq : t2 = (n - h + 1) / 2 := by omega
    have htot : costList rS.1 = (2 ^ t1 - 1) + (2 ^ t2 - 1) + 2 ^ t1 := by
      simp only [hcostS, hcostP, hcostM2, hcostM1, hcostB, costList_nil, hv1_len, hv2_len, hus_len]
      omega
    change costList rS.1 ≤ 3 * 2 ^ ((n - h + 1) / 2)
    rw [htot, ← ht2_eq]
    omega
  · intro j
    change (if hj : j.val < h then rB.2.getD j.val 0 else rS.2) < n + rS.1.length
    split_ifs with hj
    · have hj' : j.val < rB.2.length := by rw [hlenB]; simp [hj]
      have hmem : rB.2.getD j.val 0 ∈ rB.2 := by
        rw [List.getD_eq_getElem _ _ hj']
        exact List.getElem_mem hj'
      have hlt := hmemB _ hmem
      rw [hprefixB, List.length_append]
      have : 0 ≤ (hM1 ++ hM2 ++ hP ++ hS).length := Nat.zero_le _
      omega
    · exact houtS
  · intro x j
    simp only [buildCircuitData, Circuit.wires, j.isLt, ↓reduceDIte]
    show (run rS.1 (List.ofFn x)).getD (rB.2.getD j.val 0) false = bucketMap hh M x j
    have hj' : j.val < rB.2.length := by rw [hlenB]; simp
    have hmem : rB.2.getD j.val 0 ∈ rB.2 := by
      rw [List.getD_eq_getElem _ _ hj']
      exact List.getElem_mem hj'
    have hpre_lt : rB.2.getD j.val 0 < (List.ofFn x).length + rB.1.length := by
      rw [List.length_ofFn]
      exact hmemB _ hmem
    rw [hprefixB, run_prefix rB.1 (hM1 ++ hM2 ++ hP ++ hS) (List.ofFn x) _ hpre_lt]
    have hidx := congrArg (fun l => l.getD j.val false) (hevalB x)
    have hj_map1 : j.val < (rB.2.map (fun w => (run rB.1 (List.ofFn x)).getD w false)).length := by
      rw [List.length_map]; exact hj'
    have hj_map2 : j.val < ((List.finRange h).map (fun j => bucketMap hh M x j)).length := by
      rw [List.length_map, List.length_finRange]; exact j.isLt
    rw [List.getD_eq_getElem _ _ hj_map1, List.getElem_map] at hidx
    rw [List.getD_eq_getElem _ _ hj_map2, List.getElem_map, List.getElem_finRange] at hidx
    rw [List.getD_eq_getElem _ _ hj']
    exact hidx
  · intro x
    simp only [buildCircuitData, Circuit.wires, lt_self_iff_false, ↓reduceDIte]
    show (run rS.1 (List.ofFn x)).getD rS.2 false = σ (addr hh x)
    rw [hevalS x]
    have hfold : rP.2.foldl (fun a u => xor a ((run rP.1 (List.ofFn x)).getD u false)) false =
        (rP.2.map (fun u => (run rP.1 (List.ofFn x)).getD u false)).foldl xor false := by
      rw [List.foldl_map]
    rw [hfold, hevalP x, List.foldl_map]
    have hnd : us.Nodup := Finset.nodup_toList _
    have hmem : v1 (addr hh x) ∈ us := Finset.mem_toList.mpr (Finset.mem_univ _)
    have huniq := foldl_xor_unique us (v1 (addr hh x))
      (fun u => σ (joinVec u (v2 (addr hh x)))) hnd hmem false
    rw [huniq, Bool.false_xor, joinVec_v1_v2]

end HashMapAndCircuit

section HashCollision

theorem addr_ne_of_bucket_eq {n h : ℕ} (hh : h ≤ n) (M : Mat h (n - h))
    {x x' : Fin n → Bool} (hne : x ≠ x')
    (hb : bucketMap hh M x = bucketMap hh M x') :
    addr hh x ≠ addr hh x' := by
  intro ha
  apply hne
  funext i
  by_cases hi : i.val < h
  · have hbj := congr_fun hb ⟨i.val, hi⟩
    simp only [bucketMap, ha] at hbj
    have hxeq : x ⟨i.val, by omega⟩ = x' ⟨i.val, by omega⟩ := by
      revert hbj
      cases x ⟨i.val, by omega⟩ <;> cases x' ⟨i.val, by omega⟩ <;>
        cases dotBool (M ⟨i.val, hi⟩) (addr hh x') <;> simp
    exact hxeq
  · have haj := congr_fun ha ⟨i.val - h, by omega⟩
    simp only [addr] at haj
    have heq : (⟨h + (i.val - h), by omega⟩ : Fin n) = i := by apply Fin.ext; change h + (i.val - h) = i.val; omega
    rwa [heq] at haj

def shiftCol {h t : ℕ} (i0 : Fin t) (δ : Fin h → Bool) (M : Mat h t) : Mat h t :=
  fun j i => if i = i0 then xor (M j i) (δ j) else M j i

theorem shiftCol_invol {h t : ℕ} (i0 : Fin t) (δ : Fin h → Bool) (M : Mat h t) :
    shiftCol i0 δ (shiftCol i0 δ M) = M := by
  funext j i
  simp only [shiftCol]
  split_ifs
  · cases M j i <;> cases δ j <;> rfl
  · rfl

theorem dotBool_shift {t : ℕ} (i0 : Fin t) (d : Bool) (a b : Fin t → Bool) :
    dotBool (fun i => if i = i0 then xor (a i) d else a i) b =
      xor (dotBool a b) (d && b i0) := by
  have hgen : ∀ (l : List (Fin t)) (init : Bool), l.Nodup →
      l.foldl (fun acc i => xor acc ((if i = i0 then xor (a i) d else a i) && b i)) init =
        xor (l.foldl (fun acc i => xor acc (a i && b i)) init)
          (if i0 ∈ l then d && b i0 else false) := by
    intro l
    induction l with
    | nil => intro init _; simp
    | cons i l ih =>
      intro init hnd
      simp only [List.nodup_cons] at hnd
      simp only [List.foldl_cons, List.mem_cons]
      rw [ih _ hnd.2]
      by_cases hi : i = i0
      · subst hi
        have htr : (i = i) = True := eq_true rfl
        simp only [htr, true_or, hnd.1, ↓reduceIte, Bool.xor_false]
        have hdist : (xor (a i) d && b i) = xor (a i && b i) (d && b i) := by
          cases a i <;> cases d <;> cases b i <;> rfl
        rw [hdist]
        have hstep : ∀ (x y z : Bool),
            l.foldl (fun acc j => xor acc (a j && b j)) (xor (xor x y) z) =
              xor (l.foldl (fun acc j => xor acc (a j && b j)) (xor x y)) z := by
          clear ih hnd hdist
          induction l with
          | nil => intro _ _ _; rfl
          | cons j l' ihl =>
            intro x y z
            simp only [List.foldl_cons]
            have hcomm : xor (xor (xor x y) z) (a j && b j) =
                xor (xor (xor x y) (a j && b j)) z := by
              cases x <;> cases y <;> cases z <;> cases a j <;> cases b j <;> rfl
            rw [hcomm]
            simpa [Bool.xor_assoc] using ihl (xor x y) (a j && b j) z
        have hassoc : xor init (xor (a i && b i) (d && b i)) = xor (xor init (a i && b i)) (d && b i) := by
          cases init <;> cases a i <;> cases b i <;> cases d <;> rfl
        rw [hassoc, hstep init (a i && b i) (d && b i)]
      · have hne : i0 ≠ i := Ne.symm hi
        simp [hi, hne]
  have h := hgen (List.finRange t) false (List.nodup_finRange t)
  simpa [dotBool] using h

theorem bucketMap_shiftCol_xor {n h : ℕ} (hh : h ≤ n) {x x' : Fin n → Bool}
    (i0 : Fin (n - h)) (hdiff : addr hh x i0 ≠ addr hh x' i0)
    (δ : Fin h → Bool) (M : Mat h (n - h)) (j : Fin h) :
    xor (bucketMap hh (shiftCol i0 δ M) x j) (bucketMap hh (shiftCol i0 δ M) x' j) =
      xor (xor (bucketMap hh M x j) (bucketMap hh M x' j)) (δ j) := by
  have hrow : shiftCol i0 δ M j = fun i => if i = i0 then xor (M j i) (δ j) else M j i := rfl
  simp only [bucketMap, hrow]
  rw [dotBool_shift i0 (δ j) (M j) (addr hh x), dotBool_shift i0 (δ j) (M j) (addr hh x')]
  revert hdiff
  generalize addr hh x i0 = b1
  generalize addr hh x' i0 = b2
  generalize x ⟨j.val, by omega⟩ = u1
  generalize x' ⟨j.val, by omega⟩ = u2
  generalize dotBool (M j) (addr hh x) = d1
  generalize dotBool (M j) (addr hh x') = d2
  generalize δ j = dj
  cases b1 <;> cases b2 <;> cases u1 <;> cases u2 <;> cases d1 <;> cases d2 <;> cases dj <;> simp

theorem collision_card_bound {n h : ℕ} (hh : h ≤ n) {x x' : Fin n → Bool} (hne : x ≠ x') :
    ((Finset.univ : Finset (Mat h (n - h))).filter
      (fun M => bucketMap hh M x = bucketMap hh M x')).card * 2 ^ h ≤
        Fintype.card (Mat h (n - h)) := by
  by_cases ha : addr hh x = addr hh x'
  · have hemp : (Finset.univ : Finset (Mat h (n - h))).filter
        (fun M => bucketMap hh M x = bucketMap hh M x') = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro M _ hb
      exact addr_ne_of_bucket_eq hh M hne hb ha
    simp [hemp]
  · have hex : ∃ i0 : Fin (n - h), addr hh x i0 ≠ addr hh x' i0 := by
      by_contra hall
      push Not at hall
      exact ha (funext hall)
    obtain ⟨i0, hi0⟩ := hex
    let S := (Finset.univ : Finset (Mat h (n - h))).filter
      (fun M => bucketMap hh M x = bucketMap hh M x')
    let B : Finset (Fin h → Bool) := Finset.univ
    have hinj : Set.InjOn (fun p : Mat h (n - h) × (Fin h → Bool) => shiftCol i0 p.2 p.1)
        ↑(S ×ˢ B) := by
      intro p1 hp1 p2 hp2 heq
      dsimp at heq
      simp only [Finset.mem_coe, Finset.mem_product, S, B, Finset.mem_filter, Finset.mem_univ,
        true_and] at hp1 hp2
      have hδ : p1.2 = p2.2 := by
        funext j
        have h1 := bucketMap_shiftCol_xor hh i0 hi0 p1.2 p1.1 j
        have h2 := bucketMap_shiftCol_xor hh i0 hi0 p2.2 p2.1 j
        rw [heq] at h1
        rw [hp1.1] at h1
        rw [hp2.1] at h2
        simp only [Bool.xor_self, Bool.false_xor] at h1 h2
        exact h1.symm.trans h2
      have hM : p1.1 = p2.1 := by
        have h := congrArg (shiftCol i0 p1.2) heq
        rw [shiftCol_invol, hδ, shiftCol_invol] at h
        exact h
      exact Prod.ext hM hδ
    have hcard := Finset.card_le_card_of_injOn
      (fun p : Mat h (n - h) × (Fin h → Bool) => shiftCol i0 p.2 p.1)
      (fun _ _ => Finset.mem_univ _) hinj
    simpa [S, B, Finset.card_product, Fintype.card_fun, Fintype.card_bool] using hcard

end HashCollision

section VoteAnalysis

def sgn (b : Bool) : ℚ := if b then 1 else -1

theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by
  cases b <;> norm_num [sgn]

theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> norm_num [sgn]

theorem sgn_le_one (b : Bool) : sgn b ≤ 1 := by
  cases b <;> norm_num [sgn]

theorem neg_one_le_sgn (b : Bool) : -1 ≤ sgn b := by
  cases b <;> norm_num [sgn]

theorem one_add_sgn_mul (a b : Bool) :
    (1 : ℚ) + sgn a * sgn b = if a = b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [sgn]

def clip (q : ℚ) : ℚ := max (-1) (min 1 q)

theorem neg_one_le_clip (q : ℚ) : -1 ≤ clip q := le_max_left _ _

theorem clip_le_one (q : ℚ) : clip q ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

theorem clip_mono {a b : ℚ} (h : a ≤ b) : clip a ≤ clip b :=
  max_le_max_left (-1) (min_le_min_left 1 h)

theorem clip_eq_self {q : ℚ} (h1 : -1 ≤ q) (h2 : q ≤ 1) : clip q = q := by
  unfold clip
  rw [min_eq_right h2, max_eq_right h1]

theorem clip_neg (q : ℚ) : clip (-q) = -clip q := by
  by_cases h1 : q ≤ -1
  · have h2 : q ≤ 1 := by linarith
    have h3 : 1 ≤ -q := by linarith
    have hLHS : clip (-q) = 1 := by
      unfold clip
      rw [min_eq_left h3, max_eq_right (by norm_num)]
    have hRHS : clip q = -1 := by
      unfold clip
      rw [min_eq_right h2, max_eq_left h1]
    rw [hLHS, hRHS]
    norm_num
  · by_cases h2 : 1 ≤ q
    · have h3 : -q ≤ -1 := by linarith
      have h4 : -q ≤ 1 := by linarith
      have hLHS : clip (-q) = -1 := by
        unfold clip
        rw [min_eq_right h4, max_eq_left h3]
      have hRHS : clip q = 1 := by
        unfold clip
        rw [min_eq_left h2, max_eq_right (by norm_num)]
      rw [hLHS, hRHS]
    · push Not at h1 h2
      have h3 : -1 ≤ -q := by linarith
      have h4 : -q ≤ 1 := by linarith
      have hLHS : clip (-q) = -q := clip_eq_self h3 h4
      have hRHS : clip q = q := clip_eq_self (by linarith) (by linarith)
      rw [hLHS, hRHS]

theorem clip_mul_sgn (q : ℚ) (b : Bool) : clip q * sgn b = clip (q * sgn b) := by
  cases b <;> simp [sgn, clip_neg]

theorem clip_avg_ge {α z : ℚ} (h0 : 0 ≤ α) (hhalf : α ≤ 1 / 2) :
    α * (1 - 4 * z ^ 2) ≤ (clip (α + z) + clip (α - z)) / 2 := by
  by_cases hz : -1 / 2 ≤ z ∧ z ≤ 1 / 2
  · have hc1 : clip (α + z) = α + z := clip_eq_self (by linarith) (by linarith)
    have hc2 : clip (α - z) = α - z := clip_eq_self (by linarith) (by linarith)
    rw [hc1, hc2]
    have hsq : 0 ≤ z ^ 2 := sq_nonneg z
    have hmul : 0 ≤ α * (4 * z ^ 2) := mul_nonneg h0 (by linarith)
    linarith
  · have hnonneg : 0 ≤ clip (α + z) + clip (α - z) := by
      have h1 : clip z ≤ clip (α + z) := clip_mono (by linarith)
      have h2 : clip (-z) ≤ clip (α - z) := clip_mono (by linarith)
      rw [clip_neg] at h2
      linarith
    have h4z : 1 ≤ 4 * z ^ 2 := by
      rcases not_and_or.mp hz with hlt | hgt
      · push Not at hlt
        have ha : 0 < -2 * z - 1 := by linarith
        have hb : 0 < -2 * z + 1 := by linarith
        have hprod : 0 ≤ (-2 * z - 1) * (-2 * z + 1) := mul_nonneg (le_of_lt ha) (le_of_lt hb)
        have hring : (-2 * z - 1) * (-2 * z + 1) = 4 * z ^ 2 - 1 := by ring
        linarith
      · push Not at hgt
        have ha : 0 < 2 * z - 1 := by linarith
        have hb : 0 < 2 * z + 1 := by linarith
        have hprod : 0 ≤ (2 * z - 1) * (2 * z + 1) := mul_nonneg (le_of_lt ha) (le_of_lt hb)
        have hring : (2 * z - 1) * (2 * z + 1) = 4 * z ^ 2 - 1 := by ring
        linarith
    have hle : α * (1 - 4 * z ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h0 (by linarith)
    linarith

def wClip {n k : ℕ} (w : (Fin n → Bool) → Fin k → ℚ) (x : Fin n → Bool) (y : Fin k) : ℚ :=
  min (w x y) (1 / 2)

def commonDen {n k : ℕ} (w : (Fin n → Bool) → Fin k → ℚ) : ℕ :=
  ∏ x : Fin n → Bool, ∏ y : Fin k, (wClip w x y).den

theorem commonDen_pos {n k : ℕ} (w : (Fin n → Bool) → Fin k → ℚ) :
    0 < commonDen w := by
  unfold commonDen
  apply Finset.prod_pos
  intro x _
  apply Finset.prod_pos
  intro y _
  exact (wClip w x y).den_pos

theorem den_dvd_commonDen {n k : ℕ} (w : (Fin n → Bool) → Fin k → ℚ)
    (x : Fin n → Bool) (y : Fin k) :
    (wClip w x y).den ∣ commonDen w := by
  unfold commonDen
  have h1 : (wClip w x y).den ∣ ∏ y' : Fin k, (wClip w x y').den :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ y)
  have h2 : (∏ y' : Fin k, (wClip w x y').den) ∣
      ∏ x' : Fin n → Bool, ∏ y' : Fin k, (wClip w x' y').den :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ x)
  exact dvd_trans h1 h2

def wInt {n k : ℕ} (w : (Fin n → Bool) → Fin k → ℚ) (x : Fin n → Bool) (y : Fin k) : ℤ :=
  (wClip w x y).num * ((commonDen w / (wClip w x y).den : ℕ) : ℤ)

theorem wInt_cast {n k : ℕ} (w : (Fin n → Bool) → Fin k → ℚ) (x : Fin n → Bool) (y : Fin k) :
    ((wInt w x y : ℤ) : ℚ) = wClip w x y * (commonDen w : ℚ) := by
  unfold wInt
  set q := wClip w x y
  set L := commonDen w
  have hdvd : q.den ∣ L := den_dvd_commonDen w x y
  have hmul : (L : ℚ) = (q.den : ℚ) * ((L / q.den : ℕ) : ℚ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
  have hden_ne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt q.den_pos)
  rw [Int.cast_mul, Int.cast_natCast]
  rw [hmul]
  have hq : (q.num : ℚ) = q * (q.den : ℚ) := by
    calc (q.num : ℚ) = (q.num : ℚ) / (q.den : ℚ) * (q.den : ℚ) := (div_mul_cancel₀ (q.num : ℚ) hden_ne).symm
      _ = q * (q.den : ℚ) := by rw [Rat.num_div_den]
  rw [hq]
  ring

theorem sum_sgn_threshold (L m : ℕ) (hm : m ≤ 2 * L) (r : Bool) :
    ∑ τ : Fin (2 * L), sgn (if τ.val < m then r else !r) =
      (2 * (m : ℚ) - (2 * L : ℚ)) * sgn r := by
  have hsplit : ∑ τ : Fin (2 * L), sgn (if τ.val < m then r else !r) =
      ∑ τ : Fin (2 * L), (if τ.val < m then sgn r else -sgn r) := by
    apply Finset.sum_congr rfl
    intro τ _
    split_ifs <;> simp [sgn_not]
  rw [hsplit, Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard1 : ((Finset.univ : Finset (Fin (2 * L))).filter (fun τ => τ.val < m)).card = m := by
    have hbij : ((Finset.univ : Finset (Fin (2 * L))).filter (fun τ => τ.val < m)).card =
        (Finset.univ : Finset (Fin m)).card := by
      refine Finset.card_bij (fun τ hτ => ⟨τ.val, (Finset.mem_filter.mp hτ).2⟩) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ h; ext; injection h
      · intro j _; exact ⟨⟨j.val, lt_of_lt_of_le j.isLt hm⟩, by simp, rfl⟩
    simpa using hbij
  have hcard2 : ((Finset.univ : Finset (Fin (2 * L))).filter (fun τ => ¬ τ.val < m)).card =
      2 * L - m := by
    have hbij : ((Finset.univ : Finset (Fin (2 * L))).filter (fun τ => ¬ τ.val < m)).card =
        (Finset.univ : Finset (Fin (2 * L - m))).card := by
      refine Finset.card_bij (fun τ hτ => ⟨τ.val - m, by have := τ.isLt; have := (Finset.mem_filter.mp hτ).2; omega⟩) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a ha b hb h
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        have hv : a.val - m = b.val - m := congrArg Fin.val h
        apply Fin.ext; omega
      · intro j _
        refine ⟨⟨m + j.val, by have := j.isLt; omega⟩, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩
        · apply Fin.ext; change m + j.val - m = j.val; omega
    simpa using hbij
  rw [hcard1, hcard2]
  have hsub : ((2 * L - m : ℕ) : ℚ) = (2 * L : ℚ) - (m : ℚ) := by
    rw [Nat.cast_sub hm]
    push_cast
    rfl
  rw [hsub]
  ring

def flipAt {t : ℕ} (a0 : Fin t → Bool) (σ : (Fin t → Bool) → Bool) : (Fin t → Bool) → Bool :=
  fun a => if a = a0 then !σ a else σ a

theorem flipAt_invol {t : ℕ} (a0 : Fin t → Bool) (σ : (Fin t → Bool) → Bool) :
    flipAt a0 (flipAt a0 σ) = σ := by
  funext a
  simp only [flipAt]
  split_ifs
  · exact Bool.not_not _
  · rfl

theorem flipAt_self {t : ℕ} (a0 : Fin t → Bool) (σ : (Fin t → Bool) → Bool) :
    flipAt a0 σ a0 = !σ a0 := by
  simp [flipAt]

theorem flipAt_ne {t : ℕ} {a0 a : Fin t → Bool} (h : a ≠ a0) (σ : (Fin t → Bool) → Bool) :
    flipAt a0 σ a = σ a := by
  simp [flipAt, h]

theorem sum_flipAt {t : ℕ} (a0 : Fin t → Bool) (f : ((Fin t → Bool) → Bool) → ℚ) :
    ∑ σ : (Fin t → Bool) → Bool, f (flipAt a0 σ) = ∑ σ : (Fin t → Bool) → Bool, f σ := by
  refine Fintype.sum_equiv (Equiv.ofBijective (flipAt a0) ?_) _ _ (fun _ => rfl)
  refine ⟨fun s1 s2 h => ?_, fun s => ⟨flipAt a0 s, flipAt_invol a0 s⟩⟩
  have := congrArg (flipAt a0) h
  simpa [flipAt_invol] using this

theorem sum_sgn_pair_zero {t : ℕ} {a1 a2 : Fin t → Bool} (hne : a1 ≠ a2) :
    ∑ σ : (Fin t → Bool) → Bool, sgn (σ a1) * sgn (σ a2) = 0 := by
  have h1 : ∑ σ : (Fin t → Bool) → Bool, sgn (σ a1) * sgn (σ a2) =
      ∑ σ : (Fin t → Bool) → Bool, sgn (flipAt a1 σ a1) * sgn (flipAt a1 σ a2) :=
    (sum_flipAt a1 (fun σ => sgn (σ a1) * sgn (σ a2))).symm
  have h2 : ∑ σ : (Fin t → Bool) → Bool, sgn (flipAt a1 σ a1) * sgn (flipAt a1 σ a2) =
      -(∑ σ : (Fin t → Bool) → Bool, sgn (σ a1) * sgn (σ a2)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    rw [flipAt_self, flipAt_ne (Ne.symm hne), sgn_not]
    ring
  linarith

end VoteAnalysis

section MainConstruction

theorem main_proof (n h k : ℕ) (hh : h ≤ n)
    (truth : (Fin n → Bool) → Fin k → Bool)
    (w : (Fin n → Bool) → Fin k → ℚ)
    (D : Fin k → Finset (Fin n → Bool))
    (hw0 : ∀ x y, 0 ≤ w x y)
    (hw2 : ∀ y, 16 * (∑ x : Fin n → Bool, (w x y) ^ 2) ≤ (2 ^ h : ℚ)) :
    ∃ (z : ℕ) (C : Fin z → Circuit) (tap : Fin z → Fin (h + 1) → ℕ)
      (read : Fin z → (Fin (h + 1) → Bool) → Fin k → Bool),
      0 < z ∧
      (∀ s, Legal n (C s).gates ∧ costList (C s).gates ≤ 3 * 2 ^ ((n - h + 1) / 2) ∧
        ∀ j, tap s j < n + (C s).gates.length) ∧
      ∀ x y,
        let reward : ℚ := if x ∈ D y then 1 else (3 / 4 : ℚ) * min (w x y) (1 / 2)
        let hits := ((Finset.univ : Finset (Fin z)).filter (fun s =>
          read s (fun j => ((C s).wires (List.ofFn x)).getD (tap s j) false) y = truth x y)).card
        (1 + reward - 2 * ((D y).card : ℚ) / (2 ^ h : ℚ)) * (z : ℚ) ≤ 2 * (hits : ℚ) := by
  let t := n - h
  let Hnat : ℕ := 2 ^ h
  let H : ℚ := (2 ^ h : ℚ)
  have hHpos : (0 : ℚ) < H := by positivity
  let L : ℕ := commonDen w
  have hLpos : 0 < L := commonDen_pos w
  have hL2pos : 0 < 2 * L := by omega
  let : NeZero (2 * L) := ⟨Nat.ne_of_gt hL2pos⟩
  let Ω := Mat h t × ((Fin t → Bool) → Bool) × Fin (2 * L)
  let e : Ω ≃ Fin (Fintype.card Ω) := Fintype.equivFin Ω
  let z := Fintype.card Ω
  have hzpos : 0 < z := Fintype.card_pos
  have hz_eq : (z : ℚ) = (Fintype.card (Mat h t) : ℚ) *
      (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ) := by
    have hnat : z = Fintype.card (Mat h t) * Fintype.card ((Fin t → Bool) → Bool) * (2 * L) := by
      simp [z, Ω, Fintype.card_prod, Nat.mul_assoc]
    exact_mod_cast hnat
  let voteInt : Mat h t → ((Fin t → Bool) → Bool) → (Fin h → Bool) → Fin k → ℤ :=
    fun M σ b y =>
      ∑ x' ∈ (Finset.univ : Finset (Fin n → Bool)).filter (fun x' => bucketMap hh M x' = b),
        wInt w x' y * (if truth x' y then 1 else -1) * (if σ (addr hh x') then 1 else -1)
  let voteRat : Mat h t → ((Fin t → Bool) → Bool) → (Fin h → Bool) → Fin k → ℚ :=
    fun M σ b y =>
      ∑ x' ∈ (Finset.univ : Finset (Fin n → Bool)).filter (fun x' => bucketMap hh M x' = b),
        wClip w x' y * sgn (truth x' y) * sgn (σ (addr hh x'))
  have hvote_cast : ∀ M σ b y, ((voteInt M σ b y : ℤ) : ℚ) = voteRat M σ b y * (L : ℚ) := by
    intro M σ b y
    simp only [voteInt, voteRat, Int.cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x' _
    rw [Int.cast_mul, Int.cast_mul, wInt_cast]
    have hs1 : ((if truth x' y then (1 : ℤ) else -1 : ℤ) : ℚ) = sgn (truth x' y) := by
      cases truth x' y <;> simp [sgn]
    have hs2 : ((if σ (addr hh x') then (1 : ℤ) else -1 : ℤ) : ℚ) = sgn (σ (addr hh x')) := by
      cases σ (addr hh x') <;> simp [sgn]
    have hL : (commonDen w : ℚ) = (L : ℚ) := rfl
    rw [hs1, hs2, hL]
    ring
  let clipInt : Mat h t → ((Fin t → Bool) → Bool) → (Fin h → Bool) → Fin k → ℤ :=
    fun M σ b y => max (-(L : ℤ)) (min (L : ℤ) (voteInt M σ b y))
  let thresh : Mat h t → ((Fin t → Bool) → Bool) → (Fin h → Bool) → Fin k → ℕ :=
    fun M σ b y => (clipInt M σ b y + (L : ℤ)).toNat
  have hthresh_le : ∀ M σ b y, thresh M σ b y ≤ 2 * L := by
    intro M σ b y
    have hle : clipInt M σ b y ≤ (L : ℤ) := max_le (by omega) (min_le_left _ _)
    have hge : -(L : ℤ) ≤ clipInt M σ b y := le_max_left _ _
    simp only [thresh]
    omega
  have hthresh_cast : ∀ M σ b y,
      ((thresh M σ b y : ℕ) : ℚ) = (1 + clip (voteRat M σ b y)) * (L : ℚ) := by
    intro M σ b y
    have hge : -(L : ℤ) ≤ clipInt M σ b y := le_max_left _ _
    have hto : ((thresh M σ b y : ℕ) : ℤ) = clipInt M σ b y + (L : ℤ) :=
      Int.toNat_of_nonneg (by omega)
    have hq : ((thresh M σ b y : ℕ) : ℚ) = ((clipInt M σ b y : ℤ) : ℚ) + (L : ℚ) := by
      exact_mod_cast hto
    rw [hq]
    have hclip_cast : ((clipInt M σ b y : ℤ) : ℚ) = clip (voteRat M σ b y) * (L : ℚ) := by
      have hLq : (0 : ℚ) < (L : ℚ) := by exact_mod_cast hLpos
      simp only [clipInt, clip]
      rw [Int.cast_max, Int.cast_min, Int.cast_neg, Int.cast_natCast, hvote_cast]
      rw [max_mul_of_nonneg _ _ (le_of_lt hLq), min_mul_of_nonneg _ _ (le_of_lt hLq)]
      simp
    rw [hclip_cast]
    ring
  let readΩ : Ω → (Fin (h + 1) → Bool) → Fin k → Bool :=
    fun ω bits y =>
      let M := ω.1
      let σ := ω.2.1
      let τ := ω.2.2
      let b : Fin h → Bool := fun j => bits ⟨j.val, by omega⟩
      let r : Bool := bits ⟨h, by omega⟩
      let ov := (Finset.univ : Finset (Fin n → Bool)).filter (fun x' => bucketMap hh M x' = b ∧ x' ∈ D y)
      if hov : ov.Nonempty then
        truth (Classical.choose hov) y
      else
        if τ.val < thresh M σ b y then r else !r
  let C : Fin z → Circuit := fun s => (buildCircuitData hh (e.symm s).1 (e.symm s).2.1).1
  let tap : Fin z → Fin (h + 1) → ℕ := fun s => (buildCircuitData hh (e.symm s).1 (e.symm s).2.1).2
  let read : Fin z → (Fin (h + 1) → Bool) → Fin k → Bool := fun s => readΩ (e.symm s)
  refine ⟨z, C, tap, read, hzpos, ?_, ?_⟩
  · intro s
    have hspec := buildCircuitData_spec hh (e.symm s).1 (e.symm s).2.1
    exact ⟨hspec.1, hspec.2.1, hspec.2.2.1⟩
  · intro x y
    dsimp only
    let predΩ : Ω → Bool := fun ω =>
      readΩ ω (fun j => ((buildCircuitData hh ω.1 ω.2.1).1.wires (List.ofFn x)).getD
        ((buildCircuitData hh ω.1 ω.2.1).2 j) false) y
    have hhits_eq : ((Finset.univ : Finset (Fin z)).filter (fun s =>
          read s (fun j => ((C s).wires (List.ofFn x)).getD (tap s j) false) y = truth x y)).card =
        ((Finset.univ : Finset Ω).filter (fun ω => predΩ ω = truth x y)).card := by
      refine Finset.card_bij (fun s _ => e.symm s) ?_ ?_ ?_
      · intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
        exact hs
      · intro s1 _ s2 _ h
        exact e.symm.injective h
      · intro ω hω
        refine ⟨e ω, ?_, e.symm_apply_apply ω⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
        dsimp only [read, C, tap, predΩ] at *
        rw [e.symm_apply_apply]
        exact hω
    have hpred_eval : ∀ ω : Ω,
        predΩ ω =
          let M := ω.1; let σ := ω.2.1; let τ := ω.2.2
          let ov := (Finset.univ : Finset (Fin n → Bool)).filter
            (fun x' => bucketMap hh M x' = bucketMap hh M x ∧ x' ∈ D y)
          if hov : ov.Nonempty then truth (Classical.choose hov) y
          else if τ.val < thresh M σ (bucketMap hh M x) y then σ (addr hh x) else !(σ (addr hh x)) := by
      intro ω
      have hspec := buildCircuitData_spec hh ω.1 ω.2.1
      simp only [predΩ, readΩ]
      have hb : (fun j : Fin h => ((buildCircuitData hh ω.1 ω.2.1).1.wires (List.ofFn x)).getD
          ((buildCircuitData hh ω.1 ω.2.1).2 ⟨j.val, by omega⟩) false) = bucketMap hh ω.1 x := by
        funext j
        exact hspec.2.2.2.1 x j
      have hr : ((buildCircuitData hh ω.1 ω.2.1).1.wires (List.ofFn x)).getD
          ((buildCircuitData hh ω.1 ω.2.1).2 ⟨h, by omega⟩) false = ω.2.1 (addr hh x) :=
        hspec.2.2.2.2 x
      simp only [hb, hr]
    have htwo_hits : 2 * (((Finset.univ : Finset Ω).filter (fun ω => predΩ ω = truth x y)).card : ℚ) =
        (z : ℚ) + ∑ ω : Ω, sgn (predΩ ω) * sgn (truth x y) := by
      have hsum : ∑ ω : Ω, ((1 : ℚ) + sgn (predΩ ω) * sgn (truth x y)) =
          2 * (((Finset.univ : Finset Ω).filter (fun ω => predΩ ω = truth x y)).card : ℚ) := by
        have hrew : ∑ ω : Ω, ((1 : ℚ) + sgn (predΩ ω) * sgn (truth x y)) =
            ∑ ω : Ω, (if predΩ ω = truth x y then (2 : ℚ) else 0) := by
          apply Finset.sum_congr rfl
          intro ω _
          exact one_add_sgn_mul (predΩ ω) (truth x y)
        rw [hrew, Finset.sum_ite]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_zero, add_zero]
        ring
      rw [← hsum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [hhits_eq, htwo_hits]
    -- Collision count against D y \ {x}
    let badM : Finset (Mat h t) := (Finset.univ : Finset (Mat h t)).filter
      (fun M => ∃ x' ∈ D y, x' ≠ x ∧ bucketMap hh M x' = bucketMap hh M x)
    have hbadM_card : (badM.card : ℚ) ≤ ((D y).card : ℚ) * (Fintype.card (Mat h t) : ℚ) / (H : ℚ) := by
      have hsub : badM ⊆ (D y).biUnion (fun x' =>
          if x' = x then ∅
          else (Finset.univ : Finset (Mat h t)).filter (fun M => bucketMap hh M x' = bucketMap hh M x)) := by
        intro M hM
        simp only [badM, Finset.mem_filter, Finset.mem_univ, true_and] at hM
        rcases hM with ⟨x', hx'D, hx'ne, hbeq⟩
        rw [Finset.mem_biUnion]
        exact ⟨x', hx'D, by simp [hx'ne, hbeq]⟩
      have hnat : badM.card * Hnat ≤ (D y).card * Fintype.card (Mat h t) := by
        calc badM.card * Hnat
            ≤ ((D y).biUnion (fun x' =>
                if x' = x then ∅
                else (Finset.univ : Finset (Mat h t)).filter (fun M => bucketMap hh M x' = bucketMap hh M x))).card * Hnat :=
              Nat.mul_le_mul_right Hnat (Finset.card_le_card hsub)
          _ ≤ (∑ x' ∈ D y, (if x' = x then (∅ : Finset (Mat h t))
                else (Finset.univ : Finset (Mat h t)).filter (fun M => bucketMap hh M x' = bucketMap hh M x)).card) * Hnat :=
              Nat.mul_le_mul_right Hnat Finset.card_biUnion_le
          _ = ∑ x' ∈ D y, (if x' = x then (∅ : Finset (Mat h t))
                else (Finset.univ : Finset (Mat h t)).filter (fun M => bucketMap hh M x' = bucketMap hh M x)).card * Hnat :=
              Finset.sum_mul _ _ _
          _ ≤ ∑ _x' ∈ D y, Fintype.card (Mat h t) := by
              apply Finset.sum_le_sum
              intro x' _
              split_ifs with heq
              · simp
              · exact collision_card_bound hh heq
          _ = (D y).card * Fintype.card (Mat h t) := by simp
      have hq : (badM.card : ℚ) * H ≤ ((D y).card : ℚ) * (Fintype.card (Mat h t) : ℚ) := by
        have hq0 : ((badM.card * Hnat : ℕ) : ℚ) ≤ (((D y).card * Fintype.card (Mat h t) : ℕ) : ℚ) := by
          exact_mod_cast hnat
        rw [Nat.cast_mul, Nat.cast_mul] at hq0
        have hHeq : (Hnat : ℚ) = H := by simp [Hnat, H]
        rw [hHeq] at hq0
        exact hq0
      exact (le_div_iff₀ hHpos).mpr hq
    have hbad_sum : ∑ ω : Ω, (if ω.1 ∈ badM then (2 : ℚ) else 0) =
        2 * (badM.card : ℚ) * (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ) := by
      calc ∑ ω : Ω, (if ω.1 ∈ badM then (2 : ℚ) else 0)
          = ∑ M : Mat h t, ∑ _bc : ((Fin t → Bool) → Bool) × Fin (2 * L),
              (if M ∈ badM then (2 : ℚ) else 0) := by
            rw [Fintype.sum_prod_type]
        _ = ∑ M : Mat h t,
              ((Fintype.card (((Fin t → Bool) → Bool) × Fin (2 * L)) : ℕ) : ℚ) *
                (if M ∈ badM then (2 : ℚ) else 0) := by
            refine Finset.sum_congr rfl fun M _ => ?_
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = ((Fintype.card (((Fin t → Bool) → Bool) × Fin (2 * L)) : ℕ) : ℚ) *
              ∑ M : Mat h t, (if M ∈ badM then (2 : ℚ) else 0) := by
            rw [← Finset.mul_sum]
        _ = ((Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ)) *
              ((badM.card : ℚ) * 2) := by
            rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
            congr 1
            simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        _ = 2 * (badM.card : ℚ) * (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ) := by
            ring
    -- Now split into x ∈ D y vs x ∉ D y
    by_cases hxD : x ∈ D y
    · simp only [hxD, ↓reduceIte]
      have hsum_ge : (1 - 2 * ((D y).card : ℚ) / (H : ℚ)) * (z : ℚ) ≤
          ∑ ω : Ω, sgn (predΩ ω) * sgn (truth x y) := by
        have hstep : ∑ ω : Ω, (if ω.1 ∈ badM then (-1 : ℚ) else 1) ≤
            ∑ ω : Ω, sgn (predΩ ω) * sgn (truth x y) := by
          apply Finset.sum_le_sum
          intro ω _
          split_ifs with hbad
          · have h1 : -1 ≤ sgn (predΩ ω) * sgn (truth x y) := by
              cases predΩ ω <;> cases truth x y <;> norm_num [sgn]
            exact h1
          · rw [hpred_eval ω]
            let ov := (Finset.univ : Finset (Fin n → Bool)).filter
              (fun x' => bucketMap hh ω.1 x' = bucketMap hh ω.1 x ∧ x' ∈ D y)
            have hov : ov.Nonempty := ⟨x, by simp [ov, hxD]⟩
            simp only [ov, hov, ↓reduceDIte]
            have hmem := Classical.choose_spec hov
            dsimp only [ov] at hmem
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
            have hch : Classical.choose hov = x := by
              by_contra hne
              apply hbad
              simp only [badM, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨Classical.choose hov, hmem.2, hne, hmem.1⟩
            rw [hch, sgn_mul_self]
        have heval_lhs : ∑ ω : Ω, (if ω.1 ∈ badM then (-1 : ℚ) else 1) =
            (z : ℚ) - 2 * (badM.card : ℚ) * (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ) := by
          have hrew : ∀ ω : Ω, (if ω.1 ∈ badM then (-1 : ℚ) else 1) =
              1 - (if ω.1 ∈ badM then (2 : ℚ) else 0) := by
            intro ω; split_ifs <;> norm_num
          simp_rw [hrew, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
          congr 1
        rw [heval_lhs] at hstep
        have hbad_z : (badM.card : ℚ) * (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ) ≤
            ((D y).card : ℚ) / (H : ℚ) * (z : ℚ) := by
          rw [hz_eq]
          have hnonneg : 0 ≤ (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ) := by
            positivity
          calc (badM.card : ℚ) * (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ)
              = (badM.card : ℚ) * ((Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ)) := by ring
            _ ≤ (((D y).card : ℚ) * (Fintype.card (Mat h t) : ℚ) / (H : ℚ)) *
                  ((Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ)) :=
                mul_le_mul_of_nonneg_right hbadM_card hnonneg
            _ = ((D y).card : ℚ) / (H : ℚ) *
                  ((Fintype.card (Mat h t) : ℚ) * (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ)) := by
                ring
        have hd : (1 - 2 * ((D y).card : ℚ) / H) * (z : ℚ) =
            (z : ℚ) - 2 * (((D y).card : ℚ) / H * (z : ℚ)) := by ring
        rw [hd]
        linarith
      have hH : H = (2 ^ h : ℚ) := rfl
      rw [← hH]
      have hd : (1 + 1 - 2 * ((D y).card : ℚ) / H) * (z : ℚ) =
          (z : ℚ) + (1 - 2 * ((D y).card : ℚ) / H) * (z : ℚ) := by ring
      rw [hd]
      linarith
    · simp only [hxD, ↓reduceIte]
      let votePred : Ω → Bool := fun ω =>
        if ω.2.2.val < thresh ω.1 ω.2.1 (bucketMap hh ω.1 x) y then ω.2.1 (addr hh x) else !(ω.2.1 (addr hh x))
      have hoverride_loss :
          (∑ ω : Ω, sgn (votePred ω) * sgn (truth x y)) -
            2 * (badM.card : ℚ) * (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ) ≤
          ∑ ω : Ω, sgn (predΩ ω) * sgn (truth x y) := by
        have hpt : ∑ ω : Ω, (sgn (votePred ω) * sgn (truth x y) - (if ω.1 ∈ badM then (2 : ℚ) else 0)) ≤
            ∑ ω : Ω, sgn (predΩ ω) * sgn (truth x y) := by
          apply Finset.sum_le_sum
          intro ω _
          split_ifs with hbad
          · have h1 : -1 ≤ sgn (predΩ ω) * sgn (truth x y) := by
              cases predΩ ω <;> cases truth x y <;> norm_num [sgn]
            have h2 : sgn (votePred ω) * sgn (truth x y) ≤ 1 := by
              cases votePred ω <;> cases truth x y <;> norm_num [sgn]
            linarith
          · rw [hpred_eval ω]
            let ov := (Finset.univ : Finset (Fin n → Bool)).filter
              (fun x' => bucketMap hh ω.1 x' = bucketMap hh ω.1 x ∧ x' ∈ D y)
            have hnotov : ¬ ov.Nonempty := by
              intro ⟨x', hx'⟩
              simp only [ov, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
              have hne : x' ≠ x := fun heq => hxD (heq ▸ hx'.2)
              apply hbad
              simp only [badM, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨x', hx'.2, hne, hx'.1⟩
            simp only [ov, hnotov, ↓reduceDIte, sub_zero, votePred]
            rfl
        rw [Finset.sum_sub_distrib, hbad_sum] at hpt
        exact hpt
      -- Evaluate sum of votePred over Ω
      let α : ℚ := wClip w x y
      have hα0 : 0 ≤ α := le_min (hw0 x y) (by norm_num)
      have hαhalf : α ≤ 1 / 2 := min_le_right _ _
      let Z : Mat h t → ((Fin t → Bool) → Bool) → ℚ := fun M σ =>
        sgn (truth x y) * sgn (σ (addr hh x)) *
          ∑ x' ∈ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x' => bucketMap hh M x' = bucketMap hh M x)).erase x,
            wClip w x' y * sgn (truth x' y) * sgn (σ (addr hh x'))
      have hvote_tau : ∑ ω : Ω, sgn (votePred ω) * sgn (truth x y) =
          ((2 * L : ℕ) : ℚ) * ∑ M : Mat h t, ∑ σ : (Fin t → Bool) → Bool, clip (α + Z M σ) := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type]
        dsimp only [votePred]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro M _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro σ _
        rw [← Finset.sum_mul, sum_sgn_threshold L _ (hthresh_le M σ (bucketMap hh M x) y),
          hthresh_cast]
        have hmul : (2 * ((1 + clip (voteRat M σ (bucketMap hh M x) y)) * (L : ℚ)) - (2 * (L : ℚ))) *
            sgn (σ (addr hh x)) * sgn (truth x y) =
            ((2 * L : ℕ) : ℚ) * (clip (voteRat M σ (bucketMap hh M x) y) *
              sgn (σ (addr hh x)) * sgn (truth x y)) := by
          push_cast; ring
        rw [hmul]
        congr 1
        rw [clip_mul_sgn, clip_mul_sgn]
        congr 1
        let B := (Finset.univ : Finset (Fin n → Bool)).filter (fun x' => bucketMap hh M x' = bucketMap hh M x)
        have hxB : x ∈ B := by simp [B]
        have hsplit : voteRat M σ (bucketMap hh M x) y =
            wClip w x y * sgn (truth x y) * sgn (σ (addr hh x)) +
              ∑ x' ∈ B.erase x, wClip w x' y * sgn (truth x' y) * sgn (σ (addr hh x')) :=
          (Finset.add_sum_erase B (fun x' => wClip w x' y * sgn (truth x' y) * sgn (σ (addr hh x'))) hxB).symm
        rw [hsplit]
        have hs1 := sgn_mul_self (truth x y)
        have hs2 := sgn_mul_self (σ (addr hh x))
        simp only [α, Z, B]
        calc (wClip w x y * sgn (truth x y) * sgn (σ (addr hh x)) +
                ∑ x' ∈ B.erase x, wClip w x' y * sgn (truth x' y) * sgn (σ (addr hh x'))) *
                sgn (σ (addr hh x)) * sgn (truth x y)
            = wClip w x y * (sgn (truth x y) * sgn (truth x y)) * (sgn (σ (addr hh x)) * sgn (σ (addr hh x))) +
                sgn (truth x y) * sgn (σ (addr hh x)) *
                ∑ x' ∈ B.erase x, wClip w x' y * sgn (truth x' y) * sgn (σ (addr hh x')) := by ring
          _ = wClip w x y + sgn (truth x y) * sgn (σ (addr hh x)) *
                ∑ x' ∈ B.erase x, wClip w x' y * sgn (truth x' y) * sgn (σ (addr hh x')) := by
              rw [hs1, hs2]; ring
      -- Symmetry of Z under flipAt (addr hh x)
      have hZ_flip : ∀ M σ, Z M (flipAt (addr hh x) σ) = -Z M σ := by
        intro M σ
        simp only [Z]
        rw [flipAt_self, sgn_not]
        have hsum_eq : ∑ x' ∈ ((Finset.univ : Finset (Fin n → Bool)).filter
              (fun x' => bucketMap hh M x' = bucketMap hh M x)).erase x,
              wClip w x' y * sgn (truth x' y) * sgn (flipAt (addr hh x) σ (addr hh x')) =
            ∑ x' ∈ ((Finset.univ : Finset (Fin n → Bool)).filter
              (fun x' => bucketMap hh M x' = bucketMap hh M x)).erase x,
              wClip w x' y * sgn (truth x' y) * sgn (σ (addr hh x')) := by
          apply Finset.sum_congr rfl
          intro x' hx'
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
          have hane : addr hh x' ≠ addr hh x := addr_ne_of_bucket_eq hh M hx'.1 hx'.2
          rw [flipAt_ne hane]
        rw [hsum_eq]
        ring
      -- Second moment of Z for fixed M
      have hZ_sq : ∀ M, ∑ σ : (Fin t → Bool) → Bool, (Z M σ) ^ 2 =
          (Fintype.card ((Fin t → Bool) → Bool) : ℚ) *
            ∑ x' ∈ ((Finset.univ : Finset (Fin n → Bool)).filter
              (fun x' => bucketMap hh M x' = bucketMap hh M x)).erase x, (wClip w x' y) ^ 2 := by
        intro M
        let S := ((Finset.univ : Finset (Fin n → Bool)).filter
          (fun x' => bucketMap hh M x' = bucketMap hh M x)).erase x
        have hsq_pt : ∀ σ, (Z M σ) ^ 2 =
            ∑ x1 ∈ S, ∑ x2 ∈ S,
              (wClip w x1 y * sgn (truth x1 y)) * (wClip w x2 y * sgn (truth x2 y)) *
                (sgn (σ (addr hh x1)) * sgn (σ (addr hh x2))) := by
          intro σ
          have h1 : (Z M σ) ^ 2 =
              (∑ x' ∈ S, wClip w x' y * sgn (truth x' y) * sgn (σ (addr hh x'))) ^ 2 := by
            simp only [Z, S]
            have hs1 := sgn_mul_self (truth x y)
            have hs2 := sgn_mul_self (σ (addr hh x))
            calc (sgn (truth x y) * sgn (σ (addr hh x)) *
                    ∑ x' ∈ S, wClip w x' y * sgn (truth x' y) * sgn (σ (addr hh x'))) ^ 2
                = (sgn (truth x y) * sgn (truth x y)) * (sgn (σ (addr hh x)) * sgn (σ (addr hh x))) *
                    (∑ x' ∈ S, wClip w x' y * sgn (truth x' y) * sgn (σ (addr hh x'))) ^ 2 := by ring
              _ = _ := by rw [hs1, hs2]; ring
          rw [h1, sq, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl
          intro x1 _
          apply Finset.sum_congr rfl
          intro x2 _
          ring
        simp_rw [hsq_pt]
        rw [Finset.sum_comm]
        trans ∑ x1 ∈ S, ∑ x2 ∈ S,
            (wClip w x1 y * sgn (truth x1 y)) * (wClip w x2 y * sgn (truth x2 y)) *
              (∑ σ : (Fin t → Bool) → Bool, sgn (σ (addr hh x1)) * sgn (σ (addr hh x2)))
        · apply Finset.sum_congr rfl
          intro x1 _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x2 _
          rw [Finset.mul_sum]
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x1 hx1
          have hinner : ∑ x2 ∈ S,
              (wClip w x1 y * sgn (truth x1 y)) * (wClip w x2 y * sgn (truth x2 y)) *
                (∑ σ : (Fin t → Bool) → Bool, sgn (σ (addr hh x1)) * sgn (σ (addr hh x2))) =
              (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * (wClip w x1 y) ^ 2 := by
            rw [Finset.sum_eq_single x1]
            · have hs1 := sgn_mul_self (truth x1 y)
              have hsig : ∑ σ : (Fin t → Bool) → Bool, sgn (σ (addr hh x1)) * sgn (σ (addr hh x1)) =
                  (Fintype.card ((Fin t → Bool) → Bool) : ℚ) := by
                simp [sgn_mul_self]
              rw [hsig]
              calc (wClip w x1 y * sgn (truth x1 y)) * (wClip w x1 y * sgn (truth x1 y)) *
                      (Fintype.card ((Fin t → Bool) → Bool) : ℚ)
                  = (wClip w x1 y) ^ 2 * (sgn (truth x1 y) * sgn (truth x1 y)) *
                      (Fintype.card ((Fin t → Bool) → Bool) : ℚ) := by ring
                _ = (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * (wClip w x1 y) ^ 2 := by
                    rw [hs1]; ring
            · intro x2 hx2 hne
              simp only [S, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
              have hb12 : bucketMap hh M x1 = bucketMap hh M x2 := hx1.2.trans hx2.2.symm
              have hane : addr hh x1 ≠ addr hh x2 := addr_ne_of_bucket_eq hh M (Ne.symm hne) hb12
              rw [sum_sgn_pair_zero hane, mul_zero]
            · intro hnot; exact absurd hx1 hnot
          exact hinner
      -- Sum of Z^2 over M and σ
      have hZ_sq_tot : ∑ M : Mat h t, ∑ σ : (Fin t → Bool) → Bool, (Z M σ) ^ 2 ≤
          (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * (Fintype.card (Mat h t) : ℚ) / 16 := by
        simp_rw [hZ_sq, ← Finset.mul_sum]
        have hswap : ∑ M : Mat h t,
            ∑ x' ∈ ((Finset.univ : Finset (Fin n → Bool)).filter
              (fun x' => bucketMap hh M x' = bucketMap hh M x)).erase x, (wClip w x' y) ^ 2 =
            ∑ x' ∈ (Finset.univ : Finset (Fin n → Bool)).erase x,
              (wClip w x' y) ^ 2 *
                (((Finset.univ : Finset (Mat h t)).filter
                  (fun M => bucketMap hh M x' = bucketMap hh M x)).card : ℚ) := by
          have h1 : ∀ M : Mat h t,
              ∑ x' ∈ ((Finset.univ : Finset (Fin n → Bool)).filter
                (fun x' => bucketMap hh M x' = bucketMap hh M x)).erase x, (wClip w x' y) ^ 2 =
              ∑ x' ∈ (Finset.univ : Finset (Fin n → Bool)).erase x,
                if bucketMap hh M x' = bucketMap hh M x then (wClip w x' y) ^ 2 else 0 := by
            intro M
            rw [← Finset.sum_filter]
            congr 1
            ext x'
            simp [and_comm]
          simp_rw [h1]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x' _
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
        rw [hswap]
        have hinner_le : ∑ x' ∈ (Finset.univ : Finset (Fin n → Bool)).erase x,
            (wClip w x' y) ^ 2 *
              (((Finset.univ : Finset (Mat h t)).filter
                (fun M => bucketMap hh M x' = bucketMap hh M x)).card : ℚ) ≤
            (Fintype.card (Mat h t) : ℚ) / 16 := by
          have h1 : ∑ x' ∈ (Finset.univ : Finset (Fin n → Bool)).erase x,
              (wClip w x' y) ^ 2 *
                (((Finset.univ : Finset (Mat h t)).filter
                  (fun M => bucketMap hh M x' = bucketMap hh M x)).card : ℚ) ≤
              ∑ x' ∈ (Finset.univ : Finset (Fin n → Bool)).erase x,
                (w x' y) ^ 2 * ((Fintype.card (Mat h t) : ℚ) / (H : ℚ)) := by
            apply Finset.sum_le_sum
            intro x' hx'
            have hne : x' ≠ x := (Finset.mem_erase.mp hx').1
            have hcol : (((Finset.univ : Finset (Mat h t)).filter
                (fun M => bucketMap hh M x' = bucketMap hh M x)).card : ℚ) ≤
                (Fintype.card (Mat h t) : ℚ) / (H : ℚ) := by
              rw [le_div_iff₀ hHpos]
              have hc := collision_card_bound hh hne
              have hcq : ((((Finset.univ : Finset (Mat h t)).filter
                  (fun M => bucketMap hh M x' = bucketMap hh M x)).card * 2 ^ h : ℕ) : ℚ) ≤
                  ((Fintype.card (Mat h (n - h)) : ℕ) : ℚ) := by exact_mod_cast hc
              push_cast at hcq
              exact hcq
            have hw_le : (wClip w x' y) ^ 2 ≤ (w x' y) ^ 2 := by
              have hle : wClip w x' y ≤ w x' y := min_le_left _ _
              have h0 : 0 ≤ wClip w x' y := le_min (hw0 x' y) (by norm_num)
              nlinarith
            exact mul_le_mul hw_le hcol (Nat.cast_nonneg _) (sq_nonneg _)
          have h2 : ∑ x' ∈ (Finset.univ : Finset (Fin n → Bool)).erase x, (w x' y) ^ 2 ≤
              ∑ x' : Fin n → Bool, (w x' y) ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg (fun x' => sq_nonneg _)
          rw [← Finset.sum_mul] at h1
          have h3 : (∑ x' : Fin n → Bool, (w x' y) ^ 2) * ((Fintype.card (Mat h t) : ℚ) / (H : ℚ)) ≤
              (Fintype.card (Mat h t) : ℚ) / 16 := by
            have hdiv : ∑ x' : Fin n → Bool, (w x' y) ^ 2 ≤ (H : ℚ) / 16 := by linarith [hw2 y]
            have hMnonneg : (0 : ℚ) ≤ (Fintype.card (Mat h t) : ℚ) / (H : ℚ) := by positivity
            calc (∑ x' : Fin n → Bool, (w x' y) ^ 2) * ((Fintype.card (Mat h t) : ℚ) / (H : ℚ))
                ≤ ((H : ℚ) / 16) * ((Fintype.card (Mat h t) : ℚ) / (H : ℚ)) :=
                  mul_le_mul_of_nonneg_right hdiv hMnonneg
              _ = (Fintype.card (Mat h t) : ℚ) / 16 := by
                  field_simp [ne_of_gt hHpos]
          have hMnonneg : (0 : ℚ) ≤ (Fintype.card (Mat h t) : ℚ) / (H : ℚ) := by positivity
          exact le_trans h1 (le_trans (mul_le_mul_of_nonneg_right h2 hMnonneg) h3)
        have hSnonneg : (0 : ℚ) ≤ (Fintype.card ((Fin t → Bool) → Bool) : ℚ) := Nat.cast_nonneg _
        calc (Fintype.card ((Fin t → Bool) → Bool) : ℚ) *
              ∑ x' ∈ (Finset.univ : Finset (Fin n → Bool)).erase x,
                (wClip w x' y) ^ 2 *
                  (((Finset.univ : Finset (Mat h t)).filter
                    (fun M => bucketMap hh M x' = bucketMap hh M x)).card : ℚ)
            ≤ (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((Fintype.card (Mat h t) : ℚ) / 16) :=
              mul_le_mul_of_nonneg_left hinner_le hSnonneg
          _ = (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * (Fintype.card (Mat h t) : ℚ) / 16 := by ring
      -- Apply clip_avg_ge
      have hclip_sum : (3 / 4 : ℚ) * α * (Fintype.card (Mat h t) : ℚ) *
            (Fintype.card ((Fin t → Bool) → Bool) : ℚ) ≤
          ∑ M : Mat h t, ∑ σ : (Fin t → Bool) → Bool, clip (α + Z M σ) := by
        have havg : ∀ M : Mat h t,
            ∑ σ : (Fin t → Bool) → Bool, α * (1 - 4 * (Z M σ) ^ 2) ≤
            ∑ σ : (Fin t → Bool) → Bool, clip (α + Z M σ) := by
          intro M
          have hsym : ∑ σ : (Fin t → Bool) → Bool, clip (α + Z M σ) =
              ∑ σ : (Fin t → Bool) → Bool, (clip (α + Z M σ) + clip (α - Z M σ)) / 2 := by
            have hflip := sum_flipAt (addr hh x) (fun σ => clip (α + Z M σ))
            have hneg : ∑ σ : (Fin t → Bool) → Bool, clip (α + Z M (flipAt (addr hh x) σ)) =
                ∑ σ : (Fin t → Bool) → Bool, clip (α - Z M σ) := by
              apply Finset.sum_congr rfl
              intro σ _
              rw [hZ_flip M σ, sub_eq_add_neg]
            rw [hneg] at hflip
            have hsplit : ∀ σ : (Fin t → Bool) → Bool,
                (clip (α + Z M σ) + clip (α - Z M σ)) / 2 =
                  clip (α + Z M σ) * (1 / 2 : ℚ) + clip (α - Z M σ) * (1 / 2 : ℚ) := by
              intro σ; ring
            simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.sum_mul]
            rw [← hflip]
            ring
          rw [hsym]
          apply Finset.sum_le_sum
          intro σ _
          exact clip_avg_ge hα0 hαhalf
        have htot_ge : ∑ M : Mat h t, ∑ σ : (Fin t → Bool) → Bool, α * (1 - 4 * (Z M σ) ^ 2) ≤
            ∑ M : Mat h t, ∑ σ : (Fin t → Bool) → Bool, clip (α + Z M σ) :=
          Finset.sum_le_sum fun M _ => havg M
        have hsimp : ∑ M : Mat h t, ∑ σ : (Fin t → Bool) → Bool, α * (1 - 4 * (Z M σ) ^ 2) =
            α * ((Fintype.card (Mat h t) : ℚ) * (Fintype.card ((Fin t → Bool) → Bool) : ℚ) -
              4 * ∑ M : Mat h t, ∑ σ : (Fin t → Bool) → Bool, (Z M σ) ^ 2) := by
          simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, mul_one, ← Finset.mul_sum]
        rw [hsimp] at htot_ge
        have h4 : 4 * ∑ M : Mat h t, ∑ σ : (Fin t → Bool) → Bool, (Z M σ) ^ 2 ≤
            (Fintype.card (Mat h t) : ℚ) * (Fintype.card ((Fin t → Bool) → Bool) : ℚ) / 4 := by
          linarith [hZ_sq_tot]
        have hfinal : (3 / 4 : ℚ) * α * (Fintype.card (Mat h t) : ℚ) *
              (Fintype.card ((Fin t → Bool) → Bool) : ℚ) ≤
            α * ((Fintype.card (Mat h t) : ℚ) * (Fintype.card ((Fin t → Bool) → Bool) : ℚ) -
              4 * ∑ M : Mat h t, ∑ σ : (Fin t → Bool) → Bool, (Z M σ) ^ 2) := by
          have hsub : (3 / 4 : ℚ) * ((Fintype.card (Mat h t) : ℚ) *
                (Fintype.card ((Fin t → Bool) → Bool) : ℚ)) ≤
              (Fintype.card (Mat h t) : ℚ) * (Fintype.card ((Fin t → Bool) → Bool) : ℚ) -
                4 * ∑ M : Mat h t, ∑ σ : (Fin t → Bool) → Bool, (Z M σ) ^ 2 := by
            linarith
          have hmul := mul_le_mul_of_nonneg_left hsub hα0
          linarith
        exact le_trans hfinal htot_ge
      have hvote_ge : (3 / 4 : ℚ) * α * (z : ℚ) ≤
          ∑ ω : Ω, sgn (votePred ω) * sgn (truth x y) := by
        rw [hvote_tau, hz_eq]
        have hL2nonneg : (0 : ℚ) ≤ ((2 * L : ℕ) : ℚ) := Nat.cast_nonneg _
        have hmul := mul_le_mul_of_nonneg_left hclip_sum hL2nonneg
        linarith
      have hbad_z : (badM.card : ℚ) * (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ) ≤
          ((D y).card : ℚ) / (H : ℚ) * (z : ℚ) := by
        rw [hz_eq]
        have hnonneg : 0 ≤ (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ) := by
          positivity
        calc (badM.card : ℚ) * (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ)
            = (badM.card : ℚ) * ((Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ)) := by ring
          _ ≤ (((D y).card : ℚ) * (Fintype.card (Mat h t) : ℚ) / (H : ℚ)) *
                ((Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ)) :=
              mul_le_mul_of_nonneg_right hbadM_card hnonneg
          _ = ((D y).card : ℚ) / (H : ℚ) *
                ((Fintype.card (Mat h t) : ℚ) * (Fintype.card ((Fin t → Bool) → Bool) : ℚ) * ((2 * L : ℕ) : ℚ)) := by
              ring
      have hH : H = (2 ^ h : ℚ) := rfl
      have hα : α = min (w x y) (1 / 2) := rfl
      rw [← hH, ← hα]
      have hd : (1 + (3 / 4 : ℚ) * α - 2 * ((D y).card : ℚ) / H) * (z : ℚ) =
          (z : ℚ) + (3 / 4 : ℚ) * α * (z : ℚ) - 2 * (((D y).card : ℚ) / H * (z : ℚ)) := by ring
      rw [hd]
      linarith

end MainConstruction

end PEqualNP.Outside.L_lib_1024

theorem PEqualNP.Outside.L_lib_1024 :
    ∀ (n h k : Nat), h ≤ n →
  let W := Fin n → Bool
  let H := 2^h
  let t := n-h
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (C : Circ) =>
    (∀ i : Fin C.gates.length, ∀ v ∈ (C.gates.get i).inputs, v < n+i.val) ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun g => @decide
    ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
  ∀ (truth : W → Fin k → Bool) (w : W → Fin k → ℚ) (D : Fin k → Finset W),
    (∀ x y, 0 ≤ w x y) → (∀ y, 16*(∑ x : W, (w x y)^2) ≤ (H : ℚ)) →
    ∃ (z : Nat) (C : Fin z → Circ) (tap : Fin z → Fin (h+1) → Nat)
      (read : Fin z → (Fin (h+1) → Bool) → Fin k → Bool),
      0 < z ∧ (∀ s, legal (C s) ∧ cost (C s) ≤ 3*2^((t+1)/2) ∧
        ∀ j, tap s j < n+(C s).gates.length) ∧
      ∀ x y,
        let reward : ℚ := if x ∈ D y then 1 else (3/4 : ℚ)*min (w x y) (1/2)
        let hits := ((Finset.univ : Finset (Fin z)).filter (fun s =>
          read s (fun j => ((C s).wires (List.ofFn x)).getD (tap s j) false) y = truth x y)).card
        (1+reward-2*((D y).card : ℚ)/(H : ℚ))*(z : ℚ) ≤ 2*(hits : ℚ) := by
  intro n h k hh W H t Circ legal cost truth w D hw0 hw2
  exact PEqualNP.Outside.L_lib_1024.main_proof n h k hh truth w D hw0 hw2
