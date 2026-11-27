import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_819_aux

open PEqualNP.CircuitLowerBounds

def changed (x y : Bool) (p : Nat × Nat) : Prop :=
  (x = false → y = true → 0 < p.1) ∧
  (x = true → y = false → 0 < p.2)

def tracks (X Y : List Bool) (a : List (Nat × Nat)) : Prop :=
  ∀ j, changed (X.getD j false) (Y.getD j false) (a.getD j (0,0))

def value (X : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => X.getD i false)

def pathValue (a : List (Nat × Nat)) (g : Gate) : Nat × Nat :=
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  let s := g.inputs.foldl (fun (v : Nat × Nat) i =>
    let t := a.getD i (0,0)
    (v.1+t.1,v.2+t.2)) (0,0)
  let h := (g.inputs.head?.map (fun i => a.getD i (0,0))).getD (0,0)
  if g.op = GateOp.not then (h.2,h.1) else s

theorem gate_tracks (X Y : List Bool) (a : List (Nat × Nat)) (g : Gate)
    (h : tracks X Y a)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) :
    changed (value X g) (value Y g) (pathValue a g) := by
  rcases g with ⟨op, ins⟩
  cases ins with
  | nil =>
      rcases hop with rfl | rfl | rfl <;>
        simp [changed, value, pathValue, GateOp.eval]
  | cons i rest =>
      have hi := h i
      cases rest with
      | nil =>
          rcases hop with rfl | rfl | rfl <;>
            cases hxi : X.getD i false <;> cases hyi : Y.getD i false <;>
            simp_all [changed, value, pathValue, GateOp.eval]
      | cons j rest =>
          cases rest with
          | cons k rest => simp at hlen
          | nil =>
              have hj := h j
              rcases hop with rfl | rfl | rfl <;>
                cases hxi : X.getD i false <;> cases hyi : Y.getD i false <;>
                cases hxj : X.getD j false <;> cases hyj : Y.getD j false <;>
                simp_all [changed, value, pathValue, GateOp.eval]

theorem getD_snoc_ne {α : Type} (L : List α) (v d : α) (j : Nat)
    (h : j ≠ L.length) : (L ++ [v]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

theorem append_tracks (X Y : List Bool) (a : List (Nat × Nat))
    (u v : Bool) (p : Nat × Nat)
    (hXY : X.length = Y.length) (haX : a.length = X.length)
    (h : tracks X Y a) (huv : changed u v p) :
    tracks (X ++ [u]) (Y ++ [v]) (a ++ [p]) := by
  intro j
  by_cases hj : j = X.length
  · subst j
    simpa [changed, ← hXY, haX] using huv
  · simpa only [getD_snoc_ne X u false j hj,
      getD_snoc_ne Y v false j (by omega),
      getD_snoc_ne a p (0,0) j (by omega)] using h j

theorem fold_tracks (gs : List Gate)
    (hg : ∀ g ∈ gs,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (X Y : List Bool) (a : List (Nat × Nat))
    (hXY : X.length = Y.length) (haX : a.length = X.length)
    (h : tracks X Y a) :
    tracks (gs.foldl (fun w g => w ++ [value w g]) X)
      (gs.foldl (fun w g => w ++ [value w g]) Y)
      (gs.foldl (fun w g => w ++ [pathValue w g]) a) := by
  induction gs generalizing X Y a with
  | nil => exact h
  | cons g gs ih =>
      obtain ⟨hop, hlen⟩ := hg g (by simp)
      apply ih (fun k hk => hg k (by simp [hk]))
      · simpa using hXY
      · simpa using haX
      · exact append_tracks X Y a _ _ _ hXY haX h (gate_tracks X Y a g h hop hlen)

theorem seed_tracks (N : Nat) (x y : Fin N → Bool) :
    tracks (List.ofFn x) (List.ofFn y)
      (List.ofFn (fun i : Fin N =>
        (((if x i = false ∧ y i = true then 1 else 0),
         (if x i = true ∧ y i = false then 1 else 0)) : Nat × Nat))) := by
  intro j
  by_cases hj : j < N
  · simp [changed, List.getD, hj]
    constructor <;> intro hx hy <;> simp [hx, hy]
  · simp [changed, List.getD, hj]

end PEqualNP.Outside.L_lib_819_aux

theorem PEqualNP.Outside.L_lib_819 : (∀ (N : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (x y : Fin N → Bool),
  PEqualNP.MetaComplexity.FanInTwo C →
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  let seed := List.ofFn (fun i : Fin N =>
    (((if x i = false ∧ y i = true then 1 else 0),
     (if x i = true ∧ y i = false then 1 else 0)) : Nat × Nat))
  let paths := C.gates.foldl (fun (a : List (Nat × Nat)) g =>
    let s := g.inputs.foldl (fun (v : Nat × Nat) i =>
      let t := a.getD i (0,0)
      (v.1+t.1,v.2+t.2)) (0,0)
    let h := (g.inputs.head?.map (fun i => a.getD i (0,0))).getD (0,0)
    a ++ [if g.op = PEqualNP.CircuitLowerBounds.GateOp.not then (h.2,h.1) else s]) seed
  let X := C.wires (List.ofFn x)
  let Y := C.wires (List.ofFn y)
  ∀ j : Nat, (X.getD j false = false → Y.getD j false = true → 0 < (paths.getD j (0,0)).1) ∧
    (X.getD j false = true → Y.getD j false = false → 0 < (paths.getD j (0,0)).2)) := by
  intro N C x y hf
  apply PEqualNP.Outside.L_lib_819_aux.fold_tracks C.gates
  · intro g hg
    simpa using hf g hg
  · simp
  · simp
  · exact PEqualNP.Outside.L_lib_819_aux.seed_tracks N x y
