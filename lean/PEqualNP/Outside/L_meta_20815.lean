import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20815

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def remap (M big k : ℕ) : ℕ :=
  if k < M then k
  else if k = M then big
  else k - 1

def remapGate (M big : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remap M big)⟩

lemma foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp [List.foldl, ih, step, Nat.add_left_comm, Nat.add_comm]

lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

lemma list_set_eq {α : Type*} (l : List α) (j : ℕ) (a : α) (hj : j < l.length) :
    l.set j a = l.take j ++ a :: l.drop (j + 1) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      congr 1
      exact ih j (by simpa using hj)

lemma getD_append_remap (w₀ vals : List Bool) (big k : ℕ)
    (hbig : w₀.length + vals.length ≤ big) :
    (w₀ ++ vals).getD (remap w₀.length big k) false =
      (w₀ ++ false :: vals).getD k false := by
  unfold remap
  by_cases hlt : k < w₀.length
  · simp [hlt, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
  · by_cases heq : k = w₀.length
    · subst heq
      have hge : (w₀ ++ vals).length ≤ big := by simpa using hbig
      have h1 : (w₀ ++ vals)[big]? = none := List.getElem?_eq_none hge
      simp [List.getD_eq_getElem?_getD, h1]
    · have hgt : w₀.length < k := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) (Ne.symm heq)
      have hge1 : w₀.length ≤ k - 1 := Nat.le_sub_one_of_lt hgt
      have hge2 : w₀.length ≤ k := Nat.le_of_lt hgt
      have hsub : k - w₀.length = (k - 1 - w₀.length) + 1 := by omega
      simp only [hlt, heq, ↓reduceIte, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right hge1, List.getElem?_append_right hge2, hsub]
      simp

lemma foldl_remap (qs : List Gate) (w₀ vals : List Bool) (big : ℕ)
    (hbig : w₀.length + vals.length + qs.length ≤ big) :
    ∃ vals' : List Bool, vals'.length = vals.length + qs.length ∧
      qs.foldl step (w₀ ++ false :: vals) = w₀ ++ false :: vals' ∧
      (qs.map (remapGate w₀.length big)).foldl step (w₀ ++ vals) = w₀ ++ vals' := by
  induction qs generalizing vals with
  | nil =>
    exact ⟨vals, by simp, rfl, rfl⟩
  | cons q qs ih =>
    have hbig0 : w₀.length + vals.length ≤ big := by
      simp at hbig
      omega
    have hinputs :
        ((remapGate w₀.length big q).inputs.map fun i => (w₀ ++ vals).getD i false) =
          (q.inputs.map fun i => (w₀ ++ false :: vals).getD i false) := by
      simp only [remapGate, List.map_map]
      apply List.map_congr_left
      intro k _
      exact getD_append_remap w₀ vals big k hbig0
    set b : Bool := q.op.eval (q.inputs.map fun i => (w₀ ++ false :: vals).getD i false)
    have hstep1 : step (w₀ ++ false :: vals) q = w₀ ++ false :: (vals ++ [b]) := by
      simp [step, b, List.append_assoc]
    have hstep2 : step (w₀ ++ vals) (remapGate w₀.length big q) = w₀ ++ (vals ++ [b]) := by
      unfold step
      rw [hinputs]
      simp [remapGate, b, List.append_assoc]
    have hbig' : w₀.length + (vals ++ [b]).length + qs.length ≤ big := by
      simp at hbig ⊢
      omega
    obtain ⟨vals', hlen, h1, h2⟩ := ih (vals ++ [b]) hbig'
    refine ⟨vals', ?_, ?_, ?_⟩
    · simp at hlen ⊢
      omega
    · simpa [List.foldl, hstep1] using h1
    · simpa [List.foldl, hstep2] using h2

lemma main_proof :
    ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit),
      FanInTwo C → Represents A C →
      (∀ D : Circuit, FanInTwo D → Represents A D → C.size ≤ D.size) →
      ∀ j < C.size, ¬ Represents A
        (⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ : Circuit) := by
  intro n m A C hfan _hrep hmin j hj hrep'
  have hjlen : j < C.gates.length := hj
  set pre : List Gate := C.gates.take j
  set post : List Gate := C.gates.drop (j + 1)
  have hpre_len : pre.length = j := List.length_take_of_le (Nat.le_of_lt hjlen)
  have hsplit : C.gates = pre ++ C.gates[j] :: post := by
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.drop_eq_getElem_cons hjlen]
  have hset : C.gates.set j ⟨GateOp.or, []⟩ = pre ++ ⟨GateOp.or, []⟩ :: post :=
    list_set_eq C.gates j ⟨GateOp.or, []⟩ hjlen
  set M : ℕ := n + m + j
  set big : ℕ := M + post.length
  let D : Circuit := ⟨pre ++ post.map (remapGate M big), remap M big C.output⟩
  have hfanD : FanInTwo D := by
    intro g hg
    simp only [D, List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g0, hg0, rfl⟩
    · exact hfan g (by rw [hsplit]; exact List.mem_append_left _ hg)
    · have h0 := hfan g0 (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      simpa [remapGate] using h0
  have hrepD : Represents A D := by
    intro u v
    have hval' := hrep' u v
    set x : List Bool := oneEach u v
    set w₀ : List Bool := pre.foldl step x
    have hw₀ : w₀.length = M := by
      simp [w₀, M, foldl_step_length, x, oneEach_length, hpre_len]
    have hbig : w₀.length + ([] : List Bool).length + post.length ≤ big := by
      simp [hw₀, big]
    obtain ⟨vals', hlen', h1, h2⟩ := foldl_remap post w₀ [] big hbig
    have hstep0 : step w₀ ⟨GateOp.or, []⟩ = w₀ ++ [false] := by
      simp [step, GateOp.eval]
    have hwC' : (⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ : Circuit).wires x =
        w₀ ++ false :: vals' := by
      change (C.gates.set j ⟨GateOp.or, []⟩).foldl step x = _
      rw [hset, List.foldl_append]
      simpa [List.foldl, w₀, hstep0] using h1
    have hwD : D.wires x = w₀ ++ vals' := by
      change (pre ++ post.map (remapGate M big)).foldl step x = _
      rw [List.foldl_append, ← hw₀]
      simpa [w₀] using h2
    have hbig' : w₀.length + vals'.length ≤ big := by
      simp [hw₀, hlen', big]
    have heval : D.eval x = (⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ : Circuit).eval x := by
      simp only [Circuit.eval, D, hwD, hwC']
      rw [← hw₀]
      exact getD_append_remap w₀ vals' big C.output hbig'
    rw [heval]
    exact hval'
  have hle : C.size ≤ D.size := hmin D hfanD hrepD
  have hCsize : C.size = pre.length + 1 + post.length := by
    change C.gates.length = _
    rw [hsplit]
    simp [Nat.add_assoc, Nat.add_comm]
  have hDsize : D.size = pre.length + post.length := by
    simp [D, Circuit.size]
  omega

end PEqualNP.Outside.L_meta_20815

theorem PEqualNP.Outside.L_meta_20815 :
∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C →
  (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
    PEqualNP.Represents.Represents A D → C.size ≤ D.size) →
  ∀ j < C.size, ¬ PEqualNP.Represents.Represents A
    (⟨C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, C.output⟩ :
      PEqualNP.CircuitLowerBounds.Circuit) :=
  PEqualNP.Outside.L_meta_20815.main_proof
