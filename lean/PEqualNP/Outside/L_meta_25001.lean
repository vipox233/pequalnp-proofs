import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25001_aux

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepWire]; omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (stepWire w g) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

def gt (C : Circuit) (k : ℕ) : Gate := C.gates.getD k ⟨GateOp.and, []⟩

lemma gt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gt C k = C.gates[k] := by
  simp [gt, List.getD_eq_getElem?_getD, hk]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j :=
  ⟨gs.take j, gs.drop (j + 1), by rw [List.cons_getElem_drop_succ, List.take_append_drop],
    by simp; omega⟩

lemma W_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.gates.length :=
  foldl_length _ _

lemma W_input (C : Circuit) (x : List Bool) (u : ℕ) (hu : u < x.length) :
    (C.wires x).getD u false = x.getD u false :=
  foldl_getD_lt _ _ _ hu

lemma W_gate (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) (k : ℕ)
    (hk : k < C.gates.length) :
    (C.wires x).getD (N + k) false = (gt C k).op.eval ((gt C k).inputs.map fun i =>
      if i < N + k then (C.wires x).getD i false else false) := by
  obtain ⟨pre, post, hgs, hpre⟩ := split_gates C.gates k hk
  rw [gt_eq C k hk]
  set gj := C.gates[k]
  let w0 := pre.foldl stepWire x
  have hw0 : w0.length = N + k := by simp [w0, foldl_length, hpre, hx]
  have hW : C.wires x = (gj :: post).foldl stepWire w0 := by
    show C.gates.foldl stepWire x = _
    rw [hgs, List.foldl_append]
  rw [hW, List.foldl_cons, foldl_getD_lt post (stepWire w0 gj) (N + k) (by simp [stepWire]; omega)]
  have e1 : (stepWire w0 gj).getD (N + k) false =
      gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_right, hw0]
  rw [e1]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < N + k
  · simp only [hi, ↓reduceIte]
    exact (foldl_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge w0 i (by omega)

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [coneStep]; omega

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) : (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

/-- The strict cone of gate `k` in terms of the gate list. -/
lemma cone_k (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    ∃ cs : List (List ℕ), cs.length = k ∧
      (cones n C).getD k [] = ((gt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) ∧
      ∀ j < k, (cones n C).getD j [] = cs.getD j [] := by
  obtain ⟨pre, post, hgs, hpre⟩ := split_gates C.gates k hk
  rw [gt_eq C k hk]
  set gk := C.gates[k]
  have hc : cones n C =
      post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]; rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by rw [coneFold_length]; simp [hpre]
  refine ⟨pre.foldl (coneStep n) [], hl0, ?_, fun j hj => ?_⟩
  · rw [hc, coneFold_getD_lt n post _ k (by simp [coneStep, hl0])]
    simp [coneStep, List.getD_eq_getElem?_getD, hl0]
  · rw [hc, coneFold_getD_lt n post _ _ (by simp [coneStep, hl0]; omega)]
    exact coneStep_getD_lt n _ _ _ (by omega)

lemma inCone_of (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) (v : ℕ)
    (hv : v ∈ (gt C k).inputs) (h1 : n ≤ v) (h2 : v < n + k)
    (h : i = v - n ∨ InCone n C i (v - n)) : InCone n C i k := by
  obtain ⟨cs, _, hck, hlt⟩ := cone_k n C k hk
  unfold InCone at h ⊢
  rw [hck]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  refine ⟨v, ⟨hv, h1, h2⟩, ?_⟩
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (hlt (v - n) (by omega) ▸ h)

lemma inCone_lt (n : ℕ) (C : Circuit) (i k : ℕ) (h : InCone n C i k) : k < C.gates.length := by
  by_contra hk
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by rw [cones, coneFold_length]; simp; omega)] at h
  simp at h

lemma inCone_lt' (n : ℕ) (C : Circuit) : ∀ k, ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    obtain ⟨cs, _, hck, hlt⟩ := cone_k n C k (inCone_lt n C i k hi)
    unfold InCone at hi
    rw [hck] at hi
    simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons] at hi
    obtain ⟨v, ⟨_, h1, h2⟩, h⟩ := hi
    rcases h with h | h
    · omega
    · have h' : InCone n C i (v - n) := by
        unfold InCone; rw [hlt (v - n) (by omega)]; exact h
      have := ih (v - n) (by omega) i h'
      omega

def red (w K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map fun i => if i = w then K else i⟩

lemma red_id (w K : ℕ) (g : Gate) (h : w ∉ g.inputs) : red w K g = g := by
  cases g with
  | mk op ins =>
    simp only [red, Gate.mk.injEq, true_and]
    conv_rhs => rw [← List.map_id ins]
    refine List.map_congr_left fun i hi => ?_
    have : i ≠ w := fun e => h (e ▸ hi)
    simp [this]

lemma agree (N : ℕ) (C : Circuit) (w K : ℕ) (x : List Bool) (hx : x.length = N) :
    ∀ k, k < C.gates.length → (∀ j, (j = k ∨ InCone N C j k) → w ∉ (gt C j).inputs) →
      (Circuit.wires ⟨C.gates.map (red w K), C.output⟩ x).getD (N + k) false =
        (C.wires x).getD (N + k) false := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hg
    have hk2 : k < (Circuit.mk (C.gates.map (red w K)) C.output).gates.length := by simp [hk]
    have hgt : gt ⟨C.gates.map (red w K), C.output⟩ k = gt C k := by
      rw [gt_eq _ k hk2, gt_eq C k hk]
      simp only [List.getElem_map]
      exact red_id w K _ (by rw [← gt_eq C k hk]; exact hg k (Or.inl rfl))
    rw [W_gate N _ x hx k hk2, W_gate N C x hx k hk, hgt]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    by_cases hik : i < N + k
    · simp only [hik, ↓reduceIte]
      by_cases hiN : i < N
      · rw [W_input _ x i (by omega), W_input C x i (by omega)]
      · obtain ⟨k', rfl⟩ : ∃ k', i = N + k' := ⟨i - N, by omega⟩
        have he : N + k' - N = k' := by omega
        refine ih k' (by omega) (by omega) fun j hj => hg j (Or.inr ?_)
        rcases hj with rfl | hj
        · exact inCone_of N C j k hk _ hi (by omega) hik (Or.inl he.symm)
        · exact inCone_of N C j k hk _ hi (by omega) hik (Or.inr (by rw [he]; exact hj))
    · simp [hik]

end PEqualNP.Outside.L_meta_25001_aux

open PEqualNP.Outside.L_meta_25001_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25001 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ), w < n + m → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (C.output ≠ w ∧ ∀ g < C.gates.length, (C.output = (n + m) + g ∨ ((n + m) ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → w ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents A C2 ∧ C2.size ≤ C.size ∧ (∀ g ∈ C2.gates, w ∉ g.inputs) ∧ C2.output ≠ w ∧ (∀ i < (n + m), ((∃ g ∈ C2.gates, i ∈ g.inputs) ∨ C2.output = i) → ((∃ g ∈ C.gates, i ∈ g.inputs) ∨ C.output = i)) := by
  intro n m A C w hw hF hR ⟨hout, hcone⟩
  refine ⟨⟨C.gates.map (red w (n + m + C.gates.length)), C.output⟩, ?_, ?_, ?_, ?_, hout, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    simpa [red] using hF g0 hg0
  · intro u v
    rw [← hR u v]
    have hx : (PEqualNP.Represents.oneEach u v).length = n + m := by
      simp [PEqualNP.Represents.oneEach]
    show (Circuit.wires _ _).getD C.output false = (C.wires _).getD C.output false
    by_cases h1 : C.output < n + m
    · rw [W_input _ _ _ (by omega), W_input C _ _ (by omega)]
    by_cases h2 : C.output < n + m + C.gates.length
    · obtain ⟨o, ho⟩ : ∃ o, C.output = n + m + o := ⟨C.output - (n + m), by omega⟩
      have hoL : o < C.gates.length := by omega
      rw [ho]
      refine agree (n + m) C w _ _ hx o hoL fun j hj => ?_
      rcases hj with rfl | hj
      · exact hcone j hoL (Or.inl ho)
      · have := inCone_lt' (n + m) C o j hj
        exact hcone j (by omega)
          (Or.inr ⟨by omega, by rw [ho, Nat.add_sub_cancel_left]; exact hj⟩)
    · rw [getD_ge _ _ (by rw [W_len]; simp; omega), getD_ge _ _ (by rw [W_len]; omega)]
  · simp [Circuit.size]
  · intro g hg
    obtain ⟨g0, _, rfl⟩ := List.mem_map.mp hg
    simp only [red, List.mem_map, not_exists, not_and]
    intro i _
    split_ifs with h
    · omega
    · exact h
  · intro i hi h
    rcases h with ⟨g, hg, hig⟩ | h
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      obtain ⟨j, hj, hji⟩ := List.mem_map.mp hig
      split_ifs at hji with hjw
      · omega
      · exact Or.inl ⟨g0, hg0, hji ▸ hj⟩
    · exact Or.inr h
