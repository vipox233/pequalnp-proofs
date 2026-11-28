import Mathlib
import PEqualNP.Defs

-- One affine partition of the data space for all wires of a circuit with selector and data inputs, with
-- free data pairs kept inside every part.
--
-- Proof: induction over the gate list, last gate first removed. A part is a pair (a, U): for every selector
-- setting s it is the flat a s + U of the data space, and on it every wire so far equals l.y + c s with a
-- fixed data slope l. With no gates there is one part, the whole space. A MOD 2 gate, a NOT gate, or an AND
-- or OR gate with fewer than two inputs keeps every part. For an AND or OR gate reading wires i and j: if the
-- slope of wire i is not zero on U, the part is cut by the value of wire i into two parts with direction
-- U inside the kernel of that slope, the base points moved by a selector-dependent multiple of a fixed
-- vector of U, so wire i is constant on each and the gate is a constant or a copy of wire j; otherwise the
-- same with wire j; otherwise both wires depend on the selector only and so does the gate. Each cut lowers
-- the dimension of U by exactly one. The free pairs: a linear map L into U with P (L x) = x outside the
-- pairs of J and one side of every pair of J zero. At a cut by the slope l, if l (L x) is not always zero,
-- pick a coordinate (t, b) where it is one, zero the pair t, and set coordinate (t, b) to cancel l; the pair
-- t joins J.

namespace PEqualNP.Outside.L_lib_933

open PEqualNP.CircuitLowerBounds

abbrev K := ZMod 2
abbrev Sel (k : ℕ) := Fin k → K
abbrev Dat (v : ℕ) := Fin v → K
abbrev Prs (m : ℕ) := (Fin m × Bool) → K
abbrev Part (k v : ℕ) := (Sel k → Dat v) × Submodule K (Dat v)

/-- The wire list after running a gate list on a wire list: the fold inside `Circuit.wires`. -/
def W (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    W (gs ++ [g]) w = W gs w ++ [g.op.eval (g.inputs.map fun i => (W gs w).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (w : List Bool) : (W gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem new_wire (gs : List Gate) (g : Gate) (w : List Bool) :
    (W (gs ++ [g]) w).getD (w.length + gs.length) false =
      g.op.eval (g.inputs.map fun t => (W gs w).getD t false) := by
  rw [W_snoc, getD_snoc]; simp [W_len]

theorem old_wire (gs : List Gate) (g : Gate) (w : List Bool) (i : ℕ)
    (hi : i ≠ w.length + gs.length) :
    (W (gs ++ [g]) w).getD i false = (W gs w).getD i false := by
  rw [W_snoc, getD_snoc]; simp [W_len, hi]

/-- The input word of a selector setting and a data point. -/
def inp {k v : ℕ} (s : Sel k) (y : Dat v) : List Bool :=
  List.ofFn (fun j : Fin k => decide (s j = 1)) ++ List.ofFn (fun j : Fin v => decide (y j = 1))

theorem inp_len {k v : ℕ} (s : Sel k) (y : Dat v) : (inp s y).length = k + v := by simp [inp]

/-- Every wire of the gate list is `l.y + c s` on the part `(a, U)`. -/
def Aff {k v : ℕ} (gs : List Gate) (a : Sel k → Dat v) (U : Submodule K (Dat v)) : Prop :=
  ∀ wire : ℕ, ∃ (l : Dat v) (c : Sel k → K), ∀ (s : Sel k) (y : Dat v), y - a s ∈ U →
    (W gs (inp s y)).getD wire false = decide (dotProduct l y + c s = 1)

theorem aff_sub {k v : ℕ} (gs : List Gate) (a a' : Sel k → Dat v) (U U' : Submodule K (Dat v))
    (h : Aff gs a U) (hm : ∀ (s : Sel k) (y : Dat v), y - a' s ∈ U' → y - a s ∈ U) :
    Aff gs a' U' := by
  intro wire
  obtain ⟨l, c, hlc⟩ := h wire
  exact ⟨l, c, fun s y hy => hlc s y (hm s y hy)⟩

theorem aff_snoc {k v : ℕ} (gs : List Gate) (g : Gate) (a : Sel k → Dat v) (U : Submodule K (Dat v))
    (h : Aff gs a U)
    (hnew : ∃ (l : Dat v) (c : Sel k → K), ∀ (s : Sel k) (y : Dat v), y - a s ∈ U →
      g.op.eval (g.inputs.map fun t => (W gs (inp s y)).getD t false) =
        decide (dotProduct l y + c s = 1)) :
    Aff (gs ++ [g]) a U := by
  intro wire
  by_cases hw : wire = k + v + gs.length
  · obtain ⟨l, c, hlc⟩ := hnew
    refine ⟨l, c, fun s y hy => ?_⟩
    have e := new_wire gs g (inp s y)
    rw [inp_len] at e
    rw [hw, e, hlc s y hy]
  · obtain ⟨l, c, hlc⟩ := h wire
    refine ⟨l, c, fun s y hy => ?_⟩
    rw [old_wire gs g (inp s y) wire (by rw [inp_len]; exact hw)]
    exact hlc s y hy

theorem aff_nil {k v : ℕ} (a : Sel k → Dat v) (U : Submodule K (Dat v)) : Aff [] a U := by
  intro wire
  by_cases hw : wire < k
  · refine ⟨0, fun s => s ⟨wire, hw⟩, fun s y _ => ?_⟩
    have h1 : (W [] (inp s y)).getD wire false = decide (s ⟨wire, hw⟩ = 1) := by
      show (inp s y).getD wire false = _
      unfold inp
      rw [List.getD_append _ _ _ _ (by simpa using hw), List.getD_eq_getElem _ _ (by simpa using hw)]
      simp
    rw [h1]; simp
  · by_cases hw2 : wire < k + v
    · refine ⟨Pi.single ⟨wire - k, by omega⟩ 1, fun _ => 0, fun s y _ => ?_⟩
      have h1 : (W [] (inp s y)).getD wire false = decide (y ⟨wire - k, by omega⟩ = 1) := by
        show (inp s y).getD wire false = _
        unfold inp
        rw [List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_eq_getElem _ _ (by simp; omega)]
        simp
      rw [h1]; simp [single_dotProduct]
    · refine ⟨0, fun _ => 0, fun s y _ => ?_⟩
      have h1 : (W [] (inp s y)).getD wire false = false := by
        show (inp s y).getD wire false = _
        exact List.getD_eq_default _ _ (by rw [inp_len]; omega)
      rw [h1]; simp

theorem z_not (A : K) : (!decide (A = 1)) = decide (A + 1 = 1) := by revert A; decide
theorem z_one (A : K) :
    decide (List.count true [decide (A = 1)] % 2 = 0) = decide (A + 1 = 1) := by revert A; decide
theorem z_two (A B : K) :
    decide (List.count true [decide (A = 1), decide (B = 1)] % 2 = 0) = decide (A + B + 1 = 1) := by
  revert A B; decide
theorem z_and (A B : K) : (decide (A = 1) && decide (B = 1)) = decide (A * B = 1) := by
  revert A B; decide
theorem z_or (A B : K) : (decide (A = 1) || decide (B = 1)) = decide (A + B + A * B = 1) := by
  revert A B; decide
theorem z_ite (A : K) : (if decide (A = 1) then (1 : K) else 0) = A := by revert A; decide
theorem z_ne (A : K) (h : A ≠ 1) : A = 0 := by revert A; decide
theorem z_self (A : K) : A + A * 1 = 0 := by revert A; decide

/-- A gate that is not a two-input AND or OR is `l.y + c s` where the wires it reads are. -/
theorem new_free {k v : ℕ} (gs : List Gate) (g : Gate) (a : Sel k → Dat v) (U : Submodule K (Dat v))
    (h : Aff gs a U) (hlen : g.inputs.length ≤ 2)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.mod 2 ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))
    (hnp : ¬ ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)) :
    ∃ (l : Dat v) (c : Sel k → K), ∀ (s : Sel k) (y : Dat v), y - a s ∈ U →
      g.op.eval (g.inputs.map fun t => (W gs (inp s y)).getD t false) =
        decide (dotProduct l y + c s = 1) := by
  rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨r, rest⟩⟩⟩
  · rcases hop with hop | hop | hop | ⟨hop, hl⟩
    · refine ⟨0, fun _ => 1, fun s y _ => ?_⟩
      rw [hop]; simp [GateOp.eval]
    · refine ⟨0, fun _ => 0, fun s y _ => ?_⟩
      rw [hop]; simp [GateOp.eval]
    · refine ⟨0, fun _ => 1, fun s y _ => ?_⟩
      rw [hop]; simp [GateOp.eval]
    · exfalso; rw [hin] at hl; simp at hl
  · obtain ⟨la, ca, ha⟩ := h i
    rcases hop with hop | hop | hop | ⟨hop, -⟩
    · refine ⟨la, ca, fun s y hy => ?_⟩
      rw [hop]
      show ((W gs (inp s y)).getD i false && true) = _
      rw [ha s y hy, Bool.and_true]
    · refine ⟨la, ca, fun s y hy => ?_⟩
      rw [hop]
      show ((W gs (inp s y)).getD i false || false) = _
      rw [ha s y hy, Bool.or_false]
    · refine ⟨la, fun s => ca s + 1, fun s y hy => ?_⟩
      rw [hop]
      show decide (List.count true [(W gs (inp s y)).getD i false] % 2 = 0) =
        decide (dotProduct la y + (ca s + 1) = 1)
      rw [ha s y hy, z_one, add_assoc]
    · refine ⟨la, fun s => ca s + 1, fun s y hy => ?_⟩
      rw [hop]
      show (!((W gs (inp s y)).getD i false)) = decide (dotProduct la y + (ca s + 1) = 1)
      rw [ha s y hy, z_not, add_assoc]
  · obtain ⟨la, ca, ha⟩ := h i
    obtain ⟨lb, cb, hb⟩ := h j
    have hl2 : g.inputs.length = 2 := by rw [hin]; rfl
    rcases hop with hop | hop | hop | ⟨-, hl⟩
    · exact absurd ⟨Or.inl hop, hl2⟩ hnp
    · exact absurd ⟨Or.inr hop, hl2⟩ hnp
    · refine ⟨la + lb, fun s => ca s + cb s + 1, fun s y hy => ?_⟩
      have e : dotProduct (la + lb) y + (ca s + cb s + 1) =
          (dotProduct la y + ca s) + (dotProduct lb y + cb s) + 1 := by
        rw [add_dotProduct]; ring
      rw [hop]
      show decide (List.count true [(W gs (inp s y)).getD i false,
        (W gs (inp s y)).getD j false] % 2 = 0) = decide (dotProduct (la + lb) y + (ca s + cb s + 1) = 1)
      rw [e, ha s y hy, hb s y hy, z_two]
    · exfalso; rw [hl2] at hl; omega
  · exfalso
    rw [hin] at hlen
    have : 3 ≤ (i :: j :: r :: rest).length := by simp
    omega

/-- An AND or OR gate reading wires `i` and `j`, on a part where wire `i` is constant. -/
theorem new_paid_l {k v : ℕ} (gs : List Gate) (g : Gate) (a : Sel k → Dat v)
    (U : Submodule K (Dat v)) (h : Aff gs a U) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (i j : ℕ)
    (hin : g.inputs = [i, j]) (β : Bool)
    (hc : ∀ (s : Sel k) (y : Dat v), y - a s ∈ U → (W gs (inp s y)).getD i false = β) :
    ∃ (l : Dat v) (c : Sel k → K), ∀ (s : Sel k) (y : Dat v), y - a s ∈ U →
      g.op.eval (g.inputs.map fun t => (W gs (inp s y)).getD t false) =
        decide (dotProduct l y + c s = 1) := by
  obtain ⟨lb, cb, hb⟩ := h j
  rcases hop with hop | hop <;> cases β
  · refine ⟨0, fun _ => 0, fun s y hy => ?_⟩
    rw [hop, hin]
    show ((W gs (inp s y)).getD i false && ((W gs (inp s y)).getD j false && true)) = _
    rw [hc s y hy]; simp
  · refine ⟨lb, cb, fun s y hy => ?_⟩
    rw [hop, hin]
    show ((W gs (inp s y)).getD i false && ((W gs (inp s y)).getD j false && true)) = _
    rw [hc s y hy, hb s y hy]; simp
  · refine ⟨lb, cb, fun s y hy => ?_⟩
    rw [hop, hin]
    show ((W gs (inp s y)).getD i false || ((W gs (inp s y)).getD j false || false)) = _
    rw [hc s y hy, hb s y hy]; simp
  · refine ⟨0, fun _ => 1, fun s y hy => ?_⟩
    rw [hop, hin]
    show ((W gs (inp s y)).getD i false || ((W gs (inp s y)).getD j false || false)) = _
    rw [hc s y hy]; simp

/-- An AND or OR gate reading wires `i` and `j`, on a part where wire `j` is constant. -/
theorem new_paid_r {k v : ℕ} (gs : List Gate) (g : Gate) (a : Sel k → Dat v)
    (U : Submodule K (Dat v)) (h : Aff gs a U) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (i j : ℕ)
    (hin : g.inputs = [i, j]) (β : Bool)
    (hc : ∀ (s : Sel k) (y : Dat v), y - a s ∈ U → (W gs (inp s y)).getD j false = β) :
    ∃ (l : Dat v) (c : Sel k → K), ∀ (s : Sel k) (y : Dat v), y - a s ∈ U →
      g.op.eval (g.inputs.map fun t => (W gs (inp s y)).getD t false) =
        decide (dotProduct l y + c s = 1) := by
  obtain ⟨la, ca, ha⟩ := h i
  rcases hop with hop | hop <;> cases β
  · refine ⟨0, fun _ => 0, fun s y hy => ?_⟩
    rw [hop, hin]
    show ((W gs (inp s y)).getD i false && ((W gs (inp s y)).getD j false && true)) = _
    rw [hc s y hy]; simp
  · refine ⟨la, ca, fun s y hy => ?_⟩
    rw [hop, hin]
    show ((W gs (inp s y)).getD i false && ((W gs (inp s y)).getD j false && true)) = _
    rw [hc s y hy, ha s y hy]; simp
  · refine ⟨la, ca, fun s y hy => ?_⟩
    rw [hop, hin]
    show ((W gs (inp s y)).getD i false || ((W gs (inp s y)).getD j false || false)) = _
    rw [hc s y hy, ha s y hy]; simp
  · refine ⟨0, fun _ => 1, fun s y hy => ?_⟩
    rw [hop, hin]
    show ((W gs (inp s y)).getD i false || ((W gs (inp s y)).getD j false || false)) = _
    rw [hc s y hy]; simp

/-- An AND or OR gate reading two wires that depend on the selector only. -/
theorem new_sel {k v : ℕ} (gs : List Gate) (g : Gate) (a : Sel k → Dat v)
    (U : Submodule K (Dat v)) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (i j : ℕ)
    (hin : g.inputs = [i, j]) (fi fj : Sel k → K)
    (hi : ∀ (s : Sel k) (y : Dat v), y - a s ∈ U → (W gs (inp s y)).getD i false = decide (fi s = 1))
    (hj : ∀ (s : Sel k) (y : Dat v), y - a s ∈ U → (W gs (inp s y)).getD j false = decide (fj s = 1)) :
    ∃ (l : Dat v) (c : Sel k → K), ∀ (s : Sel k) (y : Dat v), y - a s ∈ U →
      g.op.eval (g.inputs.map fun t => (W gs (inp s y)).getD t false) =
        decide (dotProduct l y + c s = 1) := by
  rcases hop with hop | hop
  · refine ⟨0, fun s => fi s * fj s, fun s y hy => ?_⟩
    rw [hop, hin]
    show ((W gs (inp s y)).getD i false && ((W gs (inp s y)).getD j false && true)) = _
    rw [hi s y hy, hj s y hy, Bool.and_true, z_and]; simp
  · refine ⟨0, fun s => fi s + fj s + fi s * fj s, fun s y hy => ?_⟩
    rw [hop, hin]
    show ((W gs (inp s y)).getD i false || ((W gs (inp s y)).getD j false || false)) = _
    rw [hi s y hy, hj s y hy, Bool.or_false, z_or]; simp

/-- The slope of a wire as a linear form. -/
def phi {v : ℕ} (w : Dat v) : Dat v →ₗ[K] K where
  toFun x := dotProduct w x
  map_add' := dotProduct_add w
  map_smul' c x := by simp [dotProduct_smul]

theorem finrank_cut {v : ℕ} (U : Submodule K (Dat v)) (w : Dat v) :
    Module.finrank K U ≤ Module.finrank K ↥(U ⊓ LinearMap.ker (phi w)) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (LinearMap.ker (phi w))
  have h2 := LinearMap.finrank_range_add_finrank_ker (phi w)
  have h3 : Module.finrank K ↥(LinearMap.range (phi w)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (phi w))
    simpa using this
  have h4 := Submodule.finrank_le (U ⊔ LinearMap.ker (phi w))
  omega

/-- The free pairs inside a direction `U`. -/
def Good {v m : ℕ} (P : Dat v →ₗ[K] Prs m) (U : Submodule K (Dat v)) : Prop :=
  ∃ (J : Finset (Fin m)) (side : Fin m → Bool) (L : Prs m →ₗ[K] Dat v),
    J.card + Module.finrank K U ≤ v ∧ (∀ x : Prs m, L x ∈ U) ∧
    (∀ (x : Prs m) (t : Fin m) (b : Bool), t ∉ J → P (L x) (t, b) = x (t, b)) ∧
    (∀ (x : Prs m) (t : Fin m), t ∈ J → P (L x) (t, side t) = 0)

/-- Zero the two coordinates of pair `t`. -/
def zeroPair {m : ℕ} (t : Fin m) : Prs m →ₗ[K] Prs m where
  toFun x p := if p.1 = t then 0 else x p
  map_add' x y := by
    funext p
    by_cases hp : p.1 = t <;> simp [hp]
  map_smul' c x := by
    funext p
    by_cases hp : p.1 = t <;> simp [hp]

theorem good_cut {v m : ℕ} (P : Dat v →ₗ[K] Prs m) (U : Submodule K (Dat v)) (li : Dat v)
    (hG : Good P U) (u0 : Dat v) (hu0 : u0 ∈ U) (hu1 : dotProduct li u0 = 1) :
    Good P (U ⊓ LinearMap.ker (phi li)) := by
  classical
  obtain ⟨J, side, L, hcard, hLU, hfree, hzero⟩ := hG
  have hlt : Module.finrank K ↥(U ⊓ LinearMap.ker (phi li)) < Module.finrank K U := by
    apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne inf_le_left (fun heq => ?_)
    have hmem : u0 ∈ U ⊓ LinearMap.ker (phi li) := by rw [heq]; exact hu0
    have h0 : dotProduct li u0 = 0 := LinearMap.mem_ker.1 hmem.2
    rw [hu1] at h0
    exact one_ne_zero h0
  by_cases hf : ∀ x : Prs m, dotProduct li (L x) = 0
  · exact ⟨J, side, L, by omega, fun x => ⟨hLU x, LinearMap.mem_ker.2 (hf x)⟩, hfree, hzero⟩
  · obtain ⟨f, hfdef⟩ : ∃ f : Prs m →ₗ[K] K, f = (phi li).comp L := ⟨_, rfl⟩
    have hfa : ∀ x : Prs m, f x = dotProduct li (L x) := by intro x; rw [hfdef]; rfl
    have hpiv : ∃ p : Fin m × Bool, f (Pi.single p 1) = 1 := by
      by_contra hcon0
      have hcon : ∀ p : Fin m × Bool, f (Pi.single p 1) ≠ 1 := fun p hc => hcon0 ⟨p, hc⟩
      apply hf
      intro x
      have hz : f = 0 := by
        apply LinearMap.pi_ext
        intro p c
        have e : (Pi.single p c : Prs m) = c • Pi.single p (1 : K) := by
          rw [← Pi.single_smul]; simp
        rw [e, map_smul, z_ne _ (hcon p)]; simp
      rw [← hfa, hz]; rfl
    obtain ⟨⟨t, b⟩, hp⟩ := hpiv
    obtain ⟨E, hE⟩ : ∃ E : Prs m →ₗ[K] Prs m,
        E = zeroPair t + (f.comp (zeroPair t)).smulRight (Pi.single (t, b) (1 : K)) := ⟨_, rfl⟩
    have hEa : ∀ (x : Prs m) (p : Fin m × Bool),
        E x p = (if p.1 = t then 0 else x p) + f (zeroPair t x) * (Pi.single (t, b) (1 : K) : Prs m) p := by
      intro x p; rw [hE]; rfl
    have hE1 : ∀ (x : Prs m) (p : Fin m × Bool), p.1 ≠ t → E x p = x p := by
      intro x p hpt
      have hne : p ≠ (t, b) := fun hc => hpt (by rw [hc])
      rw [hEa, Pi.single_eq_of_ne hne]; simp [hpt]
    have hE2 : ∀ x : Prs m, E x (t, !b) = 0 := by
      intro x
      have hne : (t, !b) ≠ (t, b) := by
        intro hc
        have := congrArg Prod.snd hc
        cases b <;> simp at this
      rw [hEa, Pi.single_eq_of_ne hne]; simp
    have hE3 : ∀ x : Prs m, f (E x) = 0 := by
      intro x
      have e : E x = zeroPair t x + f (zeroPair t x) • (Pi.single (t, b) (1 : K) : Prs m) := by
        rw [hE]; rfl
      rw [e, map_add, map_smul, hp, smul_eq_mul]
      exact z_self _
    have hcardJ : (insert t J).card ≤ J.card + 1 := Finset.card_insert_le t J
    by_cases htJ : t ∈ J
    · refine ⟨J, side, L.comp E, by omega, ?_, ?_, ?_⟩
      · intro x
        exact ⟨hLU _, LinearMap.mem_ker.2 (by
          show dotProduct li (L (E x)) = 0
          rw [← hfa, hE3])⟩
      · intro x t' b' ht'
        have hne : t' ≠ t := fun hc => ht' (by rw [hc]; exact htJ)
        show P (L (E x)) (t', b') = x (t', b')
        rw [hfree (E x) t' b' ht', hE1 x (t', b') hne]
      · intro x t' ht'
        exact hzero (E x) t' ht'
    · refine ⟨insert t J, Function.update side t (!b), L.comp E, by omega, ?_, ?_, ?_⟩
      · intro x
        exact ⟨hLU _, LinearMap.mem_ker.2 (by
          show dotProduct li (L (E x)) = 0
          rw [← hfa, hE3])⟩
      · intro x t' b' ht'
        have hne : t' ≠ t := fun hc => ht' (by rw [hc]; exact Finset.mem_insert_self _ _)
        have hnJ : t' ∉ J := fun hc => ht' (Finset.mem_insert_of_mem hc)
        show P (L (E x)) (t', b') = x (t', b')
        rw [hfree (E x) t' b' hnJ, hE1 x (t', b') hne]
      · intro x t' ht'
        show P (L (E x)) (t', Function.update side t (!b) t') = 0
        by_cases hc : t' = t
        · rw [hc, Function.update_self, hfree (E x) t (!b) htJ, hE2]
        · rw [Function.update_of_ne hc]
          exact hzero (E x) t' ((Finset.mem_insert.1 ht').resolve_left hc)

/-- Cut a part by the value of a wire whose slope is not zero on the direction. -/
theorem cut {k v m : ℕ} (P : Dat v →ₗ[K] Prs m) (gs : List Gate) (a : Sel k → Dat v)
    (U : Submodule K (Dat v)) (hG : Good P U) (i : ℕ) (li : Dat v) (ci : Sel k → K)
    (hi : ∀ (s : Sel k) (y : Dat v), y - a s ∈ U →
      (W gs (inp s y)).getD i false = decide (dotProduct li y + ci s = 1))
    (u0 : Dat v) (hu0 : u0 ∈ U) (hu1 : dotProduct li u0 = 1) :
    ∃ (a0 a1 : Sel k → Dat v) (U' : Submodule K (Dat v)),
      Module.finrank K U ≤ Module.finrank K U' + 1 ∧ Good P U' ∧
      (∀ (s : Sel k) (y : Dat v), y - a0 s ∈ U' → y - a s ∈ U) ∧
      (∀ (s : Sel k) (y : Dat v), y - a1 s ∈ U' → y - a s ∈ U) ∧
      (∀ (s : Sel k) (y : Dat v), y - a0 s ∈ U' → (W gs (inp s y)).getD i false = false) ∧
      (∀ (s : Sel k) (y : Dat v), y - a1 s ∈ U' → (W gs (inp s y)).getD i false = true) ∧
      (∀ (s : Sel k) (y : Dat v), y - a s ∈ U →
        ((W gs (inp s y)).getD i false = false → y - a0 s ∈ U') ∧
        ((W gs (inp s y)).getD i false = true → y - a1 s ∈ U')) := by
  have hback : ∀ (β : K) (s : Sel k) (y : Dat v),
      y - (a s + (dotProduct li (a s) + ci s + β) • u0) ∈ U ⊓ LinearMap.ker (phi li) →
      y - a s ∈ U := by
    intro β s y hy
    have e : y - a s = (y - (a s + (dotProduct li (a s) + ci s + β) • u0))
        + (dotProduct li (a s) + ci s + β) • u0 := by abel
    rw [e]; exact U.add_mem hy.1 (U.smul_mem _ hu0)
  have hval : ∀ (β : K) (s : Sel k) (y : Dat v),
      y - (a s + (dotProduct li (a s) + ci s + β) • u0) ∈ U ⊓ LinearMap.ker (phi li) →
      (W gs (inp s y)).getD i false = decide (β = 1) := by
    intro β s y hy
    have hk : dotProduct li (y - (a s + (dotProduct li (a s) + ci s + β) • u0)) = 0 :=
      LinearMap.mem_ker.1 hy.2
    rw [dotProduct_sub, dotProduct_add, dotProduct_smul, hu1] at hk
    rw [hi s y (hback β s y hy)]
    clear hy
    generalize dotProduct li y = Y at hk ⊢
    generalize dotProduct li (a s) = A at hk ⊢
    generalize ci s = C at hk ⊢
    revert Y A C β
    decide
  have hfwd : ∀ (β : K) (s : Sel k) (y : Dat v), y - a s ∈ U →
      (W gs (inp s y)).getD i false = decide (β = 1) →
      y - (a s + (dotProduct li (a s) + ci s + β) • u0) ∈ U ⊓ LinearMap.ker (phi li) := by
    intro β s y hy hv
    rw [hi s y hy] at hv
    refine ⟨?_, LinearMap.mem_ker.2 ?_⟩
    · have e : y - (a s + (dotProduct li (a s) + ci s + β) • u0)
          = (y - a s) - (dotProduct li (a s) + ci s + β) • u0 := by abel
      rw [e]; exact U.sub_mem hy (U.smul_mem _ hu0)
    · show dotProduct li (y - (a s + (dotProduct li (a s) + ci s + β) • u0)) = 0
      rw [dotProduct_sub, dotProduct_add, dotProduct_smul, hu1]
      generalize dotProduct li y = Y at hv ⊢
      generalize dotProduct li (a s) = A at hv ⊢
      generalize ci s = C at hv ⊢
      revert Y A C β
      decide
  refine ⟨fun s => a s + (dotProduct li (a s) + ci s + 0) • u0,
    fun s => a s + (dotProduct li (a s) + ci s + 1) • u0, U ⊓ LinearMap.ker (phi li),
    finrank_cut U li, good_cut P U li hG u0 hu0 hu1, hback 0, hback 1, ?_, ?_, ?_⟩
  · intro s y hy
    rw [hval 0 s y hy]; decide
  · intro s y hy
    rw [hval 1 s y hy]; decide
  · intro s y hy
    exact ⟨fun hv => hfwd 0 s y hy (by rw [hv]; decide), fun hv => hfwd 1 s y hy (by rw [hv]; decide)⟩

/-- What is kept for every part: the dimension count, the wire forms and the free pairs. -/
def Inv {k v m : ℕ} (P : Dat v →ₗ[K] Prs m) (gs : List Gate) (c : ℕ) (Q : Part k v) : Prop :=
  v ≤ Module.finrank K Q.2 + c ∧ Aff gs Q.1 Q.2 ∧ Good P Q.2

/-- A part that is kept whole. -/
theorem keep {k v m : ℕ} (P : Dat v →ₗ[K] Prs m) (gs : List Gate) (g : Gate) (c d : ℕ)
    (Q : Part k v) (hI : Inv P gs c Q) (h : Aff (gs ++ [g]) Q.1 Q.2) :
    ∃ T : Finset (Part k v),
      (∀ Q' ∈ T, Inv P (gs ++ [g]) (c + d) Q' ∧
        ∀ (s : Sel k) (y : Dat v), y - Q'.1 s ∈ Q'.2 → y - Q.1 s ∈ Q.2) ∧
      (∀ (s : Sel k) (y : Dat v), y - Q.1 s ∈ Q.2 → ∃! Q', Q' ∈ T ∧ y - Q'.1 s ∈ Q'.2) := by
  refine ⟨{Q}, ?_, ?_⟩
  · intro Q' hQ'
    rw [Finset.mem_singleton] at hQ'; subst hQ'
    exact ⟨⟨by have := hI.1; omega, h, hI.2.2⟩, fun s y hy => hy⟩
  · intro s y hy
    exact ⟨Q, ⟨Finset.mem_singleton_self _, hy⟩, fun Q' hQ' => Finset.mem_singleton.1 hQ'.1⟩

/-- The two parts of a cut, with the new gate added. -/
theorem two {k v m : ℕ} (P : Dat v →ₗ[K] Prs m) (gs : List Gate) (g : Gate) (c : ℕ)
    (Q : Part k v) (hI : Inv P gs c Q) (i : ℕ) (a0 a1 : Sel k → Dat v) (U' : Submodule K (Dat v))
    (hfin : Module.finrank K Q.2 ≤ Module.finrank K U' + 1) (hG' : Good P U')
    (hm0 : ∀ (s : Sel k) (y : Dat v), y - a0 s ∈ U' → y - Q.1 s ∈ Q.2)
    (hm1 : ∀ (s : Sel k) (y : Dat v), y - a1 s ∈ U' → y - Q.1 s ∈ Q.2)
    (hv0 : ∀ (s : Sel k) (y : Dat v), y - a0 s ∈ U' → (W gs (inp s y)).getD i false = false)
    (hv1 : ∀ (s : Sel k) (y : Dat v), y - a1 s ∈ U' → (W gs (inp s y)).getD i false = true)
    (hcov : ∀ (s : Sel k) (y : Dat v), y - Q.1 s ∈ Q.2 →
      ((W gs (inp s y)).getD i false = false → y - a0 s ∈ U') ∧
      ((W gs (inp s y)).getD i false = true → y - a1 s ∈ U'))
    (A0 : Aff (gs ++ [g]) a0 U') (A1 : Aff (gs ++ [g]) a1 U') :
    ∃ T : Finset (Part k v),
      (∀ Q' ∈ T, Inv P (gs ++ [g]) (c + 1) Q' ∧
        ∀ (s : Sel k) (y : Dat v), y - Q'.1 s ∈ Q'.2 → y - Q.1 s ∈ Q.2) ∧
      (∀ (s : Sel k) (y : Dat v), y - Q.1 s ∈ Q.2 → ∃! Q', Q' ∈ T ∧ y - Q'.1 s ∈ Q'.2) := by
  classical
  have hfr := hI.1
  refine ⟨{(a0, U'), (a1, U')}, ?_, ?_⟩
  · intro Q' hQ'
    rcases Finset.mem_insert.1 hQ' with rfl | hQ'
    · exact ⟨⟨by show v ≤ Module.finrank K U' + (c + 1); omega, A0, hG'⟩, hm0⟩
    · rw [Finset.mem_singleton] at hQ'; subst hQ'
      exact ⟨⟨by show v ≤ Module.finrank K U' + (c + 1); omega, A1, hG'⟩, hm1⟩
  · intro s y hy
    obtain ⟨c0, c1⟩ := hcov s y hy
    cases hval : (W gs (inp s y)).getD i false
    · refine ⟨(a0, U'), ⟨by simp, c0 hval⟩, ?_⟩
      rintro Q' ⟨hQ', hyQ'⟩
      rcases Finset.mem_insert.1 hQ' with rfl | hQ'
      · rfl
      · rw [Finset.mem_singleton] at hQ'; subst hQ'
        have h1 := hv1 s y hyQ'
        rw [hval] at h1
        exact absurd h1 (by simp)
    · refine ⟨(a1, U'), ⟨by simp, c1 hval⟩, ?_⟩
      rintro Q' ⟨hQ', hyQ'⟩
      rcases Finset.mem_insert.1 hQ' with rfl | hQ'
      · have h0 := hv0 s y hyQ'
        rw [hval] at h0
        exact absurd h0 (by simp)
      · exact Finset.mem_singleton.1 hQ'

/-- A two-input AND or OR gate cuts a part into at most two. -/
theorem split {k v m : ℕ} (P : Dat v →ₗ[K] Prs m) (gs : List Gate) (g : Gate) (c : ℕ)
    (Q : Part k v) (hI : Inv P gs c Q) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2) :
    ∃ T : Finset (Part k v),
      (∀ Q' ∈ T, Inv P (gs ++ [g]) (c + 1) Q' ∧
        ∀ (s : Sel k) (y : Dat v), y - Q'.1 s ∈ Q'.2 → y - Q.1 s ∈ Q.2) ∧
      (∀ (s : Sel k) (y : Dat v), y - Q.1 s ∈ Q.2 → ∃! Q', Q' ∈ T ∧ y - Q'.1 s ∈ Q'.2) := by
  obtain ⟨i, j, hin⟩ := List.length_eq_two.1 hlen
  have hA := hI.2.1
  have hG := hI.2.2
  obtain ⟨li, ci, hi⟩ := hA i
  obtain ⟨lj, cj, hj⟩ := hA j
  by_cases hvi : ∃ u0 ∈ Q.2, dotProduct li u0 = 1
  · obtain ⟨u0, hu0, hu1⟩ := hvi
    obtain ⟨a0, a1, U', hfin, hG', hm0, hm1, hv0, hv1, hcov⟩ :=
      cut P gs Q.1 Q.2 hG i li ci hi u0 hu0 hu1
    exact two P gs g c Q hI i a0 a1 U' hfin hG' hm0 hm1 hv0 hv1 hcov
      (aff_snoc gs g a0 U' (aff_sub gs Q.1 a0 Q.2 U' hA hm0)
        (new_paid_l gs g a0 U' (aff_sub gs Q.1 a0 Q.2 U' hA hm0) hop i j hin false hv0))
      (aff_snoc gs g a1 U' (aff_sub gs Q.1 a1 Q.2 U' hA hm1)
        (new_paid_l gs g a1 U' (aff_sub gs Q.1 a1 Q.2 U' hA hm1) hop i j hin true hv1))
  · by_cases hvj : ∃ u0 ∈ Q.2, dotProduct lj u0 = 1
    · obtain ⟨u0, hu0, hu1⟩ := hvj
      obtain ⟨a0, a1, U', hfin, hG', hm0, hm1, hv0, hv1, hcov⟩ :=
        cut P gs Q.1 Q.2 hG j lj cj hj u0 hu0 hu1
      exact two P gs g c Q hI j a0 a1 U' hfin hG' hm0 hm1 hv0 hv1 hcov
        (aff_snoc gs g a0 U' (aff_sub gs Q.1 a0 Q.2 U' hA hm0)
          (new_paid_r gs g a0 U' (aff_sub gs Q.1 a0 Q.2 U' hA hm0) hop i j hin false hv0))
        (aff_snoc gs g a1 U' (aff_sub gs Q.1 a1 Q.2 U' hA hm1)
          (new_paid_r gs g a1 U' (aff_sub gs Q.1 a1 Q.2 U' hA hm1) hop i j hin true hv1))
    · have hzi : ∀ u ∈ Q.2, dotProduct li u = 0 := fun u hu => z_ne _ (fun hc => hvi ⟨u, hu, hc⟩)
      have hzj : ∀ u ∈ Q.2, dotProduct lj u = 0 := fun u hu => z_ne _ (fun hc => hvj ⟨u, hu, hc⟩)
      have hsel : ∀ (l : Dat v), (∀ u ∈ Q.2, dotProduct l u = 0) → ∀ (s : Sel k) (y : Dat v),
          y - Q.1 s ∈ Q.2 → dotProduct l y = dotProduct l (Q.1 s) := by
        intro l hl s y hy
        have h0 := hl _ hy
        rw [dotProduct_sub] at h0
        exact sub_eq_zero.1 h0
      exact keep P gs g c 1 Q hI (aff_snoc gs g Q.1 Q.2 hA
        (new_sel gs g Q.1 Q.2 hop i j hin (fun s => dotProduct li (Q.1 s) + ci s)
          (fun s => dotProduct lj (Q.1 s) + cj s)
          (fun s y hy => by rw [hi s y hy, hsel li hzi s y hy])
          (fun s y hy => by rw [hj s y hy, hsel lj hzj s y hy])))

/-- The number of two-input AND and OR gates, written as in the statement. -/
noncomputable def cost (gs : List Gate) : ℕ :=
  gs.countP (fun h => @decide ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length = 2)
    (Classical.propDecidable _))

theorem cost_snoc_paid (gs : List Gate) (g : Gate)
    (h : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    cost (gs ++ [g]) = cost gs + 1 := by
  unfold cost
  rw [List.countP_append]
  simp [h]

theorem cost_snoc_free (gs : List Gate) (g : Gate)
    (h : ¬ ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)) :
    cost (gs ++ [g]) = cost gs := by
  unfold cost
  rw [List.countP_append]
  simp [h]

/-- One gate more: every part is replaced by the parts it is cut into. -/
theorem glue {k v m : ℕ} (P : Dat v →ₗ[K] Prs m) (gs : List Gate) (g : Gate) (c d : ℕ)
    (parts : Finset (Part k v))
    (hcov : ∀ (s : Sel k) (y : Dat v), ∃! Q, Q ∈ parts ∧ y - Q.1 s ∈ Q.2)
    (hstep : ∀ Q ∈ parts, ∃ T : Finset (Part k v),
      (∀ Q' ∈ T, Inv P (gs ++ [g]) (c + d) Q' ∧
        ∀ (s : Sel k) (y : Dat v), y - Q'.1 s ∈ Q'.2 → y - Q.1 s ∈ Q.2) ∧
      (∀ (s : Sel k) (y : Dat v), y - Q.1 s ∈ Q.2 → ∃! Q', Q' ∈ T ∧ y - Q'.1 s ∈ Q'.2)) :
    ∃ parts' : Finset (Part k v), (∀ Q ∈ parts', Inv P (gs ++ [g]) (c + d) Q) ∧
      (∀ (s : Sel k) (y : Dat v), ∃! Q, Q ∈ parts' ∧ y - Q.1 s ∈ Q.2) := by
  classical
  choose T hT1 hT2 using hstep
  refine ⟨parts.attach.biUnion (fun Q => T Q.1 Q.2), ?_, ?_⟩
  · intro R hR
    obtain ⟨⟨Q, hQm⟩, -, hRT⟩ := Finset.mem_biUnion.1 hR
    exact (hT1 Q hQm R hRT).1
  · intro s y
    obtain ⟨Q, ⟨hQm, hyQ⟩, hQu⟩ := hcov s y
    obtain ⟨Q', ⟨hQ'T, hyQ'⟩, hQ'u⟩ := hT2 Q hQm s y hyQ
    refine ⟨Q', ⟨Finset.mem_biUnion.2 ⟨⟨Q, hQm⟩, Finset.mem_attach _ _, hQ'T⟩, hyQ'⟩, ?_⟩
    rintro R ⟨hR, hyR⟩
    obtain ⟨⟨Q2, hQ2m⟩, -, hRT⟩ := Finset.mem_biUnion.1 hR
    have hy2 := (hT1 Q2 hQ2m R hRT).2 s y hyR
    have hQQ : Q2 = Q := hQu Q2 ⟨hQ2m, hy2⟩
    subst hQQ
    exact hQ'u R ⟨hRT, hyR⟩

/-- The partition, as a finite set of parts. -/
theorem main {k v m : ℕ} (P : Dat v →ₗ[K] Prs m) (hP : Function.Surjective P) : ∀ gs : List Gate,
    (∀ g ∈ gs, g.inputs.length ≤ 2 ∧ (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.mod 2 ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1))) →
    ∃ parts : Finset (Part k v), (∀ Q ∈ parts, Inv P gs (cost gs) Q) ∧
      (∀ (s : Sel k) (y : Dat v), ∃! Q, Q ∈ parts ∧ y - Q.1 s ∈ Q.2) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    obtain ⟨L, hL⟩ := P.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hP)
    refine ⟨{((fun _ => 0), ⊤)}, ?_, ?_⟩
    · intro Q hQ
      rw [Finset.mem_singleton] at hQ; subst hQ
      refine ⟨by simp, aff_nil _ _, ∅, fun _ => false, L, by simp, fun x => Submodule.mem_top, ?_, ?_⟩
      · intro x t b _
        have e := LinearMap.congr_fun hL x
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at e
        rw [e]
      · intro x t ht
        exact absurd ht (Finset.notMem_empty t)
    · intro s y
      exact ⟨((fun _ => 0), ⊤), ⟨Finset.mem_singleton_self _, Submodule.mem_top⟩,
        fun Q hQ => Finset.mem_singleton.1 hQ.1⟩
  | append_singleton gs g ih =>
    intro hall
    obtain ⟨parts, hI, hcov⟩ := ih (fun g' hg' => hall g' (List.mem_append_left _ hg'))
    obtain ⟨hlen, hop⟩ := hall g (by simp)
    by_cases hp : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
    · have := glue P gs g (cost gs) 1 parts hcov
        (fun Q hQm => split P gs g (cost gs) Q (hI Q hQm) hp.1 hp.2)
      rw [cost_snoc_paid gs g hp]
      exact this
    · have := glue P gs g (cost gs) 0 parts hcov
        (fun Q hQm => keep P gs g (cost gs) 0 Q (hI Q hQm) (aff_snoc gs g Q.1 Q.2 (hI Q hQm).2.1
          (new_free gs g Q.1 Q.2 (hI Q hQm).2.1 hlen hop hp)))
      rw [cost_snoc_free gs g hp]
      simpa using this

end PEqualNP.Outside.L_lib_933

theorem PEqualNP.Outside.L_lib_933 : ∀ (k v m : ℕ),
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let F := ZMod 2
  let legal := fun (width : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack width C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (width : ℕ) (u : Fin width → F) => List.ofFn (fun j : Fin width => decide (u j = 1))
  let S := Fin k → F
  let V := Fin v → F
  let D := (Fin m × Bool) → F
  ∀ (P : V →ₗ[F] D) (C : Circ), Function.Surjective P → legal (k+v) C →
    let q := cost C
    let wire := fun (w : ℕ) (s : S) (y : V) =>
      if (C.wires (bits k s ++ bits v y)).getD w false then (1 : F) else 0
    ∃ (N : ℕ) (U : Fin N → Submodule F V) (a : Fin N → S → V),
      (∀ (s : S) (y : V), ∃! i : Fin N, y-a i s ∈ U i) ∧
      ∀ i : Fin N, v-Module.finrank F (U i) ≤ q ∧
        (∀ w : Fin (k+v+C.size), ∃ (l : V) (c : S → F),
          ∀ (s : S) (y : V), y-a i s ∈ U i → wire w.val s y = dotProduct l y + c s) ∧
        ∃ (J : Finset (Fin m)) (side : Fin m → Bool) (L : D →ₗ[F] V),
          J.card ≤ v-Module.finrank F (U i) ∧ (∀ x : D, L x ∈ U i) ∧
          (∀ (x : D) (t : Fin m) (b : Bool), t ∉ J → P (L x) (t,b) = x (t,b)) ∧
          (∀ (x : D) (t : Fin m), t ∈ J → P (L x) (t,side t) = 0) := by
  intro k v m
  dsimp only
  intro P C hP hleg
  obtain ⟨parts, hI, hcov⟩ := PEqualNP.Outside.L_lib_933.main P hP C.gates hleg.2
  refine ⟨parts.card, fun i => (parts.equivFin.symm i).1.2, fun i => (parts.equivFin.symm i).1.1,
    ?_, ?_⟩
  · intro s y
    obtain ⟨Q, ⟨hQm, hyQ⟩, hQu⟩ := hcov s y
    refine ⟨parts.equivFin ⟨Q, hQm⟩, by simpa using hyQ, ?_⟩
    intro j hj
    have e := hQu _ ⟨(parts.equivFin.symm j).2, hj⟩
    exact (Equiv.symm_apply_eq _).1 (Subtype.ext e)
  · intro i
    obtain ⟨hfr, hA, J, side, L, hJ, hLU, hfree, hzero⟩ := hI _ (parts.equivFin.symm i).2
    refine ⟨?_, ?_, J, side, L, ?_, hLU, hfree, hzero⟩
    · exact Nat.sub_le_iff_le_add'.2 hfr
    · intro w
      obtain ⟨l, c, hlc⟩ := hA w.val
      refine ⟨l, c, fun s y hy => ?_⟩
      have e := hlc s y hy
      show (if (PEqualNP.Outside.L_lib_933.W C.gates (PEqualNP.Outside.L_lib_933.inp s y)).getD w.val
        false then (1 : ZMod 2) else 0) = _
      rw [e]
      exact PEqualNP.Outside.L_lib_933.z_ite _
    · exact Nat.le_sub_of_add_le hJ
