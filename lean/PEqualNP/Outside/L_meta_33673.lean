import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33673

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

abbrev F2 := ZMod 2

def b2z (b : Bool) : F2 := if b then 1 else 0

def det2 (u v : F2 × F2) : F2 := u.1 * v.2 + u.2 * v.1

lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp [b2z] at h <;> rfl

lemma b2z_false : b2z false = 0 := rfl

lemma b2z_true : b2z true = 1 := rfl

lemma b2z_decide (x : F2) : b2z (decide (x = 1)) = x := by
  fin_cases x <;> rfl

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_or (a b : Bool) : b2z (a || b) = b2z a + b2z b + b2z a * b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> decide

lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

lemma f2_add_self (x : F2) : x + x = 0 := by
  fin_cases x <;> decide

lemma f2_mul_self (x : F2) : x * x = x := by
  fin_cases x <;> rfl

lemma f2_two : (2 : F2) = 0 := rfl

lemma f2_eq_of_add_eq_zero {x y : F2} (h : x + y = 0) : x = y := by
  fin_cases x <;> fin_cases y
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

lemma det2_self (u : F2 × F2) : det2 u u = 0 := by
  unfold det2
  have h : u.1 * u.2 + u.2 * u.1 = u.1 * u.2 + u.1 * u.2 := by ring
  rw [h, f2_add_self]

lemma det2_comm (u v : F2 × F2) : det2 u v = det2 v u := by
  unfold det2; ring

def colorToVec : Fin 3 → F2 × F2
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (0, 1)
  | ⟨2, _⟩ => (1, 1)

def vecToColor : Bool × Bool → Fin 3
  | (true, false) => 0
  | (false, true) => 1
  | (true, true) => 2
  | (false, false) => 0

lemma vecToColor_colorToVec (c : Fin 3) :
    vecToColor (decide ((colorToVec c).1 = 1), decide ((colorToVec c).2 = 1)) = c := by
  fin_cases c <;> decide

lemma colorToVec_vecToColor {u : F2 × F2} (h : u ≠ (0, 0)) :
    colorToVec (vecToColor (decide (u.1 = 1), decide (u.2 = 1))) = u := by
  rcases u with ⟨a, b⟩
  fin_cases a <;> fin_cases b
  · exact absurd rfl h
  · rfl
  · rfl
  · rfl

lemma ne_zero_of_det2_eq_one {u v : F2 × F2} (h : det2 u v = 1) : u ≠ (0, 0) := by
  intro hu
  rw [hu] at h
  simp [det2] at h

lemma card_vertex_w (c : Fin 3) :
    (Finset.univ.filter (fun w : F2 × F2 => det2 (colorToVec c) w = 1)).card = 2 := by
  fin_cases c <;> decide

def pairValid (c1 : Fin 3) (ge : Bool) (yz : (F2 × F2) × (F2 × F2)) : Bool :=
  decide (det2 (colorToVec c1) yz.2 = b2z ge ∧
          det2 (colorToVec c1) yz.1 = 1 ∧
          det2 yz.1 yz.2 = 0)

def pairErr (c2 : Fin 3) (yz : (F2 × F2) × (F2 × F2)) : Bool :=
  decide (det2 (colorToVec c2) yz.2 = 1)

lemma card_pair_false (c1 c2 : Fin 3) (b : Bool) :
    (Finset.univ.filter (fun yz : (F2 × F2) × (F2 × F2) =>
      pairValid c1 false yz = true ∧ pairErr c2 yz = b)).card =
      if b = false then 2 else 0 := by
  fin_cases c1 <;> fin_cases c2 <;> cases b <;> decide

lemma card_pair_true_eq (c1 : Fin 3) (b : Bool) :
    (Finset.univ.filter (fun yz : (F2 × F2) × (F2 × F2) =>
      pairValid c1 true yz = true ∧ pairErr c1 yz = b)).card =
      if b = true then 2 else 0 := by
  fin_cases c1 <;> cases b <;> decide

lemma card_pair_true_ne (c1 c2 : Fin 3) (hne : c1 ≠ c2) (b : Bool) :
    (Finset.univ.filter (fun yz : (F2 × F2) × (F2 × F2) =>
      pairValid c1 true yz = true ∧ pairErr c2 yz = b)).card = 1 := by
  fin_cases c1 <;> fin_cases c2 <;> cases b <;> simp_all <;> decide

def legalOp (u : Gate) : Prop :=
  u.inputs.length ≤ 2 ∧
    (u.op = .and ∨ u.op = .or ∨ u.op = .mod 2 ∨ (u.op = .not ∧ u.inputs.length = 1))

def isNL (u : Gate) : Prop :=
  (u.op = .and ∨ u.op = .or) ∧ u.inputs.length = 2

def legalGates (n : ℕ) (gs : List Gate) : Prop :=
  ReadsBack n ⟨gs, 0⟩ ∧ ∀ u ∈ gs, legalOp u

noncomputable def nlCount (gs : List Gate) : ℕ :=
  gs.countP (fun u => @decide (isNL u) (Classical.propDecidable _))

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires x

lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  unfold wiresOf Circuit.wires
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma wiresOf_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresOf (gs1 ++ gs2) x = wiresOf gs2 (wiresOf gs1 x) := by
  unfold wiresOf Circuit.wires
  exact List.foldl_append

lemma wiresOf_getD_lt (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (wiresOf gs x).getD i false = x.getD i false := by
  unfold wiresOf Circuit.wires
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (x ++ [g.op.eval (g.inputs.map fun idx => x.getD idx false)]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [ih _ hi']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wiresOf_append_getD_lt (gs1 gs2 : List Gate) (x : List Bool) {i : ℕ}
    (hi : i < x.length + gs1.length) :
    (wiresOf (gs1 ++ gs2) x).getD i false = (wiresOf gs1 x).getD i false := by
  rw [wiresOf_append, wiresOf_getD_lt gs2 (wiresOf gs1 x) (by rw [wiresOf_length]; exact hi)]

lemma wiresOf_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (wiresOf (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false) := by
  rw [wiresOf_append]
  set w := wiresOf gs x
  have hlen : w.length = x.length + gs.length := wiresOf_length gs x
  change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD (x.length + gs.length) false = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      show x.length + gs.length - w.length = 0 by omega]
  rfl

lemma legalGates_nil (n : ℕ) : legalGates n [] := by
  refine ⟨?_, by simp⟩
  intro j hj
  simp at hj

lemma legalGates_snoc {n : ℕ} {gs : List Gate} {g : Gate}
    (hleg : legalGates n gs) (hop : legalOp g) (hin : ∀ a ∈ g.inputs, a < n + gs.length) :
    legalGates n (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro j hj a ha
    change j < (gs ++ [g]).length at hj
    change a ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at ha
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at ha
      exact hleg.1 j hj' a ha
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst heq
      rw [List.getD_append_right _ _ _ _ le_rfl] at ha
      simp only [Nat.sub_self, List.getD_cons_zero] at ha
      exact hin a ha
  · intro u hu
    rcases List.mem_append.mp hu with h1 | h2
    · exact hleg.2 u h1
    · rw [List.mem_singleton] at h2
      subst h2
      exact hop

lemma legalGates_prefix {n : ℕ} {gs : List Gate} {g : Gate}
    (hleg : legalGates n (gs ++ [g])) :
    legalGates n gs ∧ legalOp g ∧ ∀ a ∈ g.inputs, a < n + gs.length := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro j hj a ha
    change j < gs.length at hj
    have hj' : j < (gs ++ [g]).length := by simp; omega
    have h := hleg.1 j hj' a
    change a ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs → _ at h
    rw [List.getD_append _ _ _ _ hj] at h
    exact h ha
  · intro u hu
    exact hleg.2 u (List.mem_append_left _ hu)
  · exact hleg.2 g (List.mem_append_right _ (List.mem_singleton_self g))
  · intro a ha
    have hj' : gs.length < (gs ++ [g]).length := by simp
    have h := hleg.1 gs.length hj' a
    change a ∈ ((gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩).inputs → _ at h
    rw [List.getD_append_right _ _ _ _ le_rfl] at h
    simp only [Nat.sub_self, List.getD_cons_zero] at h
    exact h ha

lemma nlCount_append (gs1 gs2 : List Gate) :
    nlCount (gs1 ++ gs2) = nlCount gs1 + nlCount gs2 := by
  unfold nlCount
  exact List.countP_append

lemma nlCount_snoc_of_not {gs : List Gate} {g : Gate} (h : ¬ isNL g) :
    nlCount (gs ++ [g]) = nlCount gs := by
  rw [nlCount_append]
  have h0 : nlCount [g] = 0 := by
    unfold nlCount
    simp [h]
  omega

lemma nlCount_snoc_of_is {gs : List Gate} {g : Gate} (h : isNL g) :
    nlCount (gs ++ [g]) = nlCount gs + 1 := by
  rw [nlCount_append]
  have h1 : nlCount [g] = 1 := by
    unfold nlCount
    simp [h]
  omega

lemma eval_and2 (v1 v2 : Bool) : GateOp.and.eval [v1, v2] = (v1 && v2) := by
  cases v1 <;> cases v2 <;> rfl

lemma eval_or2 (v1 v2 : Bool) : GateOp.or.eval [v1, v2] = (v1 || v2) := by
  cases v1 <;> cases v2 <;> rfl

lemma wires_quad_inv (n : ℕ) (gs : List Gate) (hleg : legalGates n gs) (hcnt : nlCount gs ≤ 1) :
    ∃ a b : Fin n → F2, ∀ w < n + gs.length,
      ∃ α γ : F2, ∃ ℓ : Fin n → F2,
        (nlCount gs = 0 → γ = 0) ∧
        ∀ x : Fin n → Bool,
          b2z ((wiresOf gs (List.ofFn x)).getD w false) =
            α + (∑ i : Fin n, ℓ i * b2z (x i)) +
            γ * ((∑ i : Fin n, a i * b2z (x i)) * (∑ i : Fin n, b i * b2z (x i))) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨0, 0, fun w hw => ?_⟩
    simp only [List.length_nil, Nat.add_zero] at hw
    let i0 : Fin n := ⟨w, hw⟩
    refine ⟨0, 0, fun i => if i = i0 then 1 else 0, fun _ => rfl, fun x => ?_⟩
    have hget : (wiresOf [] (List.ofFn x)).getD w false = x i0 := by
      simp [wiresOf, Circuit.wires, List.getD_eq_getElem?_getD, hw, i0]
    rw [hget]
    simp only [zero_mul, zero_add, ite_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Pi.zero_apply, Finset.sum_const_zero, mul_zero, add_zero]
  | append_singleton gs g ih =>
    obtain ⟨hleg0, hop, hin⟩ := legalGates_prefix hleg
    by_cases hnl : isNL g
    · have hcnt_eq : nlCount (gs ++ [g]) = nlCount gs + 1 := nlCount_snoc_of_is hnl
      have hcnt0 : nlCount gs = 0 := by omega
      obtain ⟨a0, b0, h0⟩ := ih hleg0 (by omega)
      rcases hnl with ⟨hor, hlen2⟩
      cases hgin : g.inputs with
      | nil => simp [hgin] at hlen2
      | cons w1 rest =>
        cases rest with
        | nil => simp [hgin] at hlen2
        | cons w2 rest2 =>
          cases rest2 with
          | cons _ _ => simp [hgin] at hlen2
          | nil =>
            have hw1 : w1 < n + gs.length := hin w1 (by simp [hgin])
            have hw2 : w2 < n + gs.length := hin w2 (by simp [hgin])
            obtain ⟨α1, γ1, ℓ1, hγ1, hev1⟩ := h0 w1 hw1
            obtain ⟨α2, γ2, ℓ2, hγ2, hev2⟩ := h0 w2 hw2
            have hg1 : γ1 = 0 := hγ1 hcnt0
            have hg2 : γ2 = 0 := hγ2 hcnt0
            refine ⟨ℓ1, ℓ2, fun w hw => ?_⟩
            simp only [List.length_append, List.length_singleton] at hw
            by_cases hwlt : w < n + gs.length
            · obtain ⟨α, γ, ℓ, hγ, hev⟩ := h0 w hwlt
              have hg0 : γ = 0 := hγ hcnt0
              refine ⟨α, 0, ℓ, fun _ => rfl, fun x => ?_⟩
              rw [wiresOf_append_getD_lt gs [g] (List.ofFn x) (by simp; exact hwlt)]
              have hx := hev x
              rw [hg0] at hx
              simpa only [zero_mul, add_zero] using hx
            · have hweq : w = n + gs.length := by omega
              subst hweq
              have hlast : ∀ x : Fin n → Bool,
                  (wiresOf (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false =
                    g.op.eval [(wiresOf gs (List.ofFn x)).getD w1 false,
                               (wiresOf gs (List.ofFn x)).getD w2 false] := by
                intro x
                have h := wiresOf_snoc_last gs g (List.ofFn x)
                simp only [List.length_ofFn, hgin, List.map_cons, List.map_nil] at h
                exact h
              rcases hor with hgand | hgor
              · refine ⟨α1 * α2, 1, fun i => α2 * ℓ1 i + α1 * ℓ2 i, by omega, fun x => ?_⟩
                rw [hlast x, hgand, eval_and2, b2z_and, hev1 x, hev2 x, hg1, hg2]
                simp only [zero_mul, add_zero, one_mul, add_mul, Finset.sum_add_distrib,
                  ← Finset.mul_sum, mul_assoc]
                ring
              · refine ⟨α1 + α2 + α1 * α2, 1, fun i => (1 + α2) * ℓ1 i + (1 + α1) * ℓ2 i,
                  by omega, fun x => ?_⟩
                rw [hlast x, hgor, eval_or2, b2z_or, hev1 x, hev2 x, hg1, hg2]
                simp only [zero_mul, add_zero, one_mul, add_mul, Finset.sum_add_distrib,
                  ← Finset.mul_sum, mul_assoc]
                ring
    · have hcnt_eq : nlCount (gs ++ [g]) = nlCount gs := nlCount_snoc_of_not hnl
      obtain ⟨a, b, h0⟩ := ih hleg0 (by omega)
      refine ⟨a, b, fun w hw => ?_⟩
      simp only [List.length_append, List.length_singleton] at hw
      by_cases hwlt : w < n + gs.length
      · obtain ⟨α, γ, ℓ, hγ, hev⟩ := h0 w hwlt
        refine ⟨α, γ, ℓ, fun hz => hγ (by omega), fun x => ?_⟩
        rw [wiresOf_append_getD_lt gs [g] (List.ofFn x) (by simp; exact hwlt)]
        exact hev x
      · have hweq : w = n + gs.length := by omega
        subst hweq
        have hlast : ∀ x : Fin n → Bool,
            (wiresOf (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false =
              g.op.eval (g.inputs.map fun i => (wiresOf gs (List.ofFn x)).getD i false) := by
          intro x
          have h := wiresOf_snoc_last gs g (List.ofFn x)
          simp only [List.length_ofFn] at h
          exact h
        rcases hop with ⟨hlenle, hopcases⟩
        cases hgin : g.inputs with
        | nil =>
          refine ⟨b2z (g.op.eval []), 0, 0, fun _ => rfl, fun x => ?_⟩
          rw [hlast x, hgin]
          simp
        | cons w1 rest =>
          cases rest with
          | nil =>
            have hw1 : w1 < n + gs.length := hin w1 (by simp [hgin])
            obtain ⟨α1, γ1, ℓ1, hγ1, hev1⟩ := h0 w1 hw1
            rcases hopcases with hgand | hgor | hgmod | ⟨hgnot, _⟩
            · refine ⟨α1, γ1, ℓ1, fun hz => hγ1 (by omega), fun x => ?_⟩
              rw [hlast x, hgin, hgand]
              have hv : GateOp.and.eval [(wiresOf gs (List.ofFn x)).getD w1 false] =
                  (wiresOf gs (List.ofFn x)).getD w1 false := by
                cases (wiresOf gs (List.ofFn x)).getD w1 false <;> rfl
              rw [List.map_cons, List.map_nil, hv, hev1 x]
            · refine ⟨α1, γ1, ℓ1, fun hz => hγ1 (by omega), fun x => ?_⟩
              rw [hlast x, hgin, hgor]
              have hv : GateOp.or.eval [(wiresOf gs (List.ofFn x)).getD w1 false] =
                  (wiresOf gs (List.ofFn x)).getD w1 false := by
                cases (wiresOf gs (List.ofFn x)).getD w1 false <;> rfl
              rw [List.map_cons, List.map_nil, hv, hev1 x]
            · refine ⟨1 + α1, γ1, ℓ1, fun hz => hγ1 (by omega), fun x => ?_⟩
              rw [hlast x, hgin, hgmod]
              have hv : ∀ v : Bool, b2z ((GateOp.mod 2).eval [v]) = 1 + b2z v := by
                intro v; cases v <;> decide
              rw [List.map_cons, List.map_nil, hv, hev1 x]
              ring
            · refine ⟨1 + α1, γ1, ℓ1, fun hz => hγ1 (by omega), fun x => ?_⟩
              rw [hlast x, hgin, hgnot]
              have hv : ∀ v : Bool, b2z (GateOp.not.eval [v]) = 1 + b2z v := by
                intro v; cases v <;> decide
              rw [List.map_cons, List.map_nil, hv, hev1 x]
              ring
          | cons w2 rest2 =>
            cases rest2 with
            | cons _ _ =>
              simp [hgin] at hlenle
            | nil =>
              have hw1 : w1 < n + gs.length := hin w1 (by simp [hgin])
              have hw2 : w2 < n + gs.length := hin w2 (by simp [hgin])
              have hgmod : g.op = .mod 2 := by
                rcases hopcases with hgand | hgor | hgmod | ⟨_, hnotlen⟩
                · exact absurd ⟨Or.inl hgand, by simp [hgin]⟩ hnl
                · exact absurd ⟨Or.inr hgor, by simp [hgin]⟩ hnl
                · exact hgmod
                · simp [hgin] at hnotlen
              obtain ⟨α1, γ1, ℓ1, hγ1, hev1⟩ := h0 w1 hw1
              obtain ⟨α2, γ2, ℓ2, hγ2, hev2⟩ := h0 w2 hw2
              refine ⟨1 + α1 + α2, γ1 + γ2, fun i => ℓ1 i + ℓ2 i, fun hz => ?_, fun x => ?_⟩
              · rw [hγ1 (by omega), hγ2 (by omega), add_zero]
              · rw [hlast x, hgin, hgmod]
                have hv : ∀ v1 v2 : Bool,
                    b2z ((GateOp.mod 2).eval [v1, v2]) = 1 + b2z v1 + b2z v2 := by
                  intro v1 v2; cases v1 <;> cases v2 <;> decide
                rw [List.map_cons, List.map_cons, List.map_nil, hv, hev1 x, hev2 x]
                simp only [add_mul, Finset.sum_add_distrib]
                ring

theorem fits_implies_quad {n : ℕ} {C : Circuit}
    (hrb : ReadsBack n C)
    (hop : ∀ u ∈ C.gates, legalOp u)
    (hcnt : nlCount C.gates ≤ 1) :
    ∃ (α : F2) (ℓ a b : Fin n → F2), ∀ x : Fin n → Bool,
      b2z (C.eval (List.ofFn x)) =
        α + (∑ i : Fin n, ℓ i * b2z (x i)) +
        (∑ i : Fin n, a i * b2z (x i)) * (∑ i : Fin n, b i * b2z (x i)) := by
  by_cases hout : C.output < n + C.gates.length
  · have hleg : legalGates n C.gates := ⟨hrb, hop⟩
    obtain ⟨a, b, hw⟩ := wires_quad_inv n C.gates hleg hcnt
    obtain ⟨α, γ, ℓ, _, hev⟩ := hw C.output hout
    refine ⟨α, ℓ, fun i => γ * a i, b, fun x => ?_⟩
    have h := hev x
    change b2z ((wiresOf C.gates (List.ofFn x)).getD C.output false) = _
    rw [h]
    simp only [mul_assoc, ← Finset.mul_sum]
  · refine ⟨0, 0, 0, 0, fun x => ?_⟩
    have hge : (C.wires (List.ofFn x)).length ≤ C.output := by
      change (wiresOf C.gates (List.ofFn x)).length ≤ C.output
      rw [wiresOf_length, List.length_ofFn]
      omega
    have hdef : C.eval (List.ofFn x) = false := by
      unfold Circuit.eval
      exact List.getD_eq_default _ _ hge
    rw [hdef]
    simp [b2z]

def pushFalse (gs : List Gate) : List Gate :=
  gs ++ [⟨GateOp.or, []⟩]

def pushXor (n : ℕ) (gs : List Gate) (w1 w2 : ℕ) : List Gate :=
  gs ++ [⟨GateOp.mod 2, [w1, w2]⟩, ⟨GateOp.not, [n + gs.length]⟩]

def pushAnd (gs : List Gate) (w1 w2 : ℕ) : List Gate :=
  gs ++ [⟨GateOp.and, [w1, w2]⟩]

lemma pushFalse_spec {n : ℕ} {gs : List Gate} (hleg : legalGates n gs) :
    let gs' := pushFalse gs
    let w := n + gs.length
    legalGates n gs' ∧ gs'.length = gs.length + 1 ∧ nlCount gs' = nlCount gs ∧
    (∀ x : Fin n → Bool, ∀ k < n + gs.length,
      (wiresOf gs' (List.ofFn x)).getD k false = (wiresOf gs (List.ofFn x)).getD k false) ∧
    (∀ x : Fin n → Bool, b2z ((wiresOf gs' (List.ofFn x)).getD w false) = 0) := by
  refine ⟨legalGates_snoc hleg ⟨by simp, Or.inr (Or.inl rfl)⟩ (by simp),
    by simp [pushFalse], ?_, ?_, ?_⟩
  · exact nlCount_snoc_of_not (by simp [isNL])
  · intro x k hk
    exact wiresOf_append_getD_lt gs [⟨GateOp.or, []⟩] (List.ofFn x) (by simp; exact hk)
  · intro x
    have h := wiresOf_snoc_last gs ⟨GateOp.or, []⟩ (List.ofFn x)
    simp only [List.length_ofFn, List.map_nil] at h
    unfold pushFalse
    rw [h]
    rfl

lemma pushXor_spec {n : ℕ} {gs : List Gate} (hleg : legalGates n gs) {w1 w2 : ℕ}
    (h1 : w1 < n + gs.length) (h2 : w2 < n + gs.length) :
    let gs' := pushXor n gs w1 w2
    let w := n + gs.length + 1
    legalGates n gs' ∧ gs'.length = gs.length + 2 ∧ nlCount gs' = nlCount gs ∧
    (∀ x : Fin n → Bool, ∀ k < n + gs.length,
      (wiresOf gs' (List.ofFn x)).getD k false = (wiresOf gs (List.ofFn x)).getD k false) ∧
    (∀ x : Fin n → Bool, b2z ((wiresOf gs' (List.ofFn x)).getD w false) =
      b2z ((wiresOf gs (List.ofFn x)).getD w1 false) +
      b2z ((wiresOf gs (List.ofFn x)).getD w2 false)) := by
  let g1 : Gate := ⟨GateOp.mod 2, [w1, w2]⟩
  let g2 : Gate := ⟨GateOp.not, [n + gs.length]⟩
  have hsplit : pushXor n gs w1 w2 = (gs ++ [g1]) ++ [g2] := by
    simp [pushXor, g1, g2]
  have hleg1 : legalGates n (gs ++ [g1]) :=
    legalGates_snoc hleg ⟨by simp [g1], Or.inr (Or.inr (Or.inl rfl))⟩ (by
      intro a ha
      simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> assumption)
  have hleg2 : legalGates n ((gs ++ [g1]) ++ [g2]) :=
    legalGates_snoc hleg1 ⟨by simp [g2], Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩ (by
      intro a ha
      simp only [g2, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha; simp)
  refine ⟨hsplit ▸ hleg2, by simp [pushXor], ?_, ?_, ?_⟩
  · rw [hsplit, nlCount_snoc_of_not (by simp [isNL, g2]), nlCount_snoc_of_not (by simp [isNL, g1])]
  · intro x k hk
    exact wiresOf_append_getD_lt gs [g1, g2] (List.ofFn x) (by simp; exact hk)
  · intro x
    rw [hsplit]
    have hstep2 := wiresOf_snoc_last (gs ++ [g1]) g2 (List.ofFn x)
    simp only [List.length_ofFn, List.length_append, List.length_singleton, g2,
      List.map_cons, List.map_nil] at hstep2
    rw [show n + gs.length + 1 = n + (gs.length + 1) by omega, hstep2]
    have hstep1 := wiresOf_snoc_last gs g1 (List.ofFn x)
    simp only [List.length_ofFn, g1, List.map_cons, List.map_nil] at hstep1
    rw [hstep1]
    generalize (wiresOf gs (List.ofFn x)).getD w1 false = v1
    generalize (wiresOf gs (List.ofFn x)).getD w2 false = v2
    cases v1 <;> cases v2 <;> decide

lemma pushAnd_spec {n : ℕ} {gs : List Gate} (hleg : legalGates n gs) {w1 w2 : ℕ}
    (h1 : w1 < n + gs.length) (h2 : w2 < n + gs.length) :
    let gs' := pushAnd gs w1 w2
    let w := n + gs.length
    legalGates n gs' ∧ gs'.length = gs.length + 1 ∧ nlCount gs' = nlCount gs + 1 ∧
    (∀ x : Fin n → Bool, ∀ k < n + gs.length,
      (wiresOf gs' (List.ofFn x)).getD k false = (wiresOf gs (List.ofFn x)).getD k false) ∧
    (∀ x : Fin n → Bool, b2z ((wiresOf gs' (List.ofFn x)).getD w false) =
      b2z ((wiresOf gs (List.ofFn x)).getD w1 false) *
      b2z ((wiresOf gs (List.ofFn x)).getD w2 false)) := by
  refine ⟨legalGates_snoc hleg ⟨by simp, Or.inl rfl⟩ (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> assumption), by simp [pushAnd], ?_, ?_, ?_⟩
  · exact nlCount_snoc_of_is ⟨Or.inl rfl, rfl⟩
  · intro x k hk
    exact wiresOf_append_getD_lt gs [⟨GateOp.and, [w1, w2]⟩] (List.ofFn x) (by simp; exact hk)
  · intro x
    have h := wiresOf_snoc_last gs ⟨GateOp.and, [w1, w2]⟩ (List.ofFn x)
    simp only [List.length_ofFn, List.map_cons, List.map_nil] at h
    unfold pushAnd
    rw [h]
    generalize (wiresOf gs (List.ofFn x)).getD w1 false = v1
    generalize (wiresOf gs (List.ofFn x)).getD w2 false = v2
    cases v1 <;> cases v2 <;> decide

lemma build_linear_list {n : ℕ} (c : Fin n → F2) (l : List (Fin n)) (gs : List Gate)
    (hleg : legalGates n gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      legalGates n gs' ∧ gs.length ≤ gs'.length ∧ out < n + gs'.length ∧
      nlCount gs' = nlCount gs ∧
      (∀ x : Fin n → Bool, ∀ k < n + gs.length,
        (wiresOf gs' (List.ofFn x)).getD k false = (wiresOf gs (List.ofFn x)).getD k false) ∧
      (∀ x : Fin n → Bool, b2z ((wiresOf gs' (List.ofFn x)).getD out false) =
        (l.map (fun i => c i * b2z (x i))).sum) := by
  induction l generalizing gs with
  | nil =>
    obtain ⟨hleg', hlen', hcnt', hpres', hval'⟩ := pushFalse_spec hleg
    exact ⟨pushFalse gs, n + gs.length, hleg', by omega, by omega, hcnt', hpres',
      fun x => by simpa using hval' x⟩
  | cons i rest ih =>
    obtain ⟨gs1, out1, hleg1, hle1, hout1, hcnt1, hpres1, hval1⟩ := ih gs hleg
    by_cases hci : c i = 1
    · obtain ⟨hleg2, hlen2, hcnt2, hpres2, hval2⟩ :=
        pushXor_spec hleg1 (by omega : i.val < n + gs1.length) hout1
      refine ⟨pushXor n gs1 i.val out1, n + gs1.length + 1, hleg2, by omega, by omega,
        by omega, ?_, ?_⟩
      · intro x k hk
        rw [hpres2 x k (by omega), hpres1 x k hk]
      · intro x
        rw [hval2 x, hval1 x, List.map_cons, List.sum_cons, hci, one_mul]
        have hin : (wiresOf gs1 (List.ofFn x)).getD i.val false = x i := by
          rw [wiresOf_getD_lt gs1 (List.ofFn x) (by simp)]
          simp [List.getD_eq_getElem?_getD, i.isLt]
        rw [hin]
    · have hci0 : c i = 0 := by
        have h2 : c i = 0 ∨ c i = 1 := by
          generalize c i = v
          fin_cases v
          · exact Or.inl rfl
          · exact Or.inr rfl
        exact h2.resolve_right hci
      refine ⟨gs1, out1, hleg1, hle1, hout1, hcnt1, hpres1, fun x => ?_⟩
      rw [hval1 x, List.map_cons, List.sum_cons, hci0, zero_mul, zero_add]

lemma build_linear {n : ℕ} (c : Fin n → F2) (gs : List Gate) (hleg : legalGates n gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      legalGates n gs' ∧ gs.length ≤ gs'.length ∧ out < n + gs'.length ∧
      nlCount gs' = nlCount gs ∧
      (∀ x : Fin n → Bool, ∀ k < n + gs.length,
        (wiresOf gs' (List.ofFn x)).getD k false = (wiresOf gs (List.ofFn x)).getD k false) ∧
      (∀ x : Fin n → Bool, b2z ((wiresOf gs' (List.ofFn x)).getD out false) =
        ∑ i : Fin n, c i * b2z (x i)) := by
  obtain ⟨gs', out, hleg', hle', hout', hcnt', hpres', hval'⟩ :=
    build_linear_list c (List.finRange n) gs hleg
  refine ⟨gs', out, hleg', hle', hout', hcnt', hpres', fun x => ?_⟩
  rw [hval' x, ← Fin.sum_univ_def]

def quadFun {n : ℕ} (v : Fin n → F2 × F2) (x : Fin n → Bool) : Bool :=
  decide ((∑ i : Fin n, (v i).1 * (v i).2 * b2z (x i)) +
    (∑ i : Fin n, (v i).1 * b2z (x i)) * (∑ i : Fin n, (v i).2 * b2z (x i)) = 1)

theorem quadFun_rep {n : ℕ} (v : Fin n → F2 × F2) :
    ∃ C : Circuit,
      (ReadsBack n C ∧ (∀ u ∈ C.gates, legalOp u) ∧ nlCount C.gates ≤ 1) ∧
      ∀ x : Fin n → Bool, quadFun v x = C.eval (List.ofFn x) := by
  obtain ⟨gs1, wa, hleg1, hl1, hwa, hc1, _, hfa⟩ :=
    build_linear (fun i => (v i).1) [] (legalGates_nil n)
  obtain ⟨gs2, wb, hleg2, hl2, hwb, hc2, hp2, hfb⟩ :=
    build_linear (fun i => (v i).2) gs1 hleg1
  obtain ⟨gs3, wd, hleg3, hl3, hwd, hc3, hp3, hfd⟩ :=
    build_linear (fun i => (v i).1 * (v i).2) gs2 hleg2
  obtain ⟨hleg4, hl4, hc4, hp4, hfp⟩ :=
    pushAnd_spec hleg3 (by omega : wa < n + gs3.length) (by omega : wb < n + gs3.length)
  set gs4 := pushAnd gs3 wa wb
  let wp := n + gs3.length
  obtain ⟨hleg5, hl5, hc5, hp5, hfo⟩ :=
    pushXor_spec hleg4 (by omega : wd < n + gs4.length) (by omega : wp < n + gs4.length)
  set gs5 := pushXor n gs4 wd wp
  let wout := n + gs4.length + 1
  have hc0 : nlCount ([] : List Gate) = 0 := rfl
  have hc5_le : nlCount gs5 ≤ 1 := by omega
  refine ⟨⟨gs5, wout⟩, ⟨hleg5.1, hleg5.2, hc5_le⟩, fun x => ?_⟩
  apply b2z_inj
  change b2z (quadFun v x) = b2z ((wiresOf gs5 (List.ofFn x)).getD wout false)
  rw [hfo x, hp4 x wd hwd, hfd x, hfp x, hp3 x wa (by omega), hp2 x wa hwa, hfa x,
    hp3 x wb hwb, hfb x]
  unfold quadFun
  rw [b2z_decide]

def zeroV (n : ℕ) : Fin n → Bool := fun _ => false
def unitV {n : ℕ} (a : Fin n) : Fin n → Bool := fun s => decide (s = a)
def pairV {n : ℕ} (a b : Fin n) : Fin n → Bool := fun s => decide (s = a ∨ s = b)

lemma quadFun_zero {n : ℕ} (v : Fin n → F2 × F2) :
    quadFun v (zeroV n) = false := by
  simp [quadFun, zeroV, b2z]

lemma quadFun_unit {n : ℕ} (v : Fin n → F2 × F2) (a : Fin n) :
    quadFun v (unitV a) = false := by
  apply b2z_inj
  unfold quadFun
  rw [b2z_decide, b2z_false]
  have h1 : ∀ f : Fin n → F2, (∑ i : Fin n, f i * b2z (unitV a i)) = f a := by
    intro f
    rw [Finset.sum_eq_single a]
    · simp [unitV, b2z]
    · intro i _ hia; simp [unitV, hia, b2z]
    · intro h; exact absurd (Finset.mem_univ a) h
  rw [h1 (fun i => (v i).1 * (v i).2), h1 (fun i => (v i).1), h1 (fun i => (v i).2), f2_add_self]

lemma quadFun_pair {n : ℕ} (v : Fin n → F2 × F2) (a b : Fin n) :
    b2z (quadFun v (pairV a b)) = det2 (v a) (v b) := by
  by_cases hab : a = b
  · subst hab
    have hp : pairV a a = unitV a := by
      funext s; simp [pairV, unitV]
    rw [hp, quadFun_unit, b2z_false, det2_self]
  · unfold quadFun
    rw [b2z_decide]
    have h2 : ∀ f : Fin n → F2, (∑ i : Fin n, f i * b2z (pairV a b i)) = f a + f b := by
      intro f
      have hsub : (∑ i : Fin n, f i * b2z (pairV a b i)) =
          ∑ i ∈ ({a, b} : Finset (Fin n)), f i * b2z (pairV a b i) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
        simp [pairV, hi.1, hi.2, b2z]
      rw [hsub, Finset.sum_pair hab]
      simp [pairV, b2z]
    rw [h2 (fun i => (v i).1 * (v i).2), h2 (fun i => (v i).1), h2 (fun i => (v i).2)]
    unfold det2
    have hring :
        ((v a).1 * (v a).2 + (v b).1 * (v b).2) + ((v a).1 + (v b).1) * ((v a).2 + (v b).2) =
        (v a).1 * (v b).2 + (v a).2 * (v b).1 +
          (2 : F2) * ((v a).1 * (v a).2 + (v b).1 * (v b).2) := by ring
    rw [hring, f2_two, zero_mul, add_zero]

def extractVec {n : ℕ} (r0 r1 : Fin n) (f : (Fin n → Bool) → Bool) : Fin n → F2 × F2 :=
  fun s => (b2z (f (pairV r1 s)), b2z (f (pairV r0 s)))

lemma extractVec_quadFun {n : ℕ} {r0 r1 : Fin n} {v : Fin n → F2 × F2}
    (h0 : v r0 = (1, 0)) (h1 : v r1 = (0, 1)) :
    extractVec r0 r1 (quadFun v) = v := by
  funext s
  unfold extractVec
  rw [quadFun_pair, quadFun_pair, h1, h0]
  ext <;> simp [det2]

lemma calibrated_eq_quadFun {n : ℕ} {r0 r1 : Fin n} {f : (Fin n → Bool) → Bool}
    (hrep : ∃ C : Circuit,
      (ReadsBack n C ∧ (∀ u ∈ C.gates, legalOp u) ∧ nlCount C.gates ≤ 1) ∧
      ∀ x : Fin n → Bool, f x = C.eval (List.ofFn x))
    (hz : f (zeroV n) = false)
    (hu : ∀ s : Fin n, f (unitV s) = false)
    (hanc : f (pairV r0 r1) = true) :
    extractVec r0 r1 f r0 = (1, 0) ∧
    extractVec r0 r1 f r1 = (0, 1) ∧
    f = quadFun (extractVec r0 r1 f) := by
  obtain ⟨C, ⟨hrb, hop, hcnt⟩, hfeq⟩ := hrep
  obtain ⟨α, ℓ, a, b, hCev⟩ := fits_implies_quad hrb hop hcnt
  have hf : ∀ x : Fin n → Bool, b2z (f x) =
      α + (∑ i : Fin n, ℓ i * b2z (x i)) +
      (∑ i : Fin n, a i * b2z (x i)) * (∑ i : Fin n, b i * b2z (x i)) := by
    intro x; rw [hfeq x, hCev x]
  have hα : α = 0 := by
    have h0 := hf (zeroV n)
    rw [hz, b2z_false] at h0
    simp [zeroV, b2z] at h0
    exact h0.symm
  have hℓ : ∀ s : Fin n, ℓ s = a s * b s := by
    intro s
    have hs := hf (unitV s)
    rw [hu s, b2z_false, hα, zero_add] at hs
    have h1 : ∀ g : Fin n → F2, (∑ i : Fin n, g i * b2z (unitV s i)) = g s := by
      intro g
      rw [Finset.sum_eq_single s]
      · simp [unitV, b2z]
      · intro i _ his; simp [unitV, his, b2z]
      · intro h; exact absurd (Finset.mem_univ s) h
    rw [h1 ℓ, h1 a, h1 b] at hs
    exact f2_eq_of_add_eq_zero hs.symm
  have hf_quad : f = quadFun (fun s => (a s, b s)) := by
    funext x
    apply b2z_inj
    rw [hf x, hα, zero_add]
    unfold quadFun
    rw [b2z_decide]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hℓ i]
  have hpair_eq : ∀ s t : Fin n, b2z (f (pairV s t)) = a s * b t + b s * a t := by
    intro s t
    rw [hf_quad, quadFun_pair]
    unfold det2
    ring
  have hd : a r0 * b r1 + b r0 * a r1 = 1 := by
    have h := hpair_eq r0 r1
    rw [hanc, b2z_true] at h
    exact h.symm
  have hpair_symm : pairV r1 r0 = pairV r0 r1 := by
    funext s; simp [pairV, or_comm]
  have hr0_self : pairV r0 r0 = unitV r0 := by
    funext s; simp [pairV, unitV]
  have hr1_self : pairV r1 r1 = unitV r1 := by
    funext s; simp [pairV, unitV]
  refine ⟨?_, ?_, ?_⟩
  · unfold extractVec
    rw [hpair_symm, hanc, hr0_self, hu r0]
    rfl
  · unfold extractVec
    rw [hr1_self, hu r1, hanc]
    rfl
  · funext x
    apply b2z_inj
    conv_lhs => rw [hf_quad]
    unfold quadFun
    rw [b2z_decide, b2z_decide]
    set Sa : F2 := ∑ i : Fin n, a i * b2z (x i)
    set Sb : F2 := ∑ i : Fin n, b i * b2z (x i)
    have hA : ∀ i : Fin n, (extractVec r0 r1 f i).1 = a r1 * b i + b r1 * a i := by
      intro i; exact hpair_eq r1 i
    have hB : ∀ i : Fin n, (extractVec r0 r1 f i).2 = a r0 * b i + b r0 * a i := by
      intro i; exact hpair_eq r0 i
    have hsumA : (∑ i : Fin n, (extractVec r0 r1 f i).1 * b2z (x i)) = a r1 * Sb + b r1 * Sa := by
      simp only [hA, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, Sa, Sb]
    have hsumB : (∑ i : Fin n, (extractVec r0 r1 f i).2 * b2z (x i)) = a r0 * Sb + b r0 * Sa := by
      simp only [hB, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, Sa, Sb]
    have hAB : ∀ i : Fin n, (extractVec r0 r1 f i).1 * (extractVec r0 r1 f i).2 =
        a r1 * a r0 * b i + b r1 * b r0 * a i + a i * b i := by
      intro i
      rw [hA i, hB i]
      have h1 : (a r1 * b i + b r1 * a i) * (a r0 * b i + b r0 * a i) =
          a r1 * a r0 * (b i * b i) + b r1 * b r0 * (a i * a i) +
          (a r0 * b r1 + b r0 * a r1) * (a i * b i) := by ring
      rw [h1, f2_mul_self, f2_mul_self, hd, one_mul]
    have hsumAB : (∑ i : Fin n, (extractVec r0 r1 f i).1 * (extractVec r0 r1 f i).2 * b2z (x i)) =
        a r1 * a r0 * Sb + b r1 * b r0 * Sa + ∑ i : Fin n, a i * b i * b2z (x i) := by
      simp only [hAB, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, Sa, Sb]
    rw [hsumAB, hsumA, hsumB]
    have hprod : (a r1 * Sb + b r1 * Sa) * (a r0 * Sb + b r0 * Sa) =
        a r1 * a r0 * (Sb * Sb) + b r1 * b r0 * (Sa * Sa) +
        (a r0 * b r1 + b r0 * a r1) * (Sa * Sb) := by ring
    rw [hprod, f2_mul_self, f2_mul_self, hd, one_mul]
    have hcancel :
        a r1 * a r0 * Sb + b r1 * b r0 * Sa + (∑ i : Fin n, a i * b i * b2z (x i)) +
          (a r1 * a r0 * Sb + b r1 * b r0 * Sa + Sa * Sb) =
        (∑ i : Fin n, a i * b i * b2z (x i)) + Sa * Sb +
          (2 : F2) * (a r1 * a r0 * Sb + b r1 * b r0 * Sa) := by ring
    rw [hcancel, f2_two, zero_mul, add_zero]

def pairsSet (k : ℕ) : Finset (Fin k × Fin k) :=
  (Finset.univ : Finset (Fin k × Fin k)).filter (fun e => e.1 < e.2)

lemma card_pairsSet (k : ℕ) : (pairsSet k).card = k.choose 2 := by
  induction k with
  | zero =>
    simp [pairsSet]
  | succ k ih =>
    let S1 : Finset (Fin (k + 1) × Fin (k + 1)) :=
      (pairsSet (k + 1)).filter (fun e => e.2 < Fin.last k)
    let S2 : Finset (Fin (k + 1) × Fin (k + 1)) :=
      (pairsSet (k + 1)).filter (fun e => ¬ (e.2 < Fin.last k))
    have hpart : (pairsSet (k + 1)).card = S1.card + S2.card := by
      rw [← Finset.card_filter_add_card_filter_not (fun e : Fin (k + 1) × Fin (k + 1) => e.2 < Fin.last k)]
    have hS1 : S1.card = (pairsSet k).card := by
      apply Finset.card_bij (fun e he => (⟨e.1.val, by
        simp only [S1, pairsSet, Finset.mem_filter, Finset.mem_univ, true_and] at he
        have h1 : e.1.val < e.2.val := he.1
        have h2 : e.2.val < k := he.2
        omega⟩, ⟨e.2.val, by
        simp only [S1, pairsSet, Finset.mem_filter, Finset.mem_univ, true_and] at he
        exact he.2⟩))
      · intro e he
        simp only [S1, pairsSet, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        exact he.1
      · intro e1 he1 e2 he2 heq
        ext
        · exact congrArg (fun p : Fin k × Fin k => p.1.val) heq
        · exact congrArg (fun p : Fin k × Fin k => p.2.val) heq
      · intro b hb
        simp only [pairsSet, Finset.mem_filter, Finset.mem_univ, true_and] at hb
        refine ⟨(b.1.castSucc, b.2.castSucc), ?_, by ext <;> rfl⟩
        simp only [S1, pairsSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hb, b.2.isLt⟩
    have hS2 : S2.card = k := by
      have hcard : S2.card = (Finset.univ : Finset (Fin k)).card := by
        apply Finset.card_bij (fun e he => ⟨e.1.val, by
          simp only [S2, pairsSet, Finset.mem_filter, Finset.mem_univ, true_and] at he
          have hlast : e.2.val = k := by
            have hlt := e.2.isLt
            have hnlt : ¬ (e.2.val < k) := he.2
            omega
          have h12 : e.1.val < e.2.val := he.1
          omega⟩)
        · intro _ _; exact Finset.mem_univ _
        · intro e1 he1 e2 he2 heq
          simp only [S2, pairsSet, Finset.mem_filter, Finset.mem_univ, true_and] at he1 he2
          have hl1 : e1.2.val = k := by have := e1.2.isLt; have := he1.2; change ¬ (e1.2.val < k) at this; omega
          have hl2 : e2.2.val = k := by have := e2.2.isLt; have := he2.2; change ¬ (e2.2.val < k) at this; omega
          ext
          · exact congrArg (fun x : Fin k => x.val) heq
          · omega
        · intro b _
          refine ⟨(b.castSucc, Fin.last k), ?_, by ext; rfl⟩
          simp only [S2, pairsSet, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨b.isLt, ?_⟩
          exact lt_irrefl _
      rw [hcard, Finset.card_univ, Fintype.card_fin]
    rw [hpart, hS1, ih, hS2, Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

noncomputable def pairEquiv (k : ℕ) : Fin (k.choose 2) ≃ { e : Fin k × Fin k // e.1 < e.2 } :=
  (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype]
    exact card_pairsSet k)).symm

noncomputable def pI (k : ℕ) (e : Fin (k.choose 2)) : Fin k := (pairEquiv k e).1.1
noncomputable def pJ (k : ℕ) (e : Fin (k.choose 2)) : Fin k := (pairEquiv k e).1.2
lemma pLt (k : ℕ) (e : Fin (k.choose 2)) : pI k e < pJ k e := (pairEquiv k e).2

lemma pairEquiv_inj {k : ℕ} {e1 e2 : Fin (k.choose 2)}
    (h1 : pI k e1 = pI k e2) (h2 : pJ k e1 = pJ k e2) : e1 = e2 := by
  apply (pairEquiv k).injective
  apply Subtype.ext
  exact Prod.ext h1 h2

def weight {n : ℕ} (x : Fin n → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => x i = true)).card

lemma weight_zeroV (n : ℕ) : weight (zeroV n) = 0 := by
  simp [weight, zeroV]

lemma weight_unitV {n : ℕ} (a : Fin n) : weight (unitV a) = 1 := by
  have hf : (Finset.univ : Finset (Fin n)).filter (fun i => unitV a i = true) = {a} := by
    ext i; simp [unitV]
  rw [weight, hf, Finset.card_singleton]

lemma weight_pairV {n : ℕ} {a b : Fin n} (hab : a ≠ b) : weight (pairV a b) = 2 := by
  have hf : (Finset.univ : Finset (Fin n)).filter (fun i => pairV a b i = true) = {a, b} := by
    ext i; simp [pairV]
  rw [weight, hf, Finset.card_pair hab]

lemma unitV_inj {n : ℕ} {a b : Fin n} (h : unitV a = unitV b) : a = b := by
  have ha := congrFun h a
  simp [unitV] at ha
  exact ha

lemma pairV_eq_of_lt {n : ℕ} {a b c d : Fin n} (hab : a < b) (hcd : c < d)
    (h : pairV a b = pairV c d) : a = c ∧ b = d := by
  have ha : a = c ∨ a = d := by
    have h1 := congrFun h a
    simp [pairV] at h1
    exact h1
  have hb : b = c ∨ b = d := by
    have h1 := congrFun h b
    simp [pairV] at h1
    exact h1
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · exact absurd hab (lt_irrefl _)
    · exact ⟨rfl, rfl⟩
  · rcases hb with rfl | rfl
    · exact absurd (lt_trans hab hcd) (lt_irrefl _)
    · exact absurd hab (lt_irrefl _)

lemma card_filter_subset_between {α : Type*} [Fintype α] [DecidableEq α]
    (E Em : Finset α) (hsub : Em ⊆ E) (q : ℕ) :
    ((Finset.univ : Finset (Finset α)).filter (fun A => A.card = q ∧ Em ⊆ A ∧ A ⊆ E)).card =
      if Em.card ≤ q then (E.card - Em.card).choose (q - Em.card) else 0 := by
  by_cases hle : Em.card ≤ q
  · simp only [hle, ite_true]
    have hbij :
        ((Finset.univ : Finset (Finset α)).filter (fun A => A.card = q ∧ Em ⊆ A ∧ A ⊆ E)).card =
        ((E \ Em).powersetCard (q - Em.card)).card := by
      apply Finset.card_bij (fun A _ => A \ Em)
      · intro A hA
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.sdiff_subset_sdiff hA.2.2 (Finset.Subset.refl _), ?_⟩
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hA.2.1, hA.1]
      · intro A1 hA1 A2 hA2 heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA1 hA2
        have h1 : A1 = Em ∪ (A1 \ Em) := (Finset.union_sdiff_of_subset hA1.2.1).symm
        have h2 : A2 = Em ∪ (A2 \ Em) := (Finset.union_sdiff_of_subset hA2.2.1).symm
        rw [h1, h2, heq]
      · intro B hB
        rw [Finset.mem_powersetCard] at hB
        have hdisj : Disjoint Em B := by
          rw [Finset.disjoint_left]
          intro x hxEm hxB
          exact (Finset.mem_sdiff.mp (hB.1 hxB)).2 hxEm
        refine ⟨Em ∪ B, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, Finset.subset_union_left,
            Finset.union_subset hsub (Finset.Subset.trans hB.1 Finset.sdiff_subset)⟩
          rw [Finset.card_union_of_disjoint hdisj, hB.2]
          omega
        · exact Finset.union_sdiff_cancel_left hdisj
    rw [hbij, Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  · simp only [hle, ite_false]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro A _ hA
    have := Finset.card_le_card hA.2.1
    omega

theorem main_proof :
    ∀ k : ℕ,
      let K := Fin k
      let p := k.choose 2
      let n := 2+2*k+2*p
      let h := 4+3*k+6*p
      let V := Fin n → Bool
      let colors := K → Fin 3
      let edges := fun (g : K → K → Bool) => (Finset.univ : Finset (K × K)).filter
        (fun e => e.1 < e.2 ∧ g e.1 e.2 = true)
      let Circ := PEqualNP.CircuitLowerBounds.Circuit
      let fits := fun (C : Circ) => PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
        (∀ u ∈ C.gates, u.inputs.length ≤ 2 ∧
          (u.op = .and ∨ u.op = .or ∨ u.op = .mod 2 ∨ (u.op = .not ∧ u.inputs.length = 1))) ∧
        C.gates.countP (fun u => @decide
          ((u.op = .and ∨ u.op = .or) ∧ u.inputs.length = 2) (Classical.propDecidable _)) ≤ 1
      let rep := fun (f : V → Bool) => ∃ C : Circ, fits C ∧ ∀ x : V, f x = C.eval (List.ofFn x)
      ∃ (X : Fin h → V) (S : Finset (Fin h)) (base : Fin h → Bool)
        (ask : Fin h → Option (K × K)) (decode : (V → Bool) → colors),
        Function.Injective X ∧ S.card = p ∧
        (∀ t, ((Finset.univ : Finset (Fin n)).filter (fun i => X t i)).card ≤ 2) ∧
        (∀ t ∈ S, ask t = none ∧ base t = false) ∧
        (∀ t i j, ask t = some (i,j) → t ∉ S ∧ i < j) ∧
        (∀ i j : K, i < j → ∃! t, ask t = some (i,j)) ∧
        ∀ g : K → K → Bool,
          let m := (edges g).card
          let d := fun (c : colors) => ((edges g).filter (fun e => c e.1 = c e.2)).card
          let label := fun t => (ask t).elim (base t) (fun ij => g ij.1 ij.2)
          let err := fun (f : V → Bool) => ∑ t : Fin h,
            if f (X t) = label t then 0 else if t ∈ S then 1 else p+1
          (∀ (c : colors) (q : ℕ), q ≤ p →
            ((Finset.univ : Finset (V → Bool)).filter (fun f => @decide
              (rep f ∧ decode f = c ∧ err f = q) (Classical.propDecidable _))).card =
              if d c ≤ q then 2^(k+(p-m)+d c) * (m-d c).choose (q-d c) else 0) ∧
          ((Finset.univ : Finset (V → Bool)).filter (fun f => @decide
            (rep f ∧ ∀ t, f (X t) = label t) (Classical.propDecidable _))).card =
            2^(k+(p-m)) * ((Finset.univ : Finset colors).filter (fun c => d c = 0)).card := by
  intro k
  dsimp only
  set p := k.choose 2
  set n := 2 + 2 * k + 2 * p
  set h := 4 + 3 * k + 6 * p
  let K := Fin k
  let V := Fin n → Bool
  let colors := K → Fin 3
  let r0 : Fin n := ⟨0, by omega⟩
  let r1 : Fin n := ⟨1, by omega⟩
  let uC : K → Fin n := fun i => ⟨2 + i.val, by omega⟩
  let wC : K → Fin n := fun i => ⟨2 + k + i.val, by omega⟩
  let yC : Fin p → Fin n := fun e => ⟨2 + 2 * k + e.val, by omega⟩
  let zC : Fin p → Fin n := fun e => ⟨2 + 2 * k + p + e.val, by omega⟩
  let tZero : Fin h := ⟨0, by omega⟩
  let tUnit : Fin n → Fin h := fun s => ⟨1 + s.val, by omega⟩
  let tAnchor : Fin h := ⟨3 + 2 * k + 2 * p, by omega⟩
  let tVert : K → Fin h := fun i => ⟨4 + 2 * k + 2 * p + i.val, by omega⟩
  let tAsk : Fin p → Fin h := fun e => ⟨4 + 3 * k + 2 * p + e.val, by omega⟩
  let tUY : Fin p → Fin h := fun e => ⟨4 + 3 * k + 3 * p + e.val, by omega⟩
  let tYZ : Fin p → Fin h := fun e => ⟨4 + 3 * k + 4 * p + e.val, by omega⟩
  let tS : Fin p → Fin h := fun e => ⟨4 + 3 * k + 5 * p + e.val, by omega⟩
  let X : Fin h → V := fun t =>
    if h0 : t.val = 0 then zeroV n
    else if h1 : t.val < 3 + 2 * k + 2 * p then unitV ⟨t.val - 1, by omega⟩
    else if h2 : t.val = 3 + 2 * k + 2 * p then pairV r0 r1
    else if h3 : t.val < 4 + 3 * k + 2 * p then
      let i : K := ⟨t.val - (4 + 2 * k + 2 * p), by omega⟩
      pairV (uC i) (wC i)
    else if h4 : t.val < 4 + 3 * k + 3 * p then
      let e : Fin p := ⟨t.val - (4 + 3 * k + 2 * p), by omega⟩
      pairV (uC (pI k e)) (zC e)
    else if h5 : t.val < 4 + 3 * k + 4 * p then
      let e : Fin p := ⟨t.val - (4 + 3 * k + 3 * p), by omega⟩
      pairV (uC (pI k e)) (yC e)
    else if h6 : t.val < 4 + 3 * k + 5 * p then
      let e : Fin p := ⟨t.val - (4 + 3 * k + 4 * p), by omega⟩
      pairV (yC e) (zC e)
    else
      let e : Fin p := ⟨t.val - (4 + 3 * k + 5 * p), by omega⟩
      pairV (uC (pJ k e)) (zC e)
  let S : Finset (Fin h) := Finset.univ.image tS
  let base : Fin h → Bool := fun t =>
    if t.val = 3 + 2 * k + 2 * p then true
    else if 4 + 2 * k + 2 * p ≤ t.val ∧ t.val < 4 + 3 * k + 2 * p then true
    else if 4 + 3 * k + 3 * p ≤ t.val ∧ t.val < 4 + 3 * k + 4 * p then true
    else false
  let ask : Fin h → Option (K × K) := fun t =>
    if h4 : 4 + 3 * k + 2 * p ≤ t.val ∧ t.val < 4 + 3 * k + 3 * p then
      let e : Fin p := ⟨t.val - (4 + 3 * k + 2 * p), by omega⟩
      some (pI k e, pJ k e)
    else none
  let decode : (V → Bool) → colors := fun f i =>
    vecToColor (f (pairV r1 (uC i)), f (pairV r0 (uC i)))
  have hX_zero : X tZero = zeroV n := by simp [X, tZero]
  have hX_unit : ∀ s : Fin n, X (tUnit s) = unitV s := by
    intro s
    have hlt : 1 + s.val < 3 + 2 * k + 2 * p := by omega
    have hne : 1 + s.val ≠ 0 := by omega
    simp only [X, tUnit, hne, ↓reduceDIte, hlt]
    congr 1; ext; simp
  have hX_anchor : X tAnchor = pairV r0 r1 := by
    have h1 : 3 + 2 * k + 2 * p ≠ 0 := by omega
    have h2 : ¬ (3 + 2 * k + 2 * p < 3 + 2 * k + 2 * p) := by omega
    simp only [X, tAnchor, h1, h2, ↓reduceDIte]
  have hX_vert : ∀ i : K, X (tVert i) = pairV (uC i) (wC i) := by
    intro i
    have h0 : 4 + 2 * k + 2 * p + i.val ≠ 0 := by omega
    have h1 : ¬ (4 + 2 * k + 2 * p + i.val < 3 + 2 * k + 2 * p) := by omega
    have h2 : 4 + 2 * k + 2 * p + i.val ≠ 3 + 2 * k + 2 * p := by omega
    have h3 : 4 + 2 * k + 2 * p + i.val < 4 + 3 * k + 2 * p := by omega
    simp only [X, tVert, h0, h1, h2, h3, ↓reduceDIte]
    have hi : (⟨4 + 2 * k + 2 * p + i.val - (4 + 2 * k + 2 * p), by omega⟩ : K) = i := by
      ext; simp
    rw [hi]
  have hX_ask : ∀ e : Fin p, X (tAsk e) = pairV (uC (pI k e)) (zC e) := by
    intro e
    have h0 : 4 + 3 * k + 2 * p + e.val ≠ 0 := by omega
    have h1 : ¬ (4 + 3 * k + 2 * p + e.val < 3 + 2 * k + 2 * p) := by omega
    have h2 : 4 + 3 * k + 2 * p + e.val ≠ 3 + 2 * k + 2 * p := by omega
    have h3 : ¬ (4 + 3 * k + 2 * p + e.val < 4 + 3 * k + 2 * p) := by omega
    have h4 : 4 + 3 * k + 2 * p + e.val < 4 + 3 * k + 3 * p := by omega
    simp only [X, tAsk, h0, h1, h2, h3, h4, ↓reduceDIte]
    have he : (⟨4 + 3 * k + 2 * p + e.val - (4 + 3 * k + 2 * p), by omega⟩ : Fin p) = e := by
      ext; simp
    rw [he]
  have hX_uy : ∀ e : Fin p, X (tUY e) = pairV (uC (pI k e)) (yC e) := by
    intro e
    have h0 : 4 + 3 * k + 3 * p + e.val ≠ 0 := by omega
    have h1 : ¬ (4 + 3 * k + 3 * p + e.val < 3 + 2 * k + 2 * p) := by omega
    have h2 : 4 + 3 * k + 3 * p + e.val ≠ 3 + 2 * k + 2 * p := by omega
    have h3 : ¬ (4 + 3 * k + 3 * p + e.val < 4 + 3 * k + 2 * p) := by omega
    have h4 : ¬ (4 + 3 * k + 3 * p + e.val < 4 + 3 * k + 3 * p) := by omega
    have h5 : 4 + 3 * k + 3 * p + e.val < 4 + 3 * k + 4 * p := by omega
    simp only [X, tUY, h0, h1, h2, h3, h4, h5, ↓reduceDIte]
    have he : (⟨4 + 3 * k + 3 * p + e.val - (4 + 3 * k + 3 * p), by omega⟩ : Fin p) = e := by
      ext; simp
    rw [he]
  have hX_yz : ∀ e : Fin p, X (tYZ e) = pairV (yC e) (zC e) := by
    intro e
    have h0 : 4 + 3 * k + 4 * p + e.val ≠ 0 := by omega
    have h1 : ¬ (4 + 3 * k + 4 * p + e.val < 3 + 2 * k + 2 * p) := by omega
    have h2 : 4 + 3 * k + 4 * p + e.val ≠ 3 + 2 * k + 2 * p := by omega
    have h3 : ¬ (4 + 3 * k + 4 * p + e.val < 4 + 3 * k + 2 * p) := by omega
    have h4 : ¬ (4 + 3 * k + 4 * p + e.val < 4 + 3 * k + 3 * p) := by omega
    have h5 : ¬ (4 + 3 * k + 4 * p + e.val < 4 + 3 * k + 4 * p) := by omega
    have h6 : 4 + 3 * k + 4 * p + e.val < 4 + 3 * k + 5 * p := by omega
    simp only [X, tYZ, h0, h1, h2, h3, h4, h5, h6, ↓reduceDIte]
    have he : (⟨4 + 3 * k + 4 * p + e.val - (4 + 3 * k + 4 * p), by omega⟩ : Fin p) = e := by
      ext; simp
    rw [he]
  have hX_s : ∀ e : Fin p, X (tS e) = pairV (uC (pJ k e)) (zC e) := by
    intro e
    have h0 : 4 + 3 * k + 5 * p + e.val ≠ 0 := by omega
    have h1 : ¬ (4 + 3 * k + 5 * p + e.val < 3 + 2 * k + 2 * p) := by omega
    have h2 : 4 + 3 * k + 5 * p + e.val ≠ 3 + 2 * k + 2 * p := by omega
    have h3 : ¬ (4 + 3 * k + 5 * p + e.val < 4 + 3 * k + 2 * p) := by omega
    have h4 : ¬ (4 + 3 * k + 5 * p + e.val < 4 + 3 * k + 3 * p) := by omega
    have h5 : ¬ (4 + 3 * k + 5 * p + e.val < 4 + 3 * k + 4 * p) := by omega
    have h6 : ¬ (4 + 3 * k + 5 * p + e.val < 4 + 3 * k + 5 * p) := by omega
    simp only [X, tS, h0, h1, h2, h3, h4, h5, h6, ↓reduceDIte]
    have he : (⟨4 + 3 * k + 5 * p + e.val - (4 + 3 * k + 5 * p), by omega⟩ : Fin p) = e := by
      ext; simp
    rw [he]
  have htS_inj : Function.Injective tS := by
    intro e1 e2 he
    have := congrArg Fin.val he
    simp only [tS] at this
    exact Fin.ext (by omega)
  have hmemS : ∀ t : Fin h, t ∈ S ↔ 4 + 3 * k + 5 * p ≤ t.val := by
    intro t
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e, rfl⟩; simp [tS]
    · intro ht
      refine ⟨⟨t.val - (4 + 3 * k + 5 * p), by omega⟩, ?_⟩
      ext; simp [tS]; omega
  have hX_pair_lt : ∀ t : Fin h, 3 + 2 * k + 2 * p ≤ t.val →
      ∃ a b : Fin n, a < b ∧ X t = pairV a b ∧
        ((t = tAnchor ∧ a = r0 ∧ b = r1) ∨
         (∃ i : K, t = tVert i ∧ a = uC i ∧ b = wC i) ∨
         (∃ e : Fin p, t = tAsk e ∧ a = uC (pI k e) ∧ b = zC e) ∨
         (∃ e : Fin p, t = tUY e ∧ a = uC (pI k e) ∧ b = yC e) ∨
         (∃ e : Fin p, t = tYZ e ∧ a = yC e ∧ b = zC e) ∨
         (∃ e : Fin p, t = tS e ∧ a = uC (pJ k e) ∧ b = zC e)) := by
    intro t ht
    by_cases h2 : t.val = 3 + 2 * k + 2 * p
    · have ht' : t = tAnchor := Fin.ext h2
      rw [ht']
      exact ⟨r0, r1, by show (0 : ℕ) < 1; omega, hX_anchor, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · by_cases h3 : t.val < 4 + 3 * k + 2 * p
      · let i : K := ⟨t.val - (4 + 2 * k + 2 * p), by omega⟩
        have ht' : t = tVert i := Fin.ext (by simp [tVert, i]; omega)
        rw [ht']
        exact ⟨uC i, wC i, by show 2 + i.val < 2 + k + i.val; omega, hX_vert i,
          Or.inr (Or.inl ⟨i, rfl, rfl, rfl⟩)⟩
      · by_cases h4 : t.val < 4 + 3 * k + 3 * p
        · let e : Fin p := ⟨t.val - (4 + 3 * k + 2 * p), by omega⟩
          have ht' : t = tAsk e := Fin.ext (by simp [tAsk, e]; omega)
          rw [ht']
          exact ⟨uC (pI k e), zC e, by show 2 + (pI k e).val < 2 + 2 * k + p + e.val; omega,
            hX_ask e, Or.inr (Or.inr (Or.inl ⟨e, rfl, rfl, rfl⟩))⟩
        · by_cases h5 : t.val < 4 + 3 * k + 4 * p
          · let e : Fin p := ⟨t.val - (4 + 3 * k + 3 * p), by omega⟩
            have ht' : t = tUY e := Fin.ext (by simp [tUY, e]; omega)
            rw [ht']
            exact ⟨uC (pI k e), yC e, by show 2 + (pI k e).val < 2 + 2 * k + e.val; omega,
              hX_uy e, Or.inr (Or.inr (Or.inr (Or.inl ⟨e, rfl, rfl, rfl⟩)))⟩
          · by_cases h6 : t.val < 4 + 3 * k + 5 * p
            · let e : Fin p := ⟨t.val - (4 + 3 * k + 4 * p), by omega⟩
              have ht' : t = tYZ e := Fin.ext (by simp [tYZ, e]; omega)
              rw [ht']
              exact ⟨yC e, zC e, by show 2 + 2 * k + e.val < 2 + 2 * k + p + e.val; omega,
                hX_yz e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, rfl, rfl, rfl⟩))))⟩
            · let e : Fin p := ⟨t.val - (4 + 3 * k + 5 * p), by omega⟩
              have ht' : t = tS e := Fin.ext (by simp [tS, e]; omega)
              rw [ht']
              exact ⟨uC (pJ k e), zC e, by show 2 + (pJ k e).val < 2 + 2 * k + p + e.val; omega,
                hX_s e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, rfl, rfl, rfl⟩))))⟩
  have hwt_X : ∀ t : Fin h,
      (t.val = 0 → weight (X t) = 0) ∧
      (0 < t.val ∧ t.val < 3 + 2 * k + 2 * p → weight (X t) = 1) ∧
      (3 + 2 * k + 2 * p ≤ t.val → weight (X t) = 2) := by
    intro t
    refine ⟨fun h0 => ?_, fun ⟨h0, h1⟩ => ?_, fun h2 => ?_⟩
    · have ht' : t = tZero := Fin.ext h0; rw [ht', hX_zero, weight_zeroV]
    · let s : Fin n := ⟨t.val - 1, by omega⟩
      have ht' : t = tUnit s := Fin.ext (by simp [tUnit, s]; omega)
      rw [ht', hX_unit s, weight_unitV]
    · obtain ⟨a, b, hab, hXt, _⟩ := hX_pair_lt t h2
      rw [hXt, weight_pairV (ne_of_lt hab)]
  refine ⟨X, S, base, ask, decode, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t1 t2 heq
    have hw := congrArg weight heq
    by_cases h10 : t1.val = 0
    · have hw1 : weight (X t1) = 0 := (hwt_X t1).1 h10
      by_cases h20 : t2.val = 0
      · exact Fin.ext (by omega)
      · by_cases h21 : t2.val < 3 + 2 * k + 2 * p
        · have hw2 := (hwt_X t2).2.1 ⟨by omega, h21⟩; omega
        · have hw2 := (hwt_X t2).2.2 (by omega); omega
    · by_cases h11 : t1.val < 3 + 2 * k + 2 * p
      · have hw1 := (hwt_X t1).2.1 ⟨by omega, h11⟩
        by_cases h20 : t2.val = 0
        · have hw2 := (hwt_X t2).1 h20; omega
        · by_cases h21 : t2.val < 3 + 2 * k + 2 * p
          · let s1 : Fin n := ⟨t1.val - 1, by omega⟩
            let s2 : Fin n := ⟨t2.val - 1, by omega⟩
            have ht1 : t1 = tUnit s1 := Fin.ext (by simp [tUnit, s1]; omega)
            have ht2 : t2 = tUnit s2 := Fin.ext (by simp [tUnit, s2]; omega)
            rw [ht1, ht2, hX_unit s1, hX_unit s2] at heq
            have hs := unitV_inj heq
            rw [ht1, ht2, hs]
          · have hw2 := (hwt_X t2).2.2 (by omega); omega
      · have hw1 := (hwt_X t1).2.2 (by omega)
        have h22 : 3 + 2 * k + 2 * p ≤ t2.val := by
          by_contra hlt
          by_cases h20 : t2.val = 0
          · have hw2 := (hwt_X t2).1 h20; omega
          · have hw2 := (hwt_X t2).2.1 ⟨by omega, by omega⟩; omega
        obtain ⟨a1, b1, hab1, hX1, hc1⟩ := hX_pair_lt t1 (by omega)
        obtain ⟨a2, b2, hab2, hX2, hc2⟩ := hX_pair_lt t2 h22
        rw [hX1, hX2] at heq
        obtain ⟨ha, hb⟩ := pairV_eq_of_lt hab1 hab2 heq
        have hav := congrArg Fin.val ha
        have hbv := congrArg Fin.val hb
        rcases hc1 with ⟨rfl, rfl, rfl⟩ | ⟨i1, rfl, rfl, rfl⟩ | ⟨e1, rfl, rfl, rfl⟩ |
          ⟨e1, rfl, rfl, rfl⟩ | ⟨e1, rfl, rfl, rfl⟩ | ⟨e1, rfl, rfl, rfl⟩ <;>
        rcases hc2 with ⟨rfl, rfl, rfl⟩ | ⟨i2, rfl, rfl, rfl⟩ | ⟨e2, rfl, rfl, rfl⟩ |
          ⟨e2, rfl, rfl, rfl⟩ | ⟨e2, rfl, rfl, rfl⟩ | ⟨e2, rfl, rfl, rfl⟩
        all_goals
          try rfl
          try (simp only [r0, r1, uC, wC, yC, zC] at hav hbv; omega)
        · have hi : i1 = i2 := Fin.ext (by simp only [uC] at hav; omega)
          subst hi; rfl
        · have he : e1 = e2 := Fin.ext (by simp only [zC] at hbv; omega)
          subst he; rfl
        · have he : e1 = e2 := Fin.ext (by simp only [zC] at hbv; omega)
          subst he
          have hij : pI k e1 = pJ k e1 := Fin.ext (by simp only [uC] at hav; omega)
          exact absurd hij (ne_of_lt (pLt k e1))
        · have he : e1 = e2 := Fin.ext (by simp only [yC] at hbv; omega)
          subst he; rfl
        · have he : e1 = e2 := Fin.ext (by simp only [yC] at hav; omega)
          subst he; rfl
        · have he : e1 = e2 := Fin.ext (by simp only [zC] at hbv; omega)
          subst he
          have hij : pJ k e1 = pI k e1 := Fin.ext (by simp only [uC] at hav; omega)
          exact absurd hij.symm (ne_of_lt (pLt k e1))
        · have he : e1 = e2 := Fin.ext (by simp only [zC] at hbv; omega)
          subst he; rfl
  · rw [Finset.card_image_of_injective _ htS_inj, Finset.card_univ, Fintype.card_fin]
  · intro t
    change weight (X t) ≤ 2
    by_cases h0 : t.val = 0
    · rw [(hwt_X t).1 h0]; omega
    · by_cases h1 : t.val < 3 + 2 * k + 2 * p
      · rw [(hwt_X t).2.1 ⟨by omega, h1⟩]; omega
      · rw [(hwt_X t).2.2 (by omega)]
  · intro t ht
    rw [hmemS] at ht
    constructor
    · simp only [ask]
      rw [dif_neg (by omega)]
    · simp only [base]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · intro t i j hask
    simp only [ask] at hask
    split_ifs at hask with h4
    simp only [Option.some.injEq, Prod.mk.injEq] at hask
    rcases hask with ⟨rfl, rfl⟩
    refine ⟨?_, pLt k _⟩
    rw [hmemS]; omega
  · intro i j hij
    let e : Fin p := (pairEquiv k).symm ⟨(i, j), hij⟩
    have hpI : pI k e = i := by
      unfold pI; simp [e]
    have hpJ : pJ k e = j := by
      unfold pJ; simp [e]
    refine ⟨tAsk e, ?_, ?_⟩
    · simp only [ask, tAsk]
      rw [dif_pos (by omega)]
      have he : (⟨4 + 3 * k + 2 * p + e.val - (4 + 3 * k + 2 * p), by omega⟩ : Fin p) = e := by
        ext; simp
      rw [he, hpI, hpJ]
    · intro t ht
      simp only [ask] at ht
      split_ifs at ht with h4
      simp only [Option.some.injEq, Prod.mk.injEq] at ht
      let e' : Fin p := ⟨t.val - (4 + 3 * k + 2 * p), by omega⟩
      have heq : e' = e := pairEquiv_inj (by rw [ht.1, hpI]) (by rw [ht.2, hpJ])
      ext
      have hv := congrArg Fin.val heq
      simp only [e'] at hv
      simp only [tAsk]
      omega
  · intro g
    set edgesG := (Finset.univ : Finset (K × K)).filter (fun e => e.1 < e.2 ∧ g e.1 e.2 = true)
    set m := edgesG.card
    let d : colors → ℕ := fun c => (edgesG.filter (fun e => c e.1 = c e.2)).card
    let label : Fin h → Bool := fun t => (ask t).elim (base t) (fun ij => g ij.1 ij.2)
    let err : (V → Bool) → ℕ := fun f => ∑ t : Fin h,
      if f (X t) = label t then 0 else if t ∈ S then 1 else p + 1
    let rep : (V → Bool) → Prop := fun f => ∃ C : Circuit,
      (ReadsBack n C ∧ (∀ u ∈ C.gates, legalOp u) ∧ nlCount C.gates ≤ 1) ∧
      ∀ x : V, f x = C.eval (List.ofFn x)
    have hlab_zero : label tZero = false := by
      simp only [label, ask, base, tZero]
      rw [dif_neg (by omega), Option.elim, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hlab_unit : ∀ s : Fin n, label (tUnit s) = false := by
      intro s
      simp only [label, ask, base, tUnit]
      rw [dif_neg (by omega), Option.elim, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hlab_anchor : label tAnchor = true := by
      simp only [label, ask, base, tAnchor]
      rw [dif_neg (by omega)]
      simp
    have hlab_vert : ∀ i : K, label (tVert i) = true := by
      intro i
      simp only [label, ask, base, tVert]
      rw [dif_neg (by omega), Option.elim, if_neg (by omega), if_pos (by omega)]
    have hlab_ask : ∀ e : Fin p, label (tAsk e) = g (pI k e) (pJ k e) := by
      intro e
      simp only [label, ask, tAsk]
      rw [dif_pos (by omega)]
      have he : (⟨4 + 3 * k + 2 * p + e.val - (4 + 3 * k + 2 * p), by omega⟩ : Fin p) = e := by
        ext; simp
      rw [he]
      rfl
    have hlab_uy : ∀ e : Fin p, label (tUY e) = true := by
      intro e
      simp only [label, ask, base, tUY]
      rw [dif_neg (by omega), Option.elim, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    have hlab_yz : ∀ e : Fin p, label (tYZ e) = false := by
      intro e
      simp only [label, ask, base, tYZ]
      rw [dif_neg (by omega), Option.elim, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hlab_s : ∀ e : Fin p, label (tS e) = false := by
      intro e
      simp only [label, ask, base, tS]
      rw [dif_neg (by omega), Option.elim, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have herr_low : ∀ f : V → Bool, err f ≤ p → ∀ t : Fin h, t ∉ S → f (X t) = label t := by
      intro f hf t htS
      by_contra hne
      have hterm : p + 1 ≤
          (if f (X t) = label t then 0 else if t ∈ S then 1 else p + 1) := by
        simp [hne, htS]
      have hle := Finset.single_le_sum (f := fun t' : Fin h =>
        if f (X t') = label t' then 0 else if t' ∈ S then 1 else p + 1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      change (if f (X t) = label t then 0 else if t ∈ S then 1 else p + 1) ≤ err f at hle
      omega
    have herr_eq_cardS : ∀ f : V → Bool, (∀ t : Fin h, t ∉ S → f (X t) = label t) →
        err f = (Finset.univ.filter (fun e : Fin p => f (X (tS e)) = true)).card := by
      intro f hmatch
      unfold err
      rw [← Finset.sum_subset (Finset.subset_univ S)]
      · rw [Finset.sum_image (fun e1 _ e2 _ he => htS_inj he)]
        have hconv : ∀ e : Fin p,
            (if f (X (tS e)) = label (tS e) then 0 else if tS e ∈ S then 1 else p + 1) =
            if f (X (tS e)) = true then 1 else 0 := by
          intro e
          have hm : tS e ∈ S := Finset.mem_image_of_mem tS (Finset.mem_univ e)
          rw [hlab_s e, if_pos hm]
          cases f (X (tS e)) <;> simp
        simp_rw [hconv, Finset.sum_boole, Nat.cast_id]
      · intro t _ htS
        rw [if_pos (hmatch t htS)]
    have hE_card : (Finset.univ.filter (fun e : Fin p => g (pI k e) (pJ k e) = true)).card = m := by
      apply Finset.card_bij (fun e _ => (pI k e, pJ k e))
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
        simp only [edgesG, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨pLt k e, he⟩
      · intro e1 _ e2 _ heq
        simp only [Prod.mk.injEq] at heq
        exact pairEquiv_inj heq.1 heq.2
      · intro b hb
        simp only [edgesG, Finset.mem_filter, Finset.mem_univ, true_and] at hb
        let e : Fin p := (pairEquiv k).symm ⟨b, hb.1⟩
        have hpe : (pI k e, pJ k e) = b := by
          unfold pI pJ; simp [e]
        refine ⟨e, ?_, hpe⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [show pI k e = b.1 from congrArg Prod.fst hpe,
            show pJ k e = b.2 from congrArg Prod.snd hpe]
        exact hb.2
    have hEm_card : ∀ c : colors,
        ((Finset.univ.filter (fun e : Fin p => g (pI k e) (pJ k e) = true)).filter
          (fun e => c (pI k e) = c (pJ k e))).card = d c := by
      intro c
      apply Finset.card_bij (fun e _ => (pI k e, pJ k e))
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
        simp only [edgesG, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨pLt k e, he.1⟩, he.2⟩
      · intro e1 _ e2 _ heq
        simp only [Prod.mk.injEq] at heq
        exact pairEquiv_inj heq.1 heq.2
      · intro b hb
        simp only [edgesG, Finset.mem_filter, Finset.mem_univ, true_and] at hb
        let e : Fin p := (pairEquiv k).symm ⟨b, hb.1.1⟩
        have hpe : (pI k e, pJ k e) = b := by
          unfold pI pJ; simp [e]
        refine ⟨e, ?_, hpe⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [show pI k e = b.1 from congrArg Prod.fst hpe,
            show pJ k e = b.2 from congrArg Prod.snd hpe]
        exact ⟨hb.1.2, hb.2⟩
    let assemble : colors → (K → F2 × F2) → (Fin p → (F2 × F2) × (F2 × F2)) → (Fin n → F2 × F2) :=
      fun c vw vyz s =>
        if h0 : s.val = 0 then (1, 0)
        else if h1 : s.val = 1 then (0, 1)
        else if h2 : s.val < 2 + k then colorToVec (c ⟨s.val - 2, by omega⟩)
        else if h3 : s.val < 2 + 2 * k then vw ⟨s.val - (2 + k), by omega⟩
        else if h4 : s.val < 2 + 2 * k + p then (vyz ⟨s.val - (2 + 2 * k), by omega⟩).1
        else (vyz ⟨s.val - (2 + 2 * k + p), by omega⟩).2
    have hass_r0 : ∀ c vw vyz, assemble c vw vyz r0 = (1, 0) := by
      intro c vw vyz; simp [assemble, r0]
    have hass_r1 : ∀ c vw vyz, assemble c vw vyz r1 = (0, 1) := by
      intro c vw vyz; simp [assemble, r1]
    have hass_u : ∀ c vw vyz (i : K), assemble c vw vyz (uC i) = colorToVec (c i) := by
      intro c vw vyz i
      simp only [assemble, uC]
      rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
      congr 2; ext; simp
    have hass_w : ∀ c vw vyz (i : K), assemble c vw vyz (wC i) = vw i := by
      intro c vw vyz i
      simp only [assemble, wC]
      rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
      congr 1; ext; simp
    have hass_y : ∀ c vw vyz (e : Fin p), assemble c vw vyz (yC e) = (vyz e).1 := by
      intro c vw vyz e
      simp only [assemble, yC]
      rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega),
        dif_pos (by omega)]
      congr 2; ext; simp
    have hass_z : ∀ c vw vyz (e : Fin p), assemble c vw vyz (zC e) = (vyz e).2 := by
      intro c vw vyz e
      simp only [assemble, zC]
      rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega),
        dif_neg (by omega)]
      congr 2; ext; simp
    have hfirst : ∀ (c : colors) (q : ℕ), q ≤ p →
        ((Finset.univ : Finset (V → Bool)).filter (fun f => @decide
          (rep f ∧ decode f = c ∧ err f = q) (Classical.propDecidable _))).card =
          if d c ≤ q then 2 ^ (k + (p - m) + d c) * (m - d c).choose (q - d c) else 0 := by
      intro c q hqp
      let validW : Finset (K → F2 × F2) :=
        Finset.univ.filter (fun vw => ∀ i : K, det2 (colorToVec (c i)) (vw i) = 1)
      let validYZ : Finset (Fin p → (F2 × F2) × (F2 × F2)) :=
        Finset.univ.filter (fun vyz =>
          (∀ e : Fin p, pairValid (c (pI k e)) (g (pI k e) (pJ k e)) (vyz e) = true) ∧
          (Finset.univ.filter (fun e : Fin p => pairErr (c (pJ k e)) (vyz e) = true)).card = q)
      have hcard_bij :
          ((Finset.univ : Finset (V → Bool)).filter (fun f => @decide
            (rep f ∧ decode f = c ∧ err f = q) (Classical.propDecidable _))).card =
          (validW ×ˢ validYZ).card := by
        symm
        apply Finset.card_bij (fun p' _ => quadFun (assemble c p'.1 p'.2))
        · rintro ⟨vw, vyz⟩ hp'
          simp only [Finset.mem_product, validW, validYZ, Finset.mem_filter, Finset.mem_univ,
            true_and] at hp'
          rcases hp' with ⟨hvw, hvyz_ok, hvyz_err⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
          set v := assemble c vw vyz
          have hv_r0 : v r0 = (1, 0) := hass_r0 c vw vyz
          have hv_r1 : v r1 = (0, 1) := hass_r1 c vw vyz
          have hv_u : ∀ i : K, v (uC i) = colorToVec (c i) := hass_u c vw vyz
          have hv_w : ∀ i : K, v (wC i) = vw i := hass_w c vw vyz
          have hv_y : ∀ e : Fin p, v (yC e) = (vyz e).1 := hass_y c vw vyz
          have hv_z : ∀ e : Fin p, v (zC e) = (vyz e).2 := hass_z c vw vyz
          have hmatch : ∀ t : Fin h, t ∉ S → quadFun v (X t) = label t := by
            intro t htS
            rw [hmemS] at htS
            by_cases h0 : t.val = 0
            · have ht' : t = tZero := Fin.ext h0
              rw [ht', hX_zero, hlab_zero, quadFun_zero]
            · by_cases h1 : t.val < 3 + 2 * k + 2 * p
              · let s : Fin n := ⟨t.val - 1, by omega⟩
                have ht' : t = tUnit s := Fin.ext (by simp [tUnit, s]; omega)
                rw [ht', hX_unit s, hlab_unit s, quadFun_unit]
              · obtain ⟨a, b, _, _, hcases⟩ := hX_pair_lt t (by omega)
                rcases hcases with ⟨rfl, _, _⟩ | ⟨i, rfl, _, _⟩ | ⟨e, rfl, _, _⟩ |
                  ⟨e, rfl, _, _⟩ | ⟨e, rfl, _, _⟩ | ⟨e, rfl, _, _⟩
                · apply b2z_inj
                  rw [hX_anchor, hlab_anchor, quadFun_pair, hv_r0, hv_r1]
                  rfl
                · apply b2z_inj
                  rw [hX_vert i, hlab_vert i, quadFun_pair, hv_u, hv_w, hvw i, b2z_true]
                · apply b2z_inj
                  rw [hX_ask e, hlab_ask e, quadFun_pair, hv_u, hv_z]
                  have he := hvyz_ok e
                  simp only [pairValid, decide_eq_true_eq] at he
                  exact he.1
                · apply b2z_inj
                  rw [hX_uy e, hlab_uy e, quadFun_pair, hv_u, hv_y, b2z_true]
                  have he := hvyz_ok e
                  simp only [pairValid, decide_eq_true_eq] at he
                  exact he.2.1
                · apply b2z_inj
                  rw [hX_yz e, hlab_yz e, quadFun_pair, hv_y, hv_z, b2z_false]
                  have he := hvyz_ok e
                  simp only [pairValid, decide_eq_true_eq] at he
                  exact he.2.2
                · exfalso; simp [tS] at htS
          refine ⟨quadFun_rep v, ?_, ?_⟩
          · funext i
            dsimp only [decode]
            have h1 : quadFun v (pairV r1 (uC i)) = decide ((colorToVec (c i)).1 = 1) := by
              apply b2z_inj
              rw [quadFun_pair, hv_r1, hv_u, b2z_decide]
              simp [det2]
            have h2 : quadFun v (pairV r0 (uC i)) = decide ((colorToVec (c i)).2 = 1) := by
              apply b2z_inj
              rw [quadFun_pair, hv_r0, hv_u, b2z_decide]
              simp [det2]
            rw [h1, h2, vecToColor_colorToVec]
          · rw [herr_eq_cardS (quadFun v) hmatch]
            have hfilt : (Finset.univ.filter (fun e : Fin p => quadFun v (X (tS e)) = true)) =
                Finset.univ.filter (fun e : Fin p => pairErr (c (pJ k e)) (vyz e) = true) := by
              ext e
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairErr, decide_eq_true_eq]
              rw [hX_s e]
              constructor
              · intro ht
                have := quadFun_pair v (uC (pJ k e)) (zC e)
                rw [ht, b2z_true, hv_u, hv_z] at this
                exact this.symm
              · intro hd1
                apply b2z_inj
                rw [quadFun_pair, hv_u, hv_z, hd1, b2z_true]
            rw [hfilt, hvyz_err]
        · rintro ⟨vw1, vyz1⟩ _ ⟨vw2, vyz2⟩ _ heq
          have hv : assemble c vw1 vyz1 = assemble c vw2 vyz2 := by
            have h1 := extractVec_quadFun (hass_r0 c vw1 vyz1) (hass_r1 c vw1 vyz1)
            have h2 := extractVec_quadFun (hass_r0 c vw2 vyz2) (hass_r1 c vw2 vyz2)
            rw [← h1, ← h2, heq]
          refine Prod.ext (funext fun i => ?_) (funext fun e => ?_)
          · have := congrFun hv (wC i); rw [hass_w, hass_w] at this; exact this
          · have hy := congrFun hv (yC e); rw [hass_y, hass_y] at hy
            have hz := congrFun hv (zC e); rw [hass_z, hass_z] at hz
            exact Prod.ext hy hz
        · intro f hf
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hf
          rcases hf with ⟨hrep, hdec, herrq⟩
          have hmatch := herr_low f (by omega)
          have hz : f (zeroV n) = false := by
            have := hmatch tZero (by rw [hmemS]; simp [tZero])
            rwa [hX_zero, hlab_zero] at this
          have hu : ∀ s : Fin n, f (unitV s) = false := by
            intro s
            have := hmatch (tUnit s) (by rw [hmemS]; simp [tUnit]; omega)
            rwa [hX_unit s, hlab_unit s] at this
          have hanc : f (pairV r0 r1) = true := by
            have := hmatch tAnchor (by rw [hmemS]; simp [tAnchor]; omega)
            rwa [hX_anchor, hlab_anchor] at this
          obtain ⟨hvr0, hvr1, hfeq⟩ := calibrated_eq_quadFun hrep hz hu hanc
          set v := extractVec r0 r1 f
          have hv_vert : ∀ i : K, det2 (v (uC i)) (v (wC i)) = 1 := by
            intro i
            have := hmatch (tVert i) (by rw [hmemS]; simp [tVert]; omega)
            rw [hX_vert i, hlab_vert i, hfeq] at this
            have hp := quadFun_pair v (uC i) (wC i)
            rw [this, b2z_true] at hp
            exact hp.symm
          have hv_u : ∀ i : K, v (uC i) = colorToVec (c i) := by
            intro i
            have hne : v (uC i) ≠ (0, 0) := ne_zero_of_det2_eq_one (hv_vert i)
            have hci : vecToColor (decide ((v (uC i)).1 = 1), decide ((v (uC i)).2 = 1)) = c i := by
              have hdi := congrFun hdec i
              dsimp only [decode] at hdi
              have h1 : decide ((v (uC i)).1 = 1) = f (pairV r1 (uC i)) := by
                apply b2z_inj; rw [b2z_decide]; rfl
              have h2 : decide ((v (uC i)).2 = 1) = f (pairV r0 (uC i)) := by
                apply b2z_inj; rw [b2z_decide]; rfl
              rw [h1, h2]
              exact hdi
            rw [← hci]
            exact (colorToVec_vecToColor hne).symm
          let vw : K → F2 × F2 := fun i => v (wC i)
          let vyz : Fin p → (F2 × F2) × (F2 × F2) := fun e => (v (yC e), v (zC e))
          have hv_eq : assemble c vw vyz = v := by
            funext s
            by_cases h0 : s.val = 0
            · have hs : s = r0 := Fin.ext h0; rw [hs, hass_r0, hvr0]
            · by_cases h1 : s.val = 1
              · have hs : s = r1 := Fin.ext h1; rw [hs, hass_r1, hvr1]
              · by_cases h2 : s.val < 2 + k
                · let i : K := ⟨s.val - 2, by omega⟩
                  have hs : s = uC i := Fin.ext (by simp [uC, i]; omega)
                  rw [hs, hass_u, hv_u]
                · by_cases h3 : s.val < 2 + 2 * k
                  · let i : K := ⟨s.val - (2 + k), by omega⟩
                    have hs : s = wC i := Fin.ext (by simp [wC, i]; omega)
                    rw [hs, hass_w]
                  · by_cases h4 : s.val < 2 + 2 * k + p
                    · let e : Fin p := ⟨s.val - (2 + 2 * k), by omega⟩
                      have hs : s = yC e := Fin.ext (by simp [yC, e]; omega)
                      rw [hs, hass_y]
                    · let e : Fin p := ⟨s.val - (2 + 2 * k + p), by omega⟩
                      have hs : s = zC e := Fin.ext (by simp [zC, e]; omega)
                      rw [hs, hass_z]
          refine ⟨(vw, vyz), ?_, ?_⟩
          · simp only [Finset.mem_product, validW, validYZ, Finset.mem_filter, Finset.mem_univ,
              true_and]
            refine ⟨fun i => ?_, fun e => ?_, ?_⟩
            · rw [← hv_u i]; exact hv_vert i
            · simp only [pairValid, decide_eq_true_eq]
              refine ⟨?_, ?_, ?_⟩
              · have := hmatch (tAsk e) (by rw [hmemS]; simp [tAsk]; omega)
                rw [hX_ask e, hlab_ask e, hfeq] at this
                have hp := quadFun_pair v (uC (pI k e)) (zC e)
                rw [this, hv_u] at hp
                exact hp.symm
              · have := hmatch (tUY e) (by rw [hmemS]; simp [tUY]; omega)
                rw [hX_uy e, hlab_uy e, hfeq] at this
                have hp := quadFun_pair v (uC (pI k e)) (yC e)
                rw [this, b2z_true, hv_u] at hp
                exact hp.symm
              · have := hmatch (tYZ e) (by rw [hmemS]; simp [tYZ]; omega)
                rw [hX_yz e, hlab_yz e, hfeq] at this
                have hp := quadFun_pair v (yC e) (zC e)
                rw [this, b2z_false] at hp
                exact hp.symm
            · have hcard := herr_eq_cardS f hmatch
              rw [herrq] at hcard
              rw [hcard]
              congr 1
              ext e
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairErr, decide_eq_true_eq]
              rw [hX_s e, hfeq]
              constructor
              · intro hd1
                apply b2z_inj
                rw [quadFun_pair, hv_u, hd1, b2z_true]
              · intro ht
                have hp := quadFun_pair v (uC (pJ k e)) (zC e)
                rw [ht, b2z_true, hv_u] at hp
                exact hp.symm
          · rw [hv_eq, ← hfeq]
      have hcardW : validW.card = 2 ^ k := by
        have hpi : validW = Fintype.piFinset (fun i : K =>
            Finset.univ.filter (fun w : F2 × F2 => det2 (colorToVec (c i)) w = 1)) := by
          ext vw
          simp [validW, Fintype.mem_piFinset]
        rw [hpi, Fintype.card_piFinset]
        simp [card_vertex_w, K]
      let E : Finset (Fin p) := Finset.univ.filter (fun e : Fin p => g (pI k e) (pJ k e) = true)
      let Em : Finset (Fin p) := E.filter (fun e : Fin p => c (pI k e) = c (pJ k e))
      have hEc : E.card = m := hE_card
      have hEmc : Em.card = d c := hEm_card c
      have hEmsub : Em ⊆ E := Finset.filter_subset _ _
      have hcardYZ : validYZ.card =
          if d c ≤ q then 2 ^ ((p - m) + d c) * (m - d c).choose (q - d c) else 0 := by
        let Qset : Finset (Finset (Fin p)) :=
          (Finset.univ : Finset (Finset (Fin p))).filter (fun A => A.card = q)
        let errOf : (Fin p → (F2 × F2) × (F2 × F2)) → Finset (Fin p) :=
          fun vyz => Finset.univ.filter (fun e : Fin p => pairErr (c (pJ k e)) (vyz e) = true)
        have hfib : validYZ.card =
            ∑ A ∈ Qset, (validYZ.filter (fun vyz => errOf vyz = A)).card := by
          apply Finset.card_eq_sum_card_fiberwise
          intro vyz hvyz
          change vyz ∈ validYZ at hvyz
          change errOf vyz ∈ Qset
          simp only [validYZ, Finset.mem_filter, Finset.mem_univ, true_and] at hvyz
          simp only [Qset, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hvyz.2
        have hterm : ∀ A ∈ Qset, (validYZ.filter (fun vyz => errOf vyz = A)).card =
            if Em ⊆ A ∧ A ⊆ E then 2 ^ ((p - m) + d c) else 0 := by
          intro A hA
          simp only [Qset, Finset.mem_filter, Finset.mem_univ, true_and] at hA
          have hpi : validYZ.filter (fun vyz => errOf vyz = A) =
              Fintype.piFinset (fun e : Fin p =>
                Finset.univ.filter (fun yz : (F2 × F2) × (F2 × F2) =>
                  pairValid (c (pI k e)) (g (pI k e) (pJ k e)) yz = true ∧
                  pairErr (c (pJ k e)) yz = decide (e ∈ A))) := by
            ext vyz
            simp only [validYZ, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
            constructor
            · rintro ⟨⟨hok, _⟩, hAe⟩ e
              refine ⟨hok e, ?_⟩
              have hmem : e ∈ errOf vyz ↔ e ∈ A := by rw [hAe]
              simp only [errOf, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
              cases hpe : pairErr (c (pJ k e)) (vyz e)
              · simp only [hpe, Bool.false_eq_true, false_iff] at hmem
                simp [hmem]
              · simp only [hpe, true_iff] at hmem
                simp [hmem]
            · intro hall
              have hAe : errOf vyz = A := by
                ext e
                simp only [errOf, Finset.mem_filter, Finset.mem_univ, true_and]
                rw [(hall e).2]
                simp
              exact ⟨⟨fun e => (hall e).1, by change (errOf vyz).card = q; rw [hAe, hA]⟩, hAe⟩
          rw [hpi, Fintype.card_piFinset]
          by_cases hcond : Em ⊆ A ∧ A ⊆ E
          · rw [if_pos hcond]
            have hfac : ∀ e : Fin p,
                (Finset.univ.filter (fun yz : (F2 × F2) × (F2 × F2) =>
                  pairValid (c (pI k e)) (g (pI k e) (pJ k e)) yz = true ∧
                  pairErr (c (pJ k e)) yz = decide (e ∈ A))).card =
                if e ∈ (Finset.univ \ E) ∪ Em then 2 else 1 := by
              intro e
              by_cases hg : g (pI k e) (pJ k e) = true
              · have heE : e ∈ E := by simp [E, hg]
                rw [hg]
                by_cases hceq : c (pI k e) = c (pJ k e)
                · have heEm : e ∈ Em := by simp [Em, heE, hceq]
                  have heA : e ∈ A := hcond.1 heEm
                  have hmemU : e ∈ (Finset.univ \ E) ∪ Em := Finset.mem_union_right _ heEm
                  rw [if_pos hmemU, hceq, card_pair_true_eq]
                  simp [heA]
                · have heEm : e ∉ Em := by simp [Em, hceq]
                  have hmemU : e ∉ (Finset.univ \ E) ∪ Em := by simp [heE, heEm]
                  rw [if_neg hmemU]
                  exact card_pair_true_ne (c (pI k e)) (c (pJ k e)) hceq _
              · have hgf : g (pI k e) (pJ k e) = false := by
                  cases hgv : g (pI k e) (pJ k e)
                  · rfl
                  · exact absurd hgv hg
                have heE : e ∉ E := by simp [E, hgf]
                have heA : e ∉ A := fun h => heE (hcond.2 h)
                have hmemU : e ∈ (Finset.univ \ E) ∪ Em :=
                  Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, heE⟩)
                rw [hgf, if_pos hmemU, card_pair_false]
                simp [heA]
            simp_rw [hfac]
            rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
            have hflt : (Finset.univ.filter (fun e : Fin p => e ∈ (Finset.univ \ E) ∪ Em)) =
                (Finset.univ \ E) ∪ Em := by
              ext e; simp
            rw [hflt]
            have hdisj : Disjoint (Finset.univ \ E) Em := by
              rw [Finset.disjoint_left]
              intro e he1 he2
              exact (Finset.mem_sdiff.mp he1).2 (hEmsub he2)
            rw [Finset.card_union_of_disjoint hdisj,
                Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ E),
                Finset.card_univ, Fintype.card_fin, hEc, hEmc]
          · rw [if_neg hcond]
            rw [not_and_or] at hcond
            rcases hcond with hnotEm | hnotE
            · rw [Finset.not_subset] at hnotEm
              obtain ⟨e, heEm, henotA⟩ := hnotEm
              have heE : e ∈ E := hEmsub heEm
              simp only [Em, E, Finset.mem_filter, Finset.mem_univ, true_and] at heEm heE
              apply Finset.prod_eq_zero (Finset.mem_univ e)
              rw [heE, heEm.2, card_pair_true_eq]
              simp [henotA]
            · rw [Finset.not_subset] at hnotE
              obtain ⟨e, heA, henotE⟩ := hnotE
              have hgf : g (pI k e) (pJ k e) = false := by
                cases hgv : g (pI k e) (pJ k e)
                · rfl
                · exfalso; exact henotE (by simp [E, hgv])
              apply Finset.prod_eq_zero (Finset.mem_univ e)
              rw [hgf, card_pair_false]
              simp [heA]
        rw [hfib, Finset.sum_congr rfl hterm]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
        have hflt : Qset.filter (fun A => Em ⊆ A ∧ A ⊆ E) =
            (Finset.univ : Finset (Finset (Fin p))).filter
              (fun A => A.card = q ∧ Em ⊆ A ∧ A ⊆ E) := by
          ext A; simp [Qset, and_assoc]
        rw [hflt, card_filter_subset_between E Em hEmsub q, hEc, hEmc]
        split_ifs
        · ring
        · simp
      rw [hcard_bij, Finset.card_product, hcardW, hcardYZ]
      split_ifs
      · rw [← mul_assoc, ← pow_add, Nat.add_assoc]
      · simp
    refine ⟨hfirst, ?_⟩
    let exactSet : Finset (V → Bool) :=
      (Finset.univ : Finset (V → Bool)).filter (fun f => @decide
        (rep f ∧ ∀ t, f (X t) = label t) (Classical.propDecidable _))
    have hexact_iff : ∀ f : V → Bool, (∀ t : Fin h, f (X t) = label t) ↔ err f = 0 := by
      intro f
      unfold err
      rw [Finset.sum_eq_zero_iff]
      constructor
      · intro hall t _; rw [if_pos (hall t)]
      · intro h0 t
        have ht := h0 t (Finset.mem_univ t)
        by_contra hne
        rw [if_neg hne] at ht
        split_ifs at ht <;> omega
    have hpart : exactSet.card =
        ∑ c : colors, (exactSet.filter (fun f => decode f = c)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro f _; exact Finset.mem_univ _
    change exactSet.card = _
    rw [hpart]
    have hterm0 : ∀ c : colors, (exactSet.filter (fun f => decode f = c)).card =
        if d c = 0 then 2 ^ (k + (p - m)) else 0 := by
      intro c
      have hseteq : exactSet.filter (fun f => decode f = c) =
          (Finset.univ : Finset (V → Bool)).filter (fun f => @decide
            (rep f ∧ decode f = c ∧ err f = 0) (Classical.propDecidable _)) := by
        ext f
        simp only [exactSet, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
          hexact_iff]
        tauto
      rw [hseteq, hfirst c 0 (Nat.zero_le p)]
      by_cases hdc : d c = 0
      · simp [hdc]
      · have hnot : ¬ (d c ≤ 0) := by omega
        simp [hdc, hnot]
    simp_rw [hterm0]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]

end PEqualNP.Outside.L_meta_33673

theorem PEqualNP.Outside.L_meta_33673 : ∀ k : ℕ,
  let K := Fin k
  let p := k.choose 2
  let n := 2+2*k+2*p
  let h := 4+3*k+6*p
  let V := Fin n → Bool
  let colors := K → Fin 3
  let edges := fun (g : K → K → Bool) => (Finset.univ : Finset (K × K)).filter
    (fun e => e.1 < e.2 ∧ g e.1 e.2 = true)
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let fits := fun (C : Circ) => PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
    (∀ u ∈ C.gates, u.inputs.length ≤ 2 ∧
      (u.op = .and ∨ u.op = .or ∨ u.op = .mod 2 ∨ (u.op = .not ∧ u.inputs.length = 1))) ∧
    C.gates.countP (fun u => @decide
      ((u.op = .and ∨ u.op = .or) ∧ u.inputs.length = 2) (Classical.propDecidable _)) ≤ 1
  let rep := fun (f : V → Bool) => ∃ C : Circ, fits C ∧ ∀ x : V, f x = C.eval (List.ofFn x)
  ∃ (X : Fin h → V) (S : Finset (Fin h)) (base : Fin h → Bool)
    (ask : Fin h → Option (K × K)) (decode : (V → Bool) → colors),
    Function.Injective X ∧ S.card = p ∧
    (∀ t, ((Finset.univ : Finset (Fin n)).filter (fun i => X t i)).card ≤ 2) ∧
    (∀ t ∈ S, ask t = none ∧ base t = false) ∧
    (∀ t i j, ask t = some (i,j) → t ∉ S ∧ i < j) ∧
    (∀ i j : K, i < j → ∃! t, ask t = some (i,j)) ∧
    ∀ g : K → K → Bool,
      let m := (edges g).card
      let d := fun (c : colors) => ((edges g).filter (fun e => c e.1 = c e.2)).card
      let label := fun t => (ask t).elim (base t) (fun ij => g ij.1 ij.2)
      let err := fun (f : V → Bool) => ∑ t : Fin h,
        if f (X t) = label t then 0 else if t ∈ S then 1 else p+1
      (∀ (c : colors) (q : ℕ), q ≤ p →
        ((Finset.univ : Finset (V → Bool)).filter (fun f => @decide
          (rep f ∧ decode f = c ∧ err f = q) (Classical.propDecidable _))).card =
          if d c ≤ q then 2^(k+(p-m)+d c) * (m-d c).choose (q-d c) else 0) ∧
      ((Finset.univ : Finset (V → Bool)).filter (fun f => @decide
        (rep f ∧ ∀ t, f (X t) = label t) (Classical.propDecidable _))).card =
        2^(k+(p-m)) * ((Finset.univ : Finset colors).filter (fun c => d c = 0)).card :=
  PEqualNP.Outside.L_meta_33673.main_proof
