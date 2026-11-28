import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29782_aux

namespace CircuitProof

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Classical

abbrev F2 := ZMod 2

def legalGates (n : ℕ) (gs : List Gate) : Prop :=
  ReadsBack n ⟨gs, 0⟩ ∧
    ∀ h ∈ gs, h.inputs.length ≤ 2 ∧
      (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))

noncomputable def costGates (gs : List Gate) : ℕ :=
  gs.countP (fun h => @decide ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires x

def bitsOf (n : ℕ) (u : Fin n → F2) : List Bool :=
  List.ofFn (fun j : Fin n => decide (u j = 1))

lemma bitsOf_len (n : ℕ) (u : Fin n → F2) : (bitsOf n u).length = n := by
  simp [bitsOf]

lemma bitsOf_getD (n : ℕ) (u : Fin n → F2) (j : Fin n) :
    (bitsOf n u).getD j.val false = decide (u j = 1) := by
  simp [bitsOf, List.getD_eq_getElem?_getD, j.isLt]

lemma zmod2_add_decide (a b : F2) :
    decide (a + b = 1) = Bool.xor (decide (a = 1)) (decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

lemma zmod2_mul_decide (a b : F2) :
    decide (a * b = 1) = (decide (a = 1) && decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

lemma zmod2_bool_decide (b : Bool) :
    decide ((if b then (1 : F2) else 0) = 1) = b := by
  cases b <;> decide

lemma zmod2_cases (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_xor_zero_iff (b ow : Bool) (d : F2) :
    d + (if Bool.xor b ow then (1 : F2) else 0) = 0 ↔ b = Bool.xor ow (decide (d = 1)) := by
  cases b <;> cases ow <;> fin_cases d <;> decide

lemma zmod2_decide_bool (a : F2) :
    (if decide (a = 1) then (1 : F2) else 0) = a := by
  fin_cases a <;> rfl

lemma zmod2_sub_eq_add (a b : F2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

lemma zmod2_vec_sub_eq_add {k : ℕ} (x y : Fin k → F2) : x - y = x + y := by
  funext j; exact zmod2_sub_eq_add (x j) (y j)

lemma zmod2_vec_add_self {k : ℕ} (x : Fin k → F2) : x + x = 0 := by
  funext j
  have : x j + x j = 0 := by
    rcases zmod2_cases (x j) with h | h <;> rw [h] <;> decide
  exact this

lemma wiresOf_len (gs : List Gate) (x : List Bool) :
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
  rw [wiresOf_append, wiresOf_getD_lt gs2 (wiresOf gs1 x) (by rw [wiresOf_len]; exact hi)]

lemma wiresOf_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (wiresOf (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false) := by
  rw [wiresOf_append]
  set w := wiresOf gs x
  have hlen : w.length = x.length + gs.length := wiresOf_len gs x
  change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD (x.length + gs.length) false = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      show x.length + gs.length - w.length = 0 by omega]
  rfl

lemma wiresOf_snoc_last_eq {n : ℕ} (gs : List Gate) (g : Gate) (x : List Bool) (hx : x.length = n) :
    (wiresOf (gs ++ [g]) x).getD (n + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false) := by
  have h := wiresOf_snoc_last gs g x
  rw [hx] at h
  exact h

lemma readsBack_append {n : ℕ} {gs1 gs2 : List Gate}
    (h1 : ReadsBack n ⟨gs1, 0⟩)
    (h2 : ∀ j < gs2.length, ∀ i ∈ (gs2.getD j ⟨.or, []⟩).inputs, i < n + gs1.length + j) :
    ReadsBack n ⟨gs1 ++ gs2, 0⟩ := by
  intro j hj i hi
  simp only [gateAt] at hi
  simp only [List.length_append] at hj
  by_cases hlt : j < gs1.length
  · have hget : (gs1 ++ gs2).getD j ⟨.or, []⟩ = gs1.getD j ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    rw [hget] at hi
    exact h1 j hlt i hi
  · have hge : gs1.length ≤ j := by omega
    have hget : (gs1 ++ gs2).getD j ⟨.or, []⟩ = gs2.getD (j - gs1.length) ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
    rw [hget] at hi
    have := h2 (j - gs1.length) (by omega) i hi
    omega

lemma legalGates_snoc {n : ℕ} {gs : List Gate} {g : Gate}
    (hgs : legalGates n gs)
    (hback : ∀ i ∈ g.inputs, i < n + gs.length)
    (hshape : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) :
    legalGates n (gs ++ [g]) := by
  refine ⟨readsBack_append hgs.1 ?_, ?_⟩
  · intro j hj i hi
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some] at hi
    have := hback i hi
    omega
  · intro h hh
    rcases List.mem_append.mp hh with h1 | h2
    · exact hgs.2 h h1
    · simp only [List.mem_singleton] at h2; subst h2; exact hshape

lemma legalGates_prefix {n : ℕ} {gs : List Gate} {g : Gate}
    (h : legalGates n (gs ++ [g])) :
    legalGates n gs ∧
      (∀ i ∈ g.inputs, i < n + gs.length) ∧
      (g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) := by
  refine ⟨⟨?_, fun h' hh' => h.2 h' (List.mem_append_left _ hh')⟩, ?_, h.2 g (by simp)⟩
  · intro j hj i hi
    have hj0 : j < gs.length := hj
    have hj' : j < (gs ++ [g]).length := by simp; omega
    have hget : (gs ++ [g]).getD j ⟨.or, []⟩ = gs.getD j ⟨.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj0]
    have hi' : i ∈ (gateAt ⟨gs ++ [g], 0⟩ j).inputs := by
      change i ∈ ((gs ++ [g]).getD j ⟨.or, []⟩).inputs
      rw [hget]; exact hi
    exact h.1 j hj' i hi'
  · intro i hi
    have hj' : gs.length < (gs ++ [g]).length := by simp
    have hget : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
    exact h.1 gs.length hj' i (by simpa [gateAt, hget] using hi)

lemma costGates_append (gs1 gs2 : List Gate) :
    costGates (gs1 ++ gs2) = costGates gs1 + costGates gs2 := by
  unfold costGates; exact List.countP_append

lemma costGates_snoc_zero (gs : List Gate) (g : Gate)
    (h0 : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)) :
    costGates (gs ++ [g]) = costGates gs := by
  rw [costGates_append]
  unfold costGates
  simp [h0]

lemma costGates_snoc_one (gs : List Gate) (g : Gate)
    (h1 : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    costGates (gs ++ [g]) = costGates gs + 1 := by
  rw [costGates_append]
  unfold costGates
  simp [h1]

lemma addXor_step (t : ℕ) (gs : List Gate) (w1 w2 : ℕ)
    (hgs : legalGates t gs) (hw1 : w1 < t + gs.length) (hw2 : w2 < t + gs.length) :
    let gs' := gs ++ [⟨.mod 2, [w1, w2]⟩, ⟨.not, [t + gs.length]⟩]
    legalGates t gs' ∧
    costGates gs' = costGates gs ∧
    gs'.length = gs.length + 2 ∧
    ∀ x : List Bool, x.length = t →
      (wiresOf gs' x).getD (t + gs.length + 1) false =
        Bool.xor ((wiresOf gs x).getD w1 false) ((wiresOf gs x).getD w2 false) := by
  intro gs'
  have h1 : legalGates t (gs ++ [⟨.mod 2, [w1, w2]⟩]) := by
    apply legalGates_snoc hgs
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega
    · exact ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩
  have h2 : legalGates t ((gs ++ [⟨.mod 2, [w1, w2]⟩]) ++ [⟨.not, [t + gs.length]⟩]) := by
    apply legalGates_snoc h1
    · intro i hi; simp at hi; subst hi; simp
    · exact ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  have hgs'_eq : gs' = (gs ++ [⟨.mod 2, [w1, w2]⟩]) ++ [⟨.not, [t + gs.length]⟩] := by simp [gs']
  refine ⟨hgs'_eq ▸ h2, ?_, by simp [gs'], ?_⟩
  · rw [hgs'_eq,
        costGates_snoc_zero (gs ++ [(⟨.mod 2, [w1, w2]⟩ : Gate)]) (⟨.not, [t + gs.length]⟩ : Gate) (by simp),
        costGates_snoc_zero gs (⟨.mod 2, [w1, w2]⟩ : Gate) (by simp)]
  · intro x hx
    rw [hgs'_eq]
    have hidx : t + gs.length + 1 = x.length + (gs ++ [(⟨.mod 2, [w1, w2]⟩ : Gate)]).length := by simp; omega
    rw [hidx, wiresOf_snoc_last]
    have hidx1 : t + gs.length = x.length + gs.length := by omega
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    rw [hidx1, wiresOf_snoc_last]
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    cases (wiresOf gs x).getD w1 false <;> cases (wiresOf gs x).getD w2 false <;> decide

def addXorMany (t cWire : ℕ) (flag : ℕ → Bool) (old : ℕ → ℕ) :
    ℕ → List Gate → List Gate × (ℕ → ℕ)
  | 0, gs => (gs, old)
  | m + 1, gs =>
    let res := addXorMany t cWire flag old m gs
    let gs1 := res.1
    let f1 := res.2
    if flag m then
      (gs1 ++ [⟨.mod 2, [old m, cWire]⟩, ⟨.not, [t + gs1.length]⟩],
        fun u => if u = m then t + gs1.length + 1 else f1 u)
    else (gs1, f1)

lemma addXorMany_spec (t cWire : ℕ) (flag : ℕ → Bool) (old : ℕ → ℕ) :
    ∀ (m : ℕ) (gs : List Gate),
      legalGates t gs →
      cWire < t + gs.length →
      (∀ u < m, old u < t + gs.length) →
      let res := addXorMany t cWire flag old m gs
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates t res.1 ∧
        costGates res.1 = costGates gs ∧
        (∀ u < m, res.2 u < t + res.1.length) ∧
        (∀ u < m, ∀ x : List Bool, x.length = t →
          (wiresOf res.1 x).getD (res.2 u) false =
            if flag u then
              Bool.xor ((wiresOf gs x).getD (old u) false) ((wiresOf gs x).getD cWire false)
            else (wiresOf gs x).getD (old u) false) := by
  intro m
  induction m with
  | zero =>
    intro gs hleg _ _
    exact ⟨[], by simp [addXorMany], hleg, rfl, fun _ hu => by omega, fun _ hu => by omega⟩
  | succ m ih =>
    intro gs hleg hc hold
    rcases ih gs hleg hc (fun u hu => hold u (by omega)) with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set gs1 := (addXorMany t cWire flag old m gs).1
    set f1 := (addXorMany t cWire flag old m gs).2
    have hlen1 : gs.length ≤ gs1.length := by rw [h1eq, List.length_append]; omega
    by_cases hfl : flag m = true
    · have hstep := addXor_step t gs1 (old m) cWire h1leg
        (by have := hold m (by omega); omega) (by omega)
      refine ⟨ext1 ++ [⟨.mod 2, [old m, cWire]⟩, ⟨.not, [t + gs1.length]⟩], ?_, ?_, ?_, ?_, ?_⟩
      · simp [addXorMany, hfl, gs1, h1eq, List.append_assoc]
      · simpa [addXorMany, hfl, gs1] using hstep.1
      · simpa [addXorMany, hfl, gs1, h1cost] using hstep.2.1
      · intro u hu
        simp only [addXorMany, hfl, ↓reduceIte]
        by_cases hum : u = m
        · subst hum; simp only [↓reduceIte, List.length_append, List.length_cons, List.length_nil]; omega
        · simp only [hum, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]
          have := h1lt u (by omega); dsimp only [gs1, f1] at this; omega
      · intro u hu x hx
        simp only [addXorMany, hfl, ↓reduceIte]
        by_cases hum : u = m
        · subst hum
          simp only [↓reduceIte, hfl]
          change (wiresOf (gs1 ++ [⟨.mod 2, [old u, cWire]⟩, ⟨.not, [t + gs1.length]⟩]) x).getD (t + gs1.length + 1) false = _
          rw [hstep.2.2.2 x hx, h1eq,
              wiresOf_append_getD_lt gs ext1 x (by rw [hx]; exact hold u (by omega)),
              wiresOf_append_getD_lt gs ext1 x (by rw [hx]; exact hc)]
        · simp only [hum, ↓reduceIte]
          change (wiresOf (gs1 ++ [⟨.mod 2, [old m, cWire]⟩, ⟨.not, [t + gs1.length]⟩]) x).getD (f1 u) false = _
          rw [wiresOf_append_getD_lt gs1 _ x (by rw [hx]; exact h1lt u (by omega))]
          exact h1sem u (by omega) x hx
    · have hflf : flag m = false := Bool.eq_false_iff.mpr hfl
      refine ⟨ext1, ?_, ?_, ?_, ?_, ?_⟩
      · simp [addXorMany, hflf, gs1, h1eq]
      · simpa [addXorMany, hflf, gs1] using h1leg
      · simpa [addXorMany, hflf, gs1] using h1cost
      · intro u hu
        simp only [addXorMany, hflf, Bool.false_eq_true, ↓reduceIte]
        by_cases hum : u = m
        · subst hum
          have hfm : (addXorMany t cWire flag old u gs).2 u = old u := by
            clear h1eq h1leg h1cost h1lt h1sem hlen1 ih
            have hkeep : ∀ (n : ℕ) (g : List Gate), u ≥ n → (addXorMany t cWire flag old n g).2 u = old u := by
              intro n
              induction n with
              | zero => intro g _; rfl
              | succ n ihn =>
                intro g hge
                simp only [addXorMany]
                split_ifs
                · have hne : u ≠ n := by omega
                  simp only [hne, ↓reduceIte]
                  exact ihn g (by omega)
                · exact ihn g (by omega)
            exact hkeep u gs (le_refl _)
          rw [hfm]; have := hold u (by omega); dsimp only [gs1] at hlen1; omega
        · exact h1lt u (by omega)
      · intro u hu x hx
        simp only [addXorMany, hflf, Bool.false_eq_true, ↓reduceIte]
        by_cases hum : u = m
        · subst hum
          have hfm : (addXorMany t cWire flag old u gs).2 u = old u := by
            clear h1eq h1leg h1cost h1lt h1sem hlen1 ih
            have hkeep : ∀ (n : ℕ) (g : List Gate), u ≥ n → (addXorMany t cWire flag old n g).2 u = old u := by
              intro n
              induction n with
              | zero => intro g _; rfl
              | succ n ihn =>
                intro g hge
                simp only [addXorMany]
                split_ifs
                · have hne : u ≠ n := by omega
                  simp only [hne, ↓reduceIte]
                  exact ihn g (by omega)
                · exact ihn g (by omega)
            exact hkeep u gs (le_refl _)
          rw [hfm, hflf]
          simp only [Bool.false_eq_true, ↓reduceIte]
          change (wiresOf gs1 x).getD (old u) false = _
          rw [h1eq, wiresOf_append_getD_lt gs ext1 x (by rw [hx]; exact hold u (by omega))]
        · exact h1sem u (by omega) x hx

def dotLin {k : ℕ} (s0 : Fin k → F2) : (Fin k → F2) →ₗ[F2] F2 :=
  { toFun := fun u => dotProduct s0 u
    map_add' := fun a b => dotProduct_add s0 a b
    map_smul' := fun c a => by simp [dotProduct_smul] }

def kerDot {k : ℕ} (U : Submodule F2 (Fin k → F2)) (s0 : Fin k → F2) : Submodule F2 (Fin k → F2) :=
  U ⊓ LinearMap.ker (dotLin s0)

lemma mem_kerDot {k : ℕ} (U : Submodule F2 (Fin k → F2)) (s0 u : Fin k → F2) :
    u ∈ kerDot U s0 ↔ u ∈ U ∧ dotProduct s0 u = 0 := Iff.rfl

lemma finrank_ker_dot {k : ℕ} (U : Submodule F2 (Fin k → F2)) (s0 v0 : Fin k → F2)
    (hv0 : v0 ∈ U) (hdot : dotProduct s0 v0 = 1) :
    Module.finrank F2 (kerDot U s0) + 1 = Module.finrank F2 U := by
  let φ : U →ₗ[F2] F2 :=
    { toFun := fun u => dotProduct s0 u.val
      map_add' := fun a b => dotProduct_add s0 a.val b.val
      map_smul' := fun c a => by simp [dotProduct_smul] }
  have hsurj : Function.Surjective φ := by
    intro c
    refine ⟨c • ⟨v0, hv0⟩, ?_⟩
    simp only [map_smul, φ, LinearMap.coe_mk, AddHom.coe_mk, hdot, smul_eq_mul, mul_one]
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  have hran : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
  rw [hran, finrank_top, Module.finrank_self] at hrk
  have hequiv : kerDot U s0 ≃ₗ[F2] LinearMap.ker φ :=
    { toFun := fun u => ⟨⟨u.val, u.property.1⟩, u.property.2⟩
      invFun := fun u => ⟨u.val.val, ⟨u.val.property, u.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [hequiv.finrank_eq]
  omega

structure Branch (k t : ℕ) where
  r : ℕ
  U : Submodule F2 (Fin k → F2)
  gates : List Gate
  tap : Fin k → ℕ
  off : ℕ → ℕ
  slope : ℕ → (Fin k → F2)

def Branch.pos {k t : ℕ} (B : Branch k t) (z : Fin t → F2) (j : Fin k) : F2 :=
  if (wiresOf B.gates (bitsOf t z)).getD (B.tap j) false then 1 else 0

def ValidBranch {k t : ℕ} (gs : List Gate) (B : Branch k t) : Prop :=
  Module.finrank F2 B.U + B.r = k ∧
  legalGates t B.gates ∧
  costGates B.gates + B.r ≤ costGates gs ∧
  (∀ j : Fin k, B.tap j < t + B.gates.length) ∧
  (∀ w < k + t + gs.length, B.off w < t + B.gates.length) ∧
  (∀ w < k + t + gs.length, ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ B.U →
    (wiresOf gs (bitsOf k (B.pos z + u) ++ bitsOf t z)).getD w false =
      Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off w) false)
        (decide (dotProduct (B.slope w) u = 1)))

lemma branch_eval_add_gate {k t : ℕ} {gs : List Gate} {g : Gate} {B : Branch k t}
    (_hleg : legalGates (k + t) (gs ++ [g]))
    (hB : ValidBranch gs B)
    (gs' : List Gate) (ext : List Gate) (hgs' : gs' = B.gates ++ ext)
    (hleg' : legalGates t gs')
    (hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]))
    (wNew : ℕ) (hwNew : wNew < t + gs'.length) (sNew : Fin k → F2)
    (hsemNew : ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ B.U →
      g.op.eval (g.inputs.map fun i => (wiresOf gs (bitsOf k (B.pos z + u) ++ bitsOf t z)).getD i false) =
        Bool.xor ((wiresOf gs' (bitsOf t z)).getD wNew false) (decide (dotProduct sNew u = 1))) :
    let B' : Branch k t :=
      ⟨B.r, B.U, gs', B.tap,
        fun w => if w = k + t + gs.length then wNew else B.off w,
        fun w => if w = k + t + gs.length then sNew else B.slope w⟩
    ValidBranch (gs ++ [g]) B' ∧
      ∀ z : Fin t → F2, B'.pos z = B.pos z := by
  intro B'
  have hpos_eq : ∀ z : Fin t → F2, B'.pos z = B.pos z := by
    intro z; funext j
    simp only [Branch.pos, B', hgs']
    rw [wiresOf_append_getD_lt B.gates ext (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.1 j)]
  refine ⟨⟨hB.1, hleg', hcost', ?_, ?_, ?_⟩, hpos_eq⟩
  · intro j; simp only [B', hgs', List.length_append]; have := hB.2.2.2.1 j; omega
  · intro w hw
    simp only [List.length_append, List.length_cons, List.length_nil] at hw
    simp only [B']
    by_cases hweq : w = k + t + gs.length
    · simp only [hweq, ↓reduceIte]; exact hwNew
    · simp only [hweq, ↓reduceIte, hgs', List.length_append]
      have := hB.2.2.2.2.1 w (by omega); omega
  · intro w hw z u hu
    simp only [List.length_append, List.length_cons, List.length_nil] at hw
    rw [hpos_eq z]
    have hlen_in : (bitsOf k (B.pos z + u) ++ bitsOf t z).length = k + t := by
      simp [bitsOf_len]
    by_cases hweq : w = k + t + gs.length
    · subst hweq
      simp only [B', ↓reduceIte]
      have hidx : k + t + gs.length = (bitsOf k (B.pos z + u) ++ bitsOf t z).length + gs.length := by omega
      rw [hidx, wiresOf_snoc_last]
      exact hsemNew z u hu
    · simp only [B', hweq, ↓reduceIte]
      rw [wiresOf_append_getD_lt gs [g] _ (by rw [hlen_in]; omega)]
      rw [hgs', wiresOf_append_getD_lt B.gates ext (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 w (by omega))]
      exact hB.2.2.2.2.2 w (by omega) z u hu

lemma step_single_branch {k t : ℕ} {gs : List Gate} {g : Gate} (B : Branch k t)
    (hleg : legalGates (k + t) (gs ++ [g])) (hB : ValidBranch gs B) :
    ∃ L : List (Branch k t),
      (∀ B' ∈ L, ValidBranch (gs ++ [g]) B') ∧
      ∀ (z : Fin t → F2) (x : Fin k → F2),
        (x - B.pos z ∈ B.U → ∃! idx : Fin L.length, x - (L.get idx).pos z ∈ (L.get idx).U) ∧
        (x - B.pos z ∉ B.U → ∀ idx : Fin L.length, x - (L.get idx).pos z ∉ (L.get idx).U) := by
  have hpre := legalGates_prefix hleg
  have hback := hpre.2.1
  have hshape := hpre.2.2
  have hcost_ge : costGates gs ≤ costGates (gs ++ [g]) := by
    rw [costGates_append]; omega
  have hwrap_one : ∀ (B' : Branch k t), ValidBranch (gs ++ [g]) B' → B'.U = B.U →
      (∀ z, B'.pos z = B.pos z) →
      ∃ L : List (Branch k t),
        (∀ b ∈ L, ValidBranch (gs ++ [g]) b) ∧
        ∀ (z : Fin t → F2) (x : Fin k → F2),
          (x - B.pos z ∈ B.U → ∃! idx : Fin L.length, x - (L.get idx).pos z ∈ (L.get idx).U) ∧
          (x - B.pos z ∉ B.U → ∀ idx : Fin L.length, x - (L.get idx).pos z ∉ (L.get idx).U) := by
    intro B' hB' hU hpos
    refine ⟨[B'], fun b hb => by simp at hb; subst hb; exact hB', fun z x => ⟨?_, ?_⟩⟩
    · intro hx
      refine ⟨⟨0, by simp⟩, by simpa [hpos, hU] using hx, fun j _ => Fin.ext (by have := j.isLt; simp only [List.length_singleton] at this; change j.val = 0; omega)⟩
    · intro hnx idx
      have hi0 : idx = ⟨0, by simp⟩ := Fin.ext (by have := idx.isLt; simp only [List.length_singleton] at this; change idx.val = 0; omega)
      subst hi0
      simpa [hpos, hU] using hnx
  rcases hshape.2 with hop | hop | hop | ⟨hop, hlen1⟩
  ·
    rcases hg : g.inputs with _ | ⟨w0, rest⟩
    ·
      let gs' := B.gates ++ [⟨.and, []⟩]
      have hleg' : legalGates t gs' :=
        legalGates_snoc hB.2.1 (by simp) ⟨by simp, Or.inl rfl⟩
      have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
        rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
      have hres := branch_eval_add_gate hleg hB gs' [⟨.and, []⟩] rfl hleg' hcost'
        (t + B.gates.length) (by simp [gs']) 0 (fun z u _ => by
          rw [hop, hg]
          have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
          rw [hidx, wiresOf_snoc_last]; simp [GateOp.eval])
      exact hwrap_one _ hres.1 rfl hres.2
    · rcases rest with _ | ⟨w1, rest2⟩
      ·
        have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        have hres := branch_eval_add_gate hleg hB B.gates [] (by simp) hB.2.1
          (by have := hB.2.2.1; omega) (B.off w0) (hB.2.2.2.2.1 w0 hw0) (B.slope w0)
          (fun z u hu => by
            rw [hop, hg]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
              List.all_nil, id_eq, Bool.and_true]
            exact hB.2.2.2.2.2 w0 hw0 z u hu)
        exact hwrap_one _ hres.1 rfl hres.2
      · rcases rest2 with _ | ⟨_, _⟩
        ·
          have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
          have hw1 : w1 < k + t + gs.length := hback w1 (by rw [hg]; simp)
          have hcost1 : costGates (gs ++ [g]) = costGates gs + 1 :=
            costGates_snoc_one gs g ⟨Or.inl hop, by rw [hg]; rfl⟩
          by_cases hvan : (∀ u ∈ B.U, dotProduct (B.slope w0) u = 0) ∧
              (∀ u ∈ B.U, dotProduct (B.slope w1) u = 0)
          ·
            let gs' := B.gates ++ [⟨.and, [B.off w0, B.off w1]⟩]
            have hleg' : legalGates t gs' :=
              legalGates_snoc hB.2.1
                (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hB.2.2.2.2.1 w0 hw0; exact hB.2.2.2.2.1 w1 hw1)
                ⟨by simp, Or.inl rfl⟩
            have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
              rw [costGates_snoc_one B.gates _ ⟨Or.inl rfl, rfl⟩, hcost1]; have := hB.2.2.1; omega
            have hres := branch_eval_add_gate hleg hB gs' [⟨.and, [B.off w0, B.off w1]⟩] rfl hleg' hcost'
              (t + B.gates.length) (by simp [gs']) 0 (fun z u hu => by
                rw [hop, hg]
                have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
                rw [hidx, wiresOf_snoc_last]
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                  id_eq, Bool.and_true]
                rw [hB.2.2.2.2.2 w0 hw0 z u hu, hB.2.2.2.2.2 w1 hw1 z u hu,
                    hvan.1 u hu, hvan.2 u hu]
                simp)
            exact hwrap_one _ hres.1 rfl hres.2
          ·
            have hex : ∃ (wa wb : ℕ), wa < k + t + gs.length ∧ wb < k + t + gs.length ∧
                ((wa = w0 ∧ wb = w1) ∨ (wa = w1 ∧ wb = w0)) ∧
                ∃ v0 ∈ B.U, dotProduct (B.slope wa) v0 = 1 := by
              by_cases h0 : ∀ u ∈ B.U, dotProduct (B.slope w0) u = 0
              · have h1 : ¬ ∀ u ∈ B.U, dotProduct (B.slope w1) u = 0 := fun h => hvan ⟨h0, h⟩
                push Not at h1
                rcases h1 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.slope w1) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.slope w1) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w1, w0, hw1, hw0, Or.inr ⟨rfl, rfl⟩, v0, hv0, hd1⟩
              · push Not at h0
                rcases h0 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.slope w0) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.slope w0) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w0, w1, hw0, hw1, Or.inl ⟨rfl, rfl⟩, v0, hv0, hd1⟩
            rcases hex with ⟨wa, wb, hwa, hwb, hwab, v0, hv0, hdot⟩
            let U' : Submodule F2 (Fin k → F2) := kerDot B.U (B.slope wa)
            have hdim' : Module.finrank F2 U' + (B.r + 1) = k := by
              have h1 : Module.finrank F2 U' + 1 = Module.finrank F2 B.U :=
                finrank_ker_dot B.U (B.slope wa) v0 hv0 hdot
              have h2 := hB.1
              omega
            have hbuild_child : ∀ (b : Bool), ∃ Bc : Branch k t,
                ValidBranch (gs ++ [g]) Bc ∧ Bc.U = U' ∧
                ∀ z : Fin t → F2,
                  Bc.pos z = B.pos z +
                    (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 := by
              intro b
              let gs0 := if b then B.gates ++ [⟨.not, [B.off wa]⟩] else B.gates
              let cWire := if b then t + B.gates.length else B.off wa
              have hgs0_ext : ∃ e0, gs0 = B.gates ++ e0 := by
                cases b
                · exact ⟨[], by simp [gs0]⟩
                · exact ⟨[⟨.not, [B.off wa]⟩], rfl⟩
              have hgs0_leg : legalGates t gs0 := by
                cases b
                · exact hB.2.1
                · exact legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 wa hwa)
                    ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
              have hgs0_cost : costGates gs0 = costGates B.gates := by
                cases b
                · rfl
                · exact costGates_snoc_zero B.gates _ (by simp)
              have hcWire_lt : cWire < t + gs0.length := by
                cases b
                · exact hB.2.2.2.2.1 wa hwa
                · simp [gs0, cWire]
              have hcWire_sem : ∀ z : Fin t → F2,
                  (wiresOf gs0 (bitsOf t z)).getD cWire false =
                    Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) := by
                intro z
                cases b
                · simp [gs0, cWire]
                · simp only [gs0, cWire, ↓reduceIte]
                  have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
                  rw [hidx, wiresOf_snoc_last]
                  simp [GateOp.eval]
              let tapOld : ℕ → ℕ := fun j => if hj : j < k then B.tap ⟨j, hj⟩ else 0
              let flagTap : ℕ → Bool := fun j => if hj : j < k then decide (v0 ⟨j, hj⟩ = 1) else false
              let resT := addXorMany t cWire flagTap tapOld k gs0
              have hresT := addXorMany_spec t cWire flagTap tapOld k gs0 hgs0_leg hcWire_lt
                (fun j hj => by
                  simp only [tapOld, hj, ↓reduceDIte]
                  rcases hgs0_ext with ⟨e0, he0⟩
                  rw [he0, List.length_append]
                  have := hB.2.2.2.1 ⟨j, hj⟩; omega)
              rcases hresT with ⟨extT, hTeq, hTleg, hTcost, hTlt, hTsem⟩
              let flagOff : ℕ → Bool := fun w => decide (dotProduct (B.slope w) v0 = 1)
              let resO := addXorMany t cWire flagOff B.off (k + t + gs.length) resT.1
              have hresO := addXorMany_spec t cWire flagOff B.off (k + t + gs.length) resT.1 hTleg
                (by rw [hTeq, List.length_append]; omega)
                (fun w hw => by
                  rcases hgs0_ext with ⟨e0, he0⟩
                  rw [hTeq, he0, List.length_append, List.length_append]
                  have := hB.2.2.2.2.1 w hw; omega)
              rcases hresO with ⟨extO, hOeq, hOleg, hOcost, hOlt, hOsem⟩
              let gsF := if b then resO.1 else resO.1 ++ [⟨.or, []⟩]
              have hgsF_ext : ∃ eF, gsF = resO.1 ++ eF := by
                cases b
                · exact ⟨[⟨.or, []⟩], rfl⟩
                · exact ⟨[], by simp [gsF]⟩
              have hgsF_leg : legalGates t gsF := by
                cases b
                · exact legalGates_snoc hOleg (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
                · exact hOleg
              have hgsF_cost : costGates gsF = costGates B.gates := by
                cases b
                · rw [show gsF = resO.1 ++ [⟨.or, []⟩] from rfl, costGates_snoc_zero _ _ (by simp), hOcost, hTcost, hgs0_cost]
                · simp only [gsF, ↓reduceIte]; rw [hOcost, hTcost, hgs0_cost]
              let tapF : Fin k → ℕ := fun j => resT.2 j.val
              let wNew := if b then resO.2 wb else t + resO.1.length
              let sNew : Fin k → F2 := if b then B.slope wb else 0
              let Bc : Branch k t :=
                ⟨B.r + 1, U', gsF, tapF,
                  fun w => if w = k + t + gs.length then wNew else resO.2 w,
                  fun w => if w = k + t + gs.length then sNew else B.slope w⟩
              have hpos_c : ∀ z : Fin t → F2,
                  Bc.pos z = B.pos z +
                    (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 := by
                intro z; funext j
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                have htap_val : (wiresOf gsF (bitsOf t z)).getD (tapF j) false =
                    (wiresOf resT.1 (bitsOf t z)).getD (resT.2 j.val) false := by
                  rw [heF, hOeq, List.append_assoc,
                      wiresOf_append_getD_lt resT.1 _ (bitsOf t z) (by rw [bitsOf_len]; exact hTlt j.val j.isLt)]
                simp only [Branch.pos, Bc, htap_val]
                rw [hTsem j.val j.isLt (bitsOf t z) (bitsOf_len t z)]
                simp only [flagTap, tapOld, j.isLt, ↓reduceDIte, hcWire_sem z]
                rw [he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.1 j)]
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Branch.pos]
                cases (wiresOf B.gates (bitsOf t z)).getD (B.tap j) false <;>
                  cases Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) <;>
                  rcases zmod2_cases (v0 j) with h | h <;> simp [h] <;> decide
              have hsem_old : ∀ w < k + t + gs.length, ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ U' →
                  (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w false =
                    Bool.xor ((wiresOf gsF (bitsOf t z)).getD (resO.2 w) false)
                      (decide (dotProduct (B.slope w) u = 1)) := by
                intro w hw z u hu
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                set cbit := Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                set cf : F2 := if cbit then 1 else 0
                have hu_in_B : cf • v0 + u ∈ B.U := B.U.add_mem (B.U.smul_mem cf hv0) hu.1
                have hpos_rw : Bc.pos z + u = B.pos z + (cf • v0 + u) := by
                  rw [hpos_c z, add_assoc]
                rw [hpos_rw, hB.2.2.2.2.2 w hw z (cf • v0 + u) hu_in_B]
                have hwireO : (wiresOf gsF (bitsOf t z)).getD (resO.2 w) false =
                    if decide (dotProduct (B.slope w) v0 = 1) then
                      Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off w) false) cbit
                    else (wiresOf B.gates (bitsOf t z)).getD (B.off w) false := by
                  rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt w hw)]
                  rw [hOsem w hw (bitsOf t z) (bitsOf_len t z)]
                  rw [hTeq,
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 w hw; omega),
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                  rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 w hw)]
                rw [hwireO, dotProduct_add, dotProduct_smul, zmod2_add_decide, smul_eq_mul, zmod2_mul_decide, zmod2_bool_decide]
                cases (wiresOf B.gates (bitsOf t z)).getD (B.off w) false <;>
                  cases cbit <;> cases decide (dotProduct (B.slope w) v0 = 1) <;>
                  cases decide (dotProduct (B.slope w) u = 1) <;> decide
              refine ⟨Bc, ⟨hdim', hgsF_leg, by change costGates gsF + (B.r + 1) ≤ costGates (gs ++ [g]); rw [hgsF_cost, hcost1]; have := hB.2.2.1; omega, ?_, ?_, ?_⟩, rfl, hpos_c⟩
              · intro j
                rcases hgsF_ext with ⟨eF, heF⟩
                have h1 : resT.2 j.val < t + resT.1.length := hTlt j.val j.isLt
                have h2 : resO.1.length = resT.1.length + extO.length := by rw [hOeq, List.length_append]
                simp only [Bc, tapF, heF, List.length_append]
                omega
              · intro w hw
                simp only [List.length_append, List.length_cons, List.length_nil] at hw
                simp only [Bc]
                by_cases hweq : w = k + t + gs.length
                · simp only [hweq, ↓reduceIte, wNew, gsF]
                  cases b
                  · simp
                  · simp only [↓reduceIte]; exact hOlt wb hwb
                · simp only [hweq, ↓reduceIte]
                  rcases hgsF_ext with ⟨eF, heF⟩
                  have h1 : resO.2 w < t + resO.1.length := hOlt w (by omega)
                  rw [heF, List.length_append]; omega
              · intro w hw z u hu
                simp only [List.length_append, List.length_cons, List.length_nil] at hw
                have hlen_in : (bitsOf k (Bc.pos z + u) ++ bitsOf t z).length = k + t := by simp [bitsOf_len]
                by_cases hweq : w = k + t + gs.length
                · subst hweq
                  simp only [Bc, ↓reduceIte]
                  rw [wiresOf_snoc_last_eq gs g _ hlen_in, hop, hg]
                  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                    id_eq, Bool.and_true]
                  have hwa_val : (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wa false = b := by
                    have hu2 : dotProduct (B.slope wa) u = 0 := hu.2
                    rw [hsem_old wa hwa z u hu, hu2]
                    rcases hgsF_ext with ⟨eF, heF⟩
                    rcases hgs0_ext with ⟨e0, he0⟩
                    rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt wa hwa)]
                    rw [hOsem wa hwa (bitsOf t z) (bitsOf_len t z)]
                    simp only [flagOff, hdot]
                    rw [hTeq,
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 wa hwa; omega),
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                    rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 wa hwa)]
                    cases b <;> cases (wiresOf B.gates (bitsOf t z)).getD (B.off wa) false <;> decide
                  have hcomm : ((wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w0 false &&
                      (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w1 false) =
                      ((wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wa false &&
                       (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wb false) := by
                    rcases hwab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · rfl
                    · exact Bool.and_comm _ _
                  rw [hcomm, hwa_val]
                  cases b
                  · simp only [Bool.false_and, wNew, sNew, gsF, Bool.false_eq_true, ↓reduceIte]
                    rw [wiresOf_snoc_last_eq resO.1 ⟨.or, []⟩ (bitsOf t z) (bitsOf_len t z)]; simp [GateOp.eval]
                  · simp only [Bool.true_and, wNew, sNew, gsF, ↓reduceIte]
                    exact hsem_old wb hwb z u hu
                · simp only [Bc, hweq, ↓reduceIte]
                  rw [wiresOf_append_getD_lt gs [g] _ (by rw [hlen_in]; omega)]
                  exact hsem_old w (by omega) z u hu
            rcases hbuild_child false with ⟨B0, hB0, hU0, hpos0⟩
            rcases hbuild_child true with ⟨B1, hB1, hU1, hpos1⟩
            refine ⟨[B0, B1], ?_, ?_⟩
            · intro b hb; simp at hb; rcases hb with rfl | rfl; exact hB0; exact hB1
            · intro z x
              have hmem_iff : ∀ (b : Bool) (Bc : Branch k t), Bc.U = U' →
                  Bc.pos z = B.pos z + (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 →
                  (x - Bc.pos z ∈ Bc.U ↔
                    x - B.pos z ∈ B.U ∧
                      b = Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                        (decide (dotProduct (B.slope wa) (x - B.pos z) = 1))) := by
                intro b Bc hUc hpc
                set ow := (wiresOf B.gates (bitsOf t z)).getD (B.off wa) false
                set cb := Bool.xor b ow
                set cf : F2 := if cb then 1 else 0
                have hdiff : x - Bc.pos z = (x - B.pos z) + cf • v0 := by
                  rw [hpc, zmod2_vec_sub_eq_add, zmod2_vec_sub_eq_add, add_assoc]
                rw [hUc, hdiff, mem_kerDot]
                constructor
                · rintro ⟨h1, h2⟩
                  have h1' : x - B.pos z ∈ B.U := by
                    have := B.U.add_mem h1 (B.U.smul_mem cf hv0)
                    rw [add_assoc, zmod2_vec_add_self, add_zero] at this
                    exact this
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one] at h2
                  exact ⟨h1', (zmod2_xor_zero_iff b ow _).mp h2⟩
                · rintro ⟨h1, h2⟩
                  refine ⟨B.U.add_mem h1 (B.U.smul_mem cf hv0), ?_⟩
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one]
                  exact (zmod2_xor_zero_iff b ow _).mpr h2
              constructor
              · intro hx
                cases htarget : Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                    (decide (dotProduct (B.slope wa) (x - B.pos z) = 1))
                · refine ⟨⟨0, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff false B0 hU0 (hpos0 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exact Fin.ext hv
                    · exfalso
                      have hm : x - B1.pos z ∈ B1.U := by simpa [hv] using hidx
                      have := ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).2
                      rw [htarget] at this; simp at this
                · refine ⟨⟨1, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff true B1 hU1 (hpos1 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exfalso
                      have hm : x - B0.pos z ∈ B0.U := by simpa [hv] using hidx
                      have := ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).2
                      rw [htarget] at this; exact Bool.false_ne_true this
                    · exact Fin.ext hv
              · intro hnx idx hidx
                have hlt : idx.val < 2 := idx.isLt
                interval_cases hv : idx.val
                · have hm : x - B0.pos z ∈ B0.U := by simpa [hv] using hidx
                  exact hnx ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).1
                · have hm : x - B1.pos z ∈ B1.U := by simpa [hv] using hidx
                  exact hnx ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).1
        · exfalso; have := hshape.1; rw [hg] at this; simp at this
  ·
    rcases hg : g.inputs with _ | ⟨w0, rest⟩
    ·
      let gs' := B.gates ++ [⟨.or, []⟩]
      have hleg' : legalGates t gs' :=
        legalGates_snoc hB.2.1 (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
      have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
        rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
      have hres := branch_eval_add_gate hleg hB gs' [⟨.or, []⟩] rfl hleg' hcost'
        (t + B.gates.length) (by simp [gs']) 0 (fun z u _ => by
          rw [hop, hg]
          have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
          rw [hidx, wiresOf_snoc_last]; simp [GateOp.eval])
      exact hwrap_one _ hres.1 rfl hres.2
    · rcases rest with _ | ⟨w1, rest2⟩
      ·
        have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        have hres := branch_eval_add_gate hleg hB B.gates [] (by simp) hB.2.1
          (by have := hB.2.2.1; omega) (B.off w0) (hB.2.2.2.2.1 w0 hw0) (B.slope w0)
          (fun z u hu => by
            rw [hop, hg]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
              List.any_nil, id_eq, Bool.or_false]
            exact hB.2.2.2.2.2 w0 hw0 z u hu)
        exact hwrap_one _ hres.1 rfl hres.2
      · rcases rest2 with _ | ⟨_, _⟩
        ·
          have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
          have hw1 : w1 < k + t + gs.length := hback w1 (by rw [hg]; simp)
          have hcost1 : costGates (gs ++ [g]) = costGates gs + 1 :=
            costGates_snoc_one gs g ⟨Or.inr hop, by rw [hg]; rfl⟩
          by_cases hvan : (∀ u ∈ B.U, dotProduct (B.slope w0) u = 0) ∧
              (∀ u ∈ B.U, dotProduct (B.slope w1) u = 0)
          · let gs' := B.gates ++ [⟨.or, [B.off w0, B.off w1]⟩]
            have hleg' : legalGates t gs' :=
              legalGates_snoc hB.2.1
                (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hB.2.2.2.2.1 w0 hw0; exact hB.2.2.2.2.1 w1 hw1)
                ⟨by simp, Or.inr (Or.inl rfl)⟩
            have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
              rw [costGates_snoc_one B.gates _ ⟨Or.inr rfl, rfl⟩, hcost1]; have := hB.2.2.1; omega
            have hres := branch_eval_add_gate hleg hB gs' [⟨.or, [B.off w0, B.off w1]⟩] rfl hleg' hcost'
              (t + B.gates.length) (by simp [gs']) 0 (fun z u hu => by
                rw [hop, hg]
                have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
                rw [hidx, wiresOf_snoc_last]
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                  id_eq, Bool.or_false]
                rw [hB.2.2.2.2.2 w0 hw0 z u hu, hB.2.2.2.2.2 w1 hw1 z u hu,
                    hvan.1 u hu, hvan.2 u hu]
                simp)
            exact hwrap_one _ hres.1 rfl hres.2
          · have hex : ∃ (wa wb : ℕ), wa < k + t + gs.length ∧ wb < k + t + gs.length ∧
                ((wa = w0 ∧ wb = w1) ∨ (wa = w1 ∧ wb = w0)) ∧
                ∃ v0 ∈ B.U, dotProduct (B.slope wa) v0 = 1 := by
              by_cases h0 : ∀ u ∈ B.U, dotProduct (B.slope w0) u = 0
              · have h1 : ¬ ∀ u ∈ B.U, dotProduct (B.slope w1) u = 0 := fun h => hvan ⟨h0, h⟩
                push Not at h1
                rcases h1 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.slope w1) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.slope w1) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w1, w0, hw1, hw0, Or.inr ⟨rfl, rfl⟩, v0, hv0, hd1⟩
              · push Not at h0
                rcases h0 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.slope w0) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.slope w0) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w0, w1, hw0, hw1, Or.inl ⟨rfl, rfl⟩, v0, hv0, hd1⟩
            rcases hex with ⟨wa, wb, hwa, hwb, hwab, v0, hv0, hdot⟩
            let U' : Submodule F2 (Fin k → F2) := kerDot B.U (B.slope wa)
            have hdim' : Module.finrank F2 U' + (B.r + 1) = k := by
              have h1 : Module.finrank F2 U' + 1 = Module.finrank F2 B.U :=
                finrank_ker_dot B.U (B.slope wa) v0 hv0 hdot
              have h2 := hB.1
              omega
            have hbuild_child : ∀ (b : Bool), ∃ Bc : Branch k t,
                ValidBranch (gs ++ [g]) Bc ∧ Bc.U = U' ∧
                ∀ z : Fin t → F2,
                  Bc.pos z = B.pos z +
                    (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 := by
              intro b
              let gs0 := if b then B.gates ++ [⟨.not, [B.off wa]⟩] else B.gates
              let cWire := if b then t + B.gates.length else B.off wa
              have hgs0_ext : ∃ e0, gs0 = B.gates ++ e0 := by
                cases b
                · exact ⟨[], by simp [gs0]⟩
                · exact ⟨[⟨.not, [B.off wa]⟩], rfl⟩
              have hgs0_leg : legalGates t gs0 := by
                cases b
                · exact hB.2.1
                · exact legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 wa hwa)
                    ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
              have hgs0_cost : costGates gs0 = costGates B.gates := by
                cases b
                · rfl
                · exact costGates_snoc_zero B.gates _ (by simp)
              have hcWire_lt : cWire < t + gs0.length := by
                cases b
                · exact hB.2.2.2.2.1 wa hwa
                · simp [gs0, cWire]
              have hcWire_sem : ∀ z : Fin t → F2,
                  (wiresOf gs0 (bitsOf t z)).getD cWire false =
                    Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) := by
                intro z
                cases b
                · simp [gs0, cWire]
                · simp only [gs0, cWire, ↓reduceIte]
                  have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
                  rw [hidx, wiresOf_snoc_last]
                  simp [GateOp.eval]
              let tapOld : ℕ → ℕ := fun j => if hj : j < k then B.tap ⟨j, hj⟩ else 0
              let flagTap : ℕ → Bool := fun j => if hj : j < k then decide (v0 ⟨j, hj⟩ = 1) else false
              let resT := addXorMany t cWire flagTap tapOld k gs0
              have hresT := addXorMany_spec t cWire flagTap tapOld k gs0 hgs0_leg hcWire_lt
                (fun j hj => by
                  simp only [tapOld, hj, ↓reduceDIte]
                  rcases hgs0_ext with ⟨e0, he0⟩
                  rw [he0, List.length_append]
                  have := hB.2.2.2.1 ⟨j, hj⟩; omega)
              rcases hresT with ⟨extT, hTeq, hTleg, hTcost, hTlt, hTsem⟩
              let flagOff : ℕ → Bool := fun w => decide (dotProduct (B.slope w) v0 = 1)
              let resO := addXorMany t cWire flagOff B.off (k + t + gs.length) resT.1
              have hresO := addXorMany_spec t cWire flagOff B.off (k + t + gs.length) resT.1 hTleg
                (by rw [hTeq, List.length_append]; omega)
                (fun w hw => by
                  rcases hgs0_ext with ⟨e0, he0⟩
                  rw [hTeq, he0, List.length_append, List.length_append]
                  have := hB.2.2.2.2.1 w hw; omega)
              rcases hresO with ⟨extO, hOeq, hOleg, hOcost, hOlt, hOsem⟩
              let gsF := if b then resO.1 ++ [⟨.and, []⟩] else resO.1
              have hgsF_ext : ∃ eF, gsF = resO.1 ++ eF := by
                cases b
                · exact ⟨[], by simp [gsF]⟩
                · exact ⟨[⟨.and, []⟩], rfl⟩
              have hgsF_leg : legalGates t gsF := by
                cases b
                · exact hOleg
                · exact legalGates_snoc hOleg (by simp) ⟨by simp, Or.inl rfl⟩
              have hgsF_cost : costGates gsF = costGates B.gates := by
                cases b
                · simp only [gsF, Bool.false_eq_true, ↓reduceIte]; rw [hOcost, hTcost, hgs0_cost]
                · rw [show gsF = resO.1 ++ [⟨.and, []⟩] from rfl, costGates_snoc_zero _ _ (by simp), hOcost, hTcost, hgs0_cost]
              let tapF : Fin k → ℕ := fun j => resT.2 j.val
              let wNew := if b then t + resO.1.length else resO.2 wb
              let sNew : Fin k → F2 := if b then 0 else B.slope wb
              let Bc : Branch k t :=
                ⟨B.r + 1, U', gsF, tapF,
                  fun w => if w = k + t + gs.length then wNew else resO.2 w,
                  fun w => if w = k + t + gs.length then sNew else B.slope w⟩
              have hpos_c : ∀ z : Fin t → F2,
                  Bc.pos z = B.pos z +
                    (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 := by
                intro z; funext j
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                have htap_val : (wiresOf gsF (bitsOf t z)).getD (tapF j) false =
                    (wiresOf resT.1 (bitsOf t z)).getD (resT.2 j.val) false := by
                  rw [heF, hOeq, List.append_assoc,
                      wiresOf_append_getD_lt resT.1 _ (bitsOf t z) (by rw [bitsOf_len]; exact hTlt j.val j.isLt)]
                simp only [Branch.pos, Bc, htap_val]
                rw [hTsem j.val j.isLt (bitsOf t z) (bitsOf_len t z)]
                simp only [flagTap, tapOld, j.isLt, ↓reduceDIte, hcWire_sem z]
                rw [he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.1 j)]
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Branch.pos]
                cases (wiresOf B.gates (bitsOf t z)).getD (B.tap j) false <;>
                  cases Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) <;>
                  rcases zmod2_cases (v0 j) with h | h <;> simp [h] <;> decide
              have hsem_old : ∀ w < k + t + gs.length, ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ U' →
                  (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w false =
                    Bool.xor ((wiresOf gsF (bitsOf t z)).getD (resO.2 w) false)
                      (decide (dotProduct (B.slope w) u = 1)) := by
                intro w hw z u hu
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                set cbit := Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                set cf : F2 := if cbit then 1 else 0
                have hu_in_B : cf • v0 + u ∈ B.U := B.U.add_mem (B.U.smul_mem cf hv0) hu.1
                have hpos_rw : Bc.pos z + u = B.pos z + (cf • v0 + u) := by
                  rw [hpos_c z, add_assoc]
                rw [hpos_rw, hB.2.2.2.2.2 w hw z (cf • v0 + u) hu_in_B]
                have hwireO : (wiresOf gsF (bitsOf t z)).getD (resO.2 w) false =
                    if decide (dotProduct (B.slope w) v0 = 1) then
                      Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off w) false) cbit
                    else (wiresOf B.gates (bitsOf t z)).getD (B.off w) false := by
                  rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt w hw)]
                  rw [hOsem w hw (bitsOf t z) (bitsOf_len t z)]
                  rw [hTeq,
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 w hw; omega),
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                  rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 w hw)]
                rw [hwireO, dotProduct_add, dotProduct_smul, zmod2_add_decide, smul_eq_mul, zmod2_mul_decide, zmod2_bool_decide]
                cases (wiresOf B.gates (bitsOf t z)).getD (B.off w) false <;>
                  cases cbit <;> cases decide (dotProduct (B.slope w) v0 = 1) <;>
                  cases decide (dotProduct (B.slope w) u = 1) <;> decide
              refine ⟨Bc, ⟨hdim', hgsF_leg, by change costGates gsF + (B.r + 1) ≤ costGates (gs ++ [g]); rw [hgsF_cost, hcost1]; have := hB.2.2.1; omega, ?_, ?_, ?_⟩, rfl, hpos_c⟩
              · intro j
                rcases hgsF_ext with ⟨eF, heF⟩
                have h1 : resT.2 j.val < t + resT.1.length := hTlt j.val j.isLt
                have h2 : resO.1.length = resT.1.length + extO.length := by rw [hOeq, List.length_append]
                simp only [Bc, tapF, heF, List.length_append]
                omega
              · intro w hw
                simp only [List.length_append, List.length_cons, List.length_nil] at hw
                simp only [Bc]
                by_cases hweq : w = k + t + gs.length
                · simp only [hweq, ↓reduceIte, wNew, gsF]
                  cases b
                  · simp only [Bool.false_eq_true, ↓reduceIte]; exact hOlt wb hwb
                  · simp
                · simp only [hweq, ↓reduceIte]
                  rcases hgsF_ext with ⟨eF, heF⟩
                  have h1 : resO.2 w < t + resO.1.length := hOlt w (by omega)
                  rw [heF, List.length_append]; omega
              · intro w hw z u hu
                simp only [List.length_append, List.length_cons, List.length_nil] at hw
                have hlen_in : (bitsOf k (Bc.pos z + u) ++ bitsOf t z).length = k + t := by simp [bitsOf_len]
                by_cases hweq : w = k + t + gs.length
                · subst hweq
                  simp only [Bc, ↓reduceIte]
                  rw [wiresOf_snoc_last_eq gs g _ hlen_in, hop, hg]
                  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                    id_eq, Bool.or_false]
                  have hwa_val : (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wa false = b := by
                    have hu2 : dotProduct (B.slope wa) u = 0 := hu.2
                    rw [hsem_old wa hwa z u hu, hu2]
                    rcases hgsF_ext with ⟨eF, heF⟩
                    rcases hgs0_ext with ⟨e0, he0⟩
                    rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt wa hwa)]
                    rw [hOsem wa hwa (bitsOf t z) (bitsOf_len t z)]
                    simp only [flagOff, hdot]
                    rw [hTeq,
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 wa hwa; omega),
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                    rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.gates e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 wa hwa)]
                    cases b <;> cases (wiresOf B.gates (bitsOf t z)).getD (B.off wa) false <;> decide
                  have hcomm : ((wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w0 false ||
                      (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD w1 false) =
                      ((wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wa false ||
                       (wiresOf gs (bitsOf k (Bc.pos z + u) ++ bitsOf t z)).getD wb false) := by
                    rcases hwab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · rfl
                    · exact Bool.or_comm _ _
                  rw [hcomm, hwa_val]
                  cases b
                  · simp only [Bool.false_or, wNew, sNew, gsF, Bool.false_eq_true, ↓reduceIte]
                    exact hsem_old wb hwb z u hu
                  · simp only [Bool.true_or, wNew, sNew, gsF, ↓reduceIte]
                    rw [wiresOf_snoc_last_eq resO.1 ⟨.and, []⟩ (bitsOf t z) (bitsOf_len t z)]; simp [GateOp.eval]
                · simp only [Bc, hweq, ↓reduceIte]
                  rw [wiresOf_append_getD_lt gs [g] _ (by rw [hlen_in]; omega)]
                  exact hsem_old w (by omega) z u hu
            rcases hbuild_child false with ⟨B0, hB0, hU0, hpos0⟩
            rcases hbuild_child true with ⟨B1, hB1, hU1, hpos1⟩
            refine ⟨[B0, B1], ?_, ?_⟩
            · intro b hb; simp at hb; rcases hb with rfl | rfl; exact hB0; exact hB1
            · intro z x
              have hmem_iff : ∀ (b : Bool) (Bc : Branch k t), Bc.U = U' →
                  Bc.pos z = B.pos z + (if Bool.xor b ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false) then (1 : F2) else 0) • v0 →
                  (x - Bc.pos z ∈ Bc.U ↔
                    x - B.pos z ∈ B.U ∧
                      b = Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                        (decide (dotProduct (B.slope wa) (x - B.pos z) = 1))) := by
                intro b Bc hUc hpc
                set ow := (wiresOf B.gates (bitsOf t z)).getD (B.off wa) false
                set cb := Bool.xor b ow
                set cf : F2 := if cb then 1 else 0
                have hdiff : x - Bc.pos z = (x - B.pos z) + cf • v0 := by
                  rw [hpc, zmod2_vec_sub_eq_add, zmod2_vec_sub_eq_add, add_assoc]
                rw [hUc, hdiff, mem_kerDot]
                constructor
                · rintro ⟨h1, h2⟩
                  have h1' : x - B.pos z ∈ B.U := by
                    have := B.U.add_mem h1 (B.U.smul_mem cf hv0)
                    rw [add_assoc, zmod2_vec_add_self, add_zero] at this
                    exact this
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one] at h2
                  exact ⟨h1', (zmod2_xor_zero_iff b ow _).mp h2⟩
                · rintro ⟨h1, h2⟩
                  refine ⟨B.U.add_mem h1 (B.U.smul_mem cf hv0), ?_⟩
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one]
                  exact (zmod2_xor_zero_iff b ow _).mpr h2
              constructor
              · intro hx
                cases htarget : Bool.xor ((wiresOf B.gates (bitsOf t z)).getD (B.off wa) false)
                    (decide (dotProduct (B.slope wa) (x - B.pos z) = 1))
                · refine ⟨⟨0, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff false B0 hU0 (hpos0 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exact Fin.ext hv
                    · exfalso
                      have hm : x - B1.pos z ∈ B1.U := by simpa [hv] using hidx
                      have := ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).2
                      rw [htarget] at this; simp at this
                · refine ⟨⟨1, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff true B1 hU1 (hpos1 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exfalso
                      have hm : x - B0.pos z ∈ B0.U := by simpa [hv] using hidx
                      have := ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).2
                      rw [htarget] at this; exact Bool.false_ne_true this
                    · exact Fin.ext hv
              · intro hnx idx hidx
                have hlt : idx.val < 2 := idx.isLt
                interval_cases hv : idx.val
                · have hm : x - B0.pos z ∈ B0.U := by simpa [hv] using hidx
                  exact hnx ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).1
                · have hm : x - B1.pos z ∈ B1.U := by simpa [hv] using hidx
                  exact hnx ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).1
        · exfalso; have := hshape.1; rw [hg] at this; simp at this
  ·
    rcases hg : g.inputs with _ | ⟨w0, rest⟩
    ·
      let gs' := B.gates ++ [⟨.mod 2, []⟩]
      have hleg' : legalGates t gs' :=
        legalGates_snoc hB.2.1 (by simp) ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩
      have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
        rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
      have hres := branch_eval_add_gate hleg hB gs' [⟨.mod 2, []⟩] rfl hleg' hcost'
        (t + B.gates.length) (by simp [gs']) 0 (fun z u _ => by
          rw [hop, hg]
          have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
          rw [hidx, wiresOf_snoc_last]; simp [GateOp.eval])
      exact hwrap_one _ hres.1 rfl hres.2
    · rcases rest with _ | ⟨w1, rest2⟩
      ·
        have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        let gs' := B.gates ++ [⟨.not, [B.off w0]⟩]
        have hleg' : legalGates t gs' :=
          legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 w0 hw0)
            ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
        have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
          rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
        have hres := branch_eval_add_gate hleg hB gs' [⟨.not, [B.off w0]⟩] rfl hleg' hcost'
          (t + B.gates.length) (by simp [gs']) (B.slope w0) (fun z u hu => by
            rw [hop, hg]
            have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
            rw [hidx, wiresOf_snoc_last]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
            rw [hB.2.2.2.2.2 w0 hw0 z u hu]
            cases (wiresOf B.gates (bitsOf t z)).getD (B.off w0) false <;>
              cases decide (dotProduct (B.slope w0) u = 1) <;> decide)
        exact hwrap_one _ hres.1 rfl hres.2
      · rcases rest2 with _ | ⟨_, _⟩
        ·
          have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
          have hw1 : w1 < k + t + gs.length := hback w1 (by rw [hg]; simp)
          let gs' := B.gates ++ [⟨.mod 2, [B.off w0, B.off w1]⟩]
          have hleg' : legalGates t gs' :=
            legalGates_snoc hB.2.1
              (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hB.2.2.2.2.1 w0 hw0; exact hB.2.2.2.2.1 w1 hw1)
              ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩
          have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
            rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
          have hres := branch_eval_add_gate hleg hB gs' [⟨.mod 2, [B.off w0, B.off w1]⟩] rfl hleg' hcost'
            (t + B.gates.length) (by simp [gs']) (B.slope w0 + B.slope w1) (fun z u hu => by
              rw [hop, hg]
              have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
              rw [hidx, wiresOf_snoc_last]
              simp only [List.map_cons, List.map_nil, GateOp.eval]
              rw [hB.2.2.2.2.2 w0 hw0 z u hu, hB.2.2.2.2.2 w1 hw1 z u hu, add_dotProduct, zmod2_add_decide]
              cases (wiresOf B.gates (bitsOf t z)).getD (B.off w0) false <;>
                cases (wiresOf B.gates (bitsOf t z)).getD (B.off w1) false <;>
                cases decide (dotProduct (B.slope w0) u = 1) <;>
                cases decide (dotProduct (B.slope w1) u = 1) <;> decide)
          exact hwrap_one _ hres.1 rfl hres.2
        · exfalso; have := hshape.1; rw [hg] at this; simp at this
  ·
    rcases hg : g.inputs with _ | ⟨w0, rest⟩
    · simp [hg] at hlen1
    · rcases rest with _ | ⟨_, _⟩
      · have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        let gs' := B.gates ++ [⟨.not, [B.off w0]⟩]
        have hleg' : legalGates t gs' :=
          legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 w0 hw0)
            ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
        have hcost' : costGates gs' + B.r ≤ costGates (gs ++ [g]) := by
          rw [costGates_snoc_zero B.gates _ (by simp)]; have := hB.2.2.1; omega
        have hres := branch_eval_add_gate hleg hB gs' [⟨.not, [B.off w0]⟩] rfl hleg' hcost'
          (t + B.gates.length) (by simp [gs']) (B.slope w0) (fun z u hu => by
            rw [hop, hg]
            have hidx : t + B.gates.length = (bitsOf t z).length + B.gates.length := by rw [bitsOf_len]
            rw [hidx, wiresOf_snoc_last]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
            rw [hB.2.2.2.2.2 w0 hw0 z u hu]
            cases (wiresOf B.gates (bitsOf t z)).getD (B.off w0) false <;>
              cases decide (dotProduct (B.slope w0) u = 1) <;> decide)
        exact hwrap_one _ hres.1 rfl hres.2
      · simp [hg] at hlen1

lemma build_branch_list (k t : ℕ) (gs : List Gate) (hleg : legalGates (k + t) gs) :
    ∃ L : List (Branch k t),
      0 < L.length ∧
      (∀ B ∈ L, ValidBranch gs B) ∧
      ∀ (z : Fin t → F2) (x : Fin k → F2),
        ∃! idx : Fin L.length, x - (L.get idx).pos z ∈ (L.get idx).U := by
  induction gs using List.reverseRecOn with
  | nil =>
    let g0 : List Gate := [⟨.or, []⟩]
    let B0 : Branch k t :=
      ⟨0, ⊤, g0, fun _ => t,
        fun w => if w < k then t else w - k,
        fun w => if hw : w < k then Pi.single ⟨w, hw⟩ (1 : F2) else 0⟩
    have hleg0 : legalGates t g0 := by
      have hnil : legalGates t [] := ⟨fun j hj => by simp at hj, fun h hh => by simp at hh⟩
      exact legalGates_snoc hnil (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
    have hg0_val : ∀ z : Fin t → F2, (wiresOf g0 (bitsOf t z)).getD t false = false := by
      intro z
      have h1 := wiresOf_snoc_last_eq ([] : List Gate) ⟨.or, []⟩ (bitsOf t z) (bitsOf_len t z)
      simpa [g0, GateOp.eval] using h1
    have hpos0 : ∀ z : Fin t → F2, B0.pos z = 0 := by
      intro z; funext j
      simp only [Branch.pos, B0, Pi.zero_apply, hg0_val z]
      rfl
    have hvalid0 : ValidBranch [] B0 := by
      refine ⟨?_, hleg0, ?_, fun _ => by simp [B0, g0], ?_, ?_⟩
      · simp [B0]
      · simp [B0, g0, costGates]
      · intro w hw
        simp only [List.length_nil, Nat.add_zero] at hw
        simp only [B0, g0, List.length_singleton]
        split_ifs <;> omega
      · intro w hw z u _
        simp only [List.length_nil, Nat.add_zero] at hw
        rw [hpos0 z, zero_add]
        conv_lhs => simp only [wiresOf, Circuit.wires, List.foldl_nil]
        simp only [B0]
        by_cases hwk : w < k
        · simp only [hwk, ↓reduceIte, ↓reduceDIte]
          have h1 : (bitsOf k u ++ bitsOf t z).getD w false = decide (u ⟨w, hwk⟩ = 1) := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [bitsOf_len]; exact hwk)]
            exact bitsOf_getD k u ⟨w, hwk⟩
          rw [h1, hg0_val z]
          simp
        · simp only [hwk, ↓reduceIte, ↓reduceDIte]
          have h1 : (bitsOf k u ++ bitsOf t z).getD w false = (bitsOf t z).getD (w - k) false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [bitsOf_len]; omega),
                bitsOf_len, List.getD_eq_getElem?_getD]
          have h2 : (wiresOf g0 (bitsOf t z)).getD (w - k) false = (bitsOf t z).getD (w - k) false :=
            wiresOf_getD_lt g0 (bitsOf t z) (by rw [bitsOf_len]; omega)
          rw [h1, h2]; simp
    refine ⟨[B0], by simp, fun b hb => by simp at hb; subst hb; exact hvalid0, fun z x => ?_⟩
    exact ⟨⟨0, by simp⟩, by simp [B0], fun idx _ => Fin.ext (by have := idx.isLt; simp only [List.length_singleton] at this; change idx.val = 0; omega)⟩
  | append_singleton gs g ih =>
    have hpre := legalGates_prefix hleg
    rcases ih hpre.1 with ⟨L, hLpos, hLval, hLpart⟩
    have hstep_all : ∀ idx : Fin L.length, ∃ Lc : List (Branch k t),
        (∀ B' ∈ Lc, ValidBranch (gs ++ [g]) B') ∧
        ∀ (z : Fin t → F2) (x : Fin k → F2),
          (x - (L.get idx).pos z ∈ (L.get idx).U → ∃! j : Fin Lc.length, x - (Lc.get j).pos z ∈ (Lc.get j).U) ∧
          (x - (L.get idx).pos z ∉ (L.get idx).U → ∀ j : Fin Lc.length, x - (Lc.get j).pos z ∉ (Lc.get j).U) :=
      fun idx => step_single_branch (L.get idx) hleg (hLval _ (List.get_mem L idx))
    let children : Fin L.length → List (Branch k t) := fun idx => (hstep_all idx).choose
    have hchildren_spec : ∀ idx : Fin L.length,
        (∀ B' ∈ children idx, ValidBranch (gs ++ [g]) B') ∧
        ∀ (z : Fin t → F2) (x : Fin k → F2),
          (x - (L.get idx).pos z ∈ (L.get idx).U →
            ∃! j : Fin (children idx).length, x - ((children idx).get j).pos z ∈ ((children idx).get j).U) ∧
          (x - (L.get idx).pos z ∉ (L.get idx).U →
            ∀ j : Fin (children idx).length, x - ((children idx).get j).pos z ∉ ((children idx).get j).U) :=
      fun idx => (hstep_all idx).choose_spec
    let L' : List (Branch k t) := (List.finRange L.length).flatMap children
    have hpart_L' : ∀ (z : Fin t → F2) (x : Fin k → F2),
        ∃! idx' : Fin L'.length, x - (L'.get idx').pos z ∈ (L'.get idx').U := by
      intro z x
      have hflat_bij : ∀ (ms : List (Fin L.length)),
          (∀ a ∈ ms, ∀ b ∈ ms, a = b → True) →
          ms.Nodup →
          ∀ (p : Branch k t → Prop),
            (∃ idx ∈ ms, (∃! j : Fin (children idx).length, p ((children idx).get j)) ∧
              ∀ idx2 ∈ ms, idx2 ≠ idx → ∀ j : Fin (children idx2).length, ¬ p ((children idx2).get j)) →
            ∃! q : Fin (ms.flatMap children).length, p ((ms.flatMap children).get q) := by
        intro ms _ hnd p
        induction ms with
        | nil => rintro ⟨_, h, _⟩; simp at h
        | cons a ms ihms =>
          rintro ⟨idx, hidx, huniq, hrest⟩
          rw [List.nodup_cons] at hnd
          change ∃! q : Fin (children a ++ ms.flatMap children).length, p ((children a ++ ms.flatMap children).get q)
          rcases List.mem_cons.mp hidx with rfl | hmem
          · rcases huniq with ⟨j0, hj0, hj0u⟩
            refine ⟨⟨j0.val, by simp only [List.length_append]; omega⟩, ?_, ?_⟩
            · dsimp only
              rw [List.get_eq_getElem, List.getElem_append_left j0.isLt]
              exact hj0
            · intro q hq
              by_cases hql : q.val < (children idx).length
              · have hq' : p ((children idx).get ⟨q.val, hql⟩) := by
                  simpa [List.get_eq_getElem, List.getElem_append_left hql] using hq
                have := hj0u ⟨q.val, hql⟩ hq'
                exact Fin.ext (by simpa using congrArg Fin.val this)
              · exfalso
                have hqr : q.val - (children idx).length < (ms.flatMap children).length := by
                  have := q.isLt; simp only [List.length_append] at this; omega
                have hq' : p ((ms.flatMap children).get ⟨q.val - (children idx).length, hqr⟩) := by
                  simpa [List.get_eq_getElem, List.getElem_append_right (by omega : (children idx).length ≤ q.val)] using hq
                have hmem_b : (ms.flatMap children).get ⟨q.val - (children idx).length, hqr⟩ ∈ ms.flatMap children :=
                  List.get_mem _ _
                rcases List.mem_flatMap.mp hmem_b with ⟨idx2, hidx2, hb2⟩
                rcases List.mem_iff_get.mp hb2 with ⟨j2, hj2⟩
                have hne2 : idx2 ≠ idx := fun heq => hnd.1 (heq ▸ hidx2)
                exact hrest idx2 (List.mem_cons_of_mem idx hidx2) hne2 j2 (hj2.symm ▸ hq')
          · have hih := ihms (fun _ _ _ _ _ => trivial) hnd.2 ⟨idx, hmem, huniq, fun idx2 hi2 hne2 => hrest idx2 (List.mem_cons_of_mem a hi2) hne2⟩
            rcases hih with ⟨q0, hq0, hq0u⟩
            refine ⟨⟨(children a).length + q0.val, by simp only [List.length_append]; omega⟩, ?_, ?_⟩
            · simp only [List.get_eq_getElem, List.getElem_append_right (by omega : (children a).length ≤ (children a).length + q0.val),
                Nat.add_sub_cancel_left]
              exact hq0
            · intro q hq
              by_cases hql : q.val < (children a).length
              · exfalso
                have hq' : p ((children a).get ⟨q.val, hql⟩) := by
                  simpa [List.get_eq_getElem, List.getElem_append_left hql] using hq
                have hne : a ≠ idx := fun heq => hnd.1 (heq ▸ hmem)
                exact hrest a (List.mem_cons_self) hne ⟨q.val, hql⟩ hq'
              · have hqr : q.val - (children a).length < (ms.flatMap children).length := by
                  have := q.isLt; simp only [List.length_append] at this; omega
                have hq' : p ((ms.flatMap children).get ⟨q.val - (children a).length, hqr⟩) := by
                  simpa [List.get_eq_getElem, List.getElem_append_right (by omega : (children a).length ≤ q.val)] using hq
                have heq := hq0u ⟨q.val - (children a).length, hqr⟩ hq'
                apply Fin.ext
                have := congrArg Fin.val heq
                dsimp at this ⊢; omega
      rcases hLpart z x with ⟨idx0, hidx0, hidx0u⟩
      apply hflat_bij (List.finRange L.length) (fun _ _ _ _ _ => trivial) (List.nodup_finRange L.length)
        (fun B => x - B.pos z ∈ B.U)
      refine ⟨idx0, List.mem_finRange idx0, ((hchildren_spec idx0).2 z x).1 hidx0, ?_⟩
      intro idx2 _ hne2
      have hnot2 : x - (L.get idx2).pos z ∉ (L.get idx2).U := fun hm => hne2 (hidx0u idx2 hm)
      exact ((hchildren_spec idx2).2 z x).2 hnot2
    have hL'pos : 0 < L'.length := by
      rcases hpart_L' 0 0 with ⟨idx0, _, _⟩
      exact Nat.pos_of_ne_zero (fun h0 => by have := idx0.isLt; omega)
    refine ⟨L', hL'pos, ?_, hpart_L'⟩
    intro B' hB'
    rcases List.mem_flatMap.mp hB' with ⟨idx, _, hmem⟩
    exact (hchildren_spec idx).1 B' hmem



lemma vec_eq_sum_single {k : ℕ} (v : Fin k → F2) :
    v = ∑ i : Fin k, v i • Pi.single i (1 : F2) := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

lemma decomp_835 (k t : ℕ) (C : Circuit) (hC : legalGates (k + t) C.gates) :
    ∃ (N : ℕ) (r : Fin N → ℕ) (U : Fin N → Submodule F2 (Fin k → F2)) (a : Fin N → (Fin k → F2))
      (D : Fin N → Circuit) (tap : Fin N → Fin k → ℕ),
      let pos := fun (i : Fin N) (z : Fin t → F2) (j : Fin k) =>
        if ((D i).wires (bitsOf t z)).getD (tap i j) false then (1 : F2) else 0
      0 < N ∧ (∀ i, Module.finrank F2 (U i) + r i = k ∧ legalGates t (D i).gates ∧
        costGates (D i).gates + r i ≤ costGates C.gates ∧ (D i).output < t + (D i).size ∧
        ∀ j, tap i j < t + (D i).size) ∧
      (∀ (z : Fin t → F2) (x : Fin k → F2), ∃! i : Fin N, x - pos i z ∈ U i) ∧
      ∀ (i : Fin N) (z : Fin t → F2) (u : Fin k → F2), u ∈ U i →
        C.eval (bitsOf k (pos i z + u) ++ bitsOf t z) =
          Bool.xor ((D i).eval (bitsOf t z)) (decide (dotProduct (a i) u = 1)) := by
  rcases build_branch_list k t C.gates hC with ⟨L, hLpos, hLval, hLpart⟩
  by_cases hout : C.output < k + t + C.gates.length
  · refine ⟨L.length,
      fun i => (L.get i).r,
      fun i => (L.get i).U,
      fun i => (L.get i).slope C.output,
      fun i => ⟨(L.get i).gates, (L.get i).off C.output⟩,
      fun i => (L.get i).tap,
      hLpos, ?_, ?_, ?_⟩
    · intro i
      have hBi := hLval (L.get i) (List.get_mem L i)
      exact ⟨hBi.1, hBi.2.1, hBi.2.2.1, hBi.2.2.2.2.1 C.output hout, hBi.2.2.2.1⟩
    · intro z x
      exact hLpart z x
    · intro i z u hu
      have hBi := hLval (L.get i) (List.get_mem L i)
      exact hBi.2.2.2.2.2 C.output hout z u hu
  · refine ⟨L.length,
      fun i => (L.get i).r,
      fun i => (L.get i).U,
      fun _ => 0,
      fun i => ⟨(L.get i).gates ++ [⟨.or, []⟩], t + (L.get i).gates.length⟩,
      fun i => (L.get i).tap,
      hLpos, ?_, ?_, ?_⟩
    · intro i
      have hBi := hLval (L.get i) (List.get_mem L i)
      refine ⟨hBi.1, ?_, ?_, by simp [Circuit.size], ?_⟩
      · exact legalGates_snoc hBi.2.1 (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
      · have hc0 := costGates_snoc_zero (L.get i).gates ⟨.or, []⟩ (by simp)
        have := hBi.2.2.1
        change costGates ((L.get i).gates ++ [⟨.or, []⟩]) + (L.get i).r ≤ costGates C.gates
        omega
      · intro j
        simp only [Circuit.size, List.length_append, List.length_singleton]
        have := hBi.2.2.2.1 j; omega
    · intro z x
      have hpeq : ∀ i : Fin L.length,
          (fun j : Fin k => if (Circuit.wires ⟨(L.get i).gates ++ [⟨.or, []⟩], t + (L.get i).gates.length⟩ (bitsOf t z)).getD ((L.get i).tap j) false then (1 : F2) else 0) =
          (L.get i).pos z := by
        intro i; funext j
        have hBi := hLval (L.get i) (List.get_mem L i)
        change (if (wiresOf ((L.get i).gates ++ [⟨.or, []⟩]) (bitsOf t z)).getD ((L.get i).tap j) false then (1 : F2) else 0) = _
        rw [wiresOf_append_getD_lt (L.get i).gates [⟨.or, []⟩] _
          (by rw [bitsOf_len]; exact hBi.2.2.2.1 j)]
        rfl
      have hconv : (fun i : Fin L.length => x - (fun j : Fin k => if (Circuit.wires ⟨(L.get i).gates ++ [⟨.or, []⟩], t + (L.get i).gates.length⟩ (bitsOf t z)).getD ((L.get i).tap j) false then (1 : F2) else 0) ∈ (L.get i).U) =
          (fun i : Fin L.length => x - (L.get i).pos z ∈ (L.get i).U) := by
        funext i; rw [hpeq i]
      exact (congrArg (fun P => ∃! i : Fin L.length, P i) hconv).mpr (hLpart z x)
    · intro i z u _
      have hlhs : ∀ v : Fin k → F2, C.eval (bitsOf k v ++ bitsOf t z) = false := by
        intro v
        have hclen : (C.wires (bitsOf k v ++ bitsOf t z)).length = k + t + C.gates.length := by
          have h := wiresOf_len C.gates (bitsOf k v ++ bitsOf t z)
          simp only [List.length_append, bitsOf_len] at h
          exact h
        unfold Circuit.eval
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      have hrhs : (Circuit.mk ((L.get i).gates ++ [⟨.or, []⟩]) (t + (L.get i).gates.length)).eval (bitsOf t z) = false := by
        unfold Circuit.eval
        change (wiresOf ((L.get i).gates ++ [⟨.or, []⟩]) (bitsOf t z)).getD (t + (L.get i).gates.length) false = false
        rw [wiresOf_snoc_last_eq (L.get i).gates ⟨.or, []⟩ (bitsOf t z) (bitsOf_len t z)]
        simp [GateOp.eval]
      rw [hlhs, hrhs]
      simp

def signBool (b : Bool) : ℤ := if b then -1 else 1

lemma signBool_xor (a b : Bool) : signBool (Bool.xor a b) = signBool a * signBool b := by
  cases a <;> cases b <;> rfl

lemma agree_eq_sign (b1 b2 b3 : Bool) :
    (if b1 = Bool.xor b2 b3 then (1 : ℤ) else -1) = signBool (Bool.xor b1 b2) * signBool b3 := by
  cases b1 <;> cases b2 <;> cases b3 <;> rfl

lemma eq_f2_sign (a b : F2) :
    (if a = b then (1 : ℤ) else -1) = signBool (decide (a = 1)) * signBool (decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

lemma signBool_abs_one (b : Bool) : |signBool b| = 1 := by
  cases b <;> simp [signBool]

lemma card_submodule_zmod2 {k : ℕ} (U : Submodule F2 (Fin k → F2)) :
    Fintype.card U = 2 ^ Module.finrank F2 U := by
  let b := Module.finBasis F2 U
  rw [Fintype.card_congr b.equivFun.toEquiv]
  simp [ZMod.card]

def orthoComp {k : ℕ} (U : Submodule F2 (Fin k → F2)) : Submodule F2 (Fin k → F2) :=
  { carrier := {w | ∀ u ∈ U, dotProduct w u = 0},
    zero_mem' := fun u _ => by simp, smul_mem' := fun c {a} ha u hu => by rw [smul_dotProduct, ha u hu, smul_zero], add_mem' := fun {a b} ha hb u hu => by rw [add_dotProduct, ha u hu, hb u hu, add_zero] }

lemma mem_orthoComp {k : ℕ} (U : Submodule F2 (Fin k → F2)) (w : Fin k → F2) :
    w ∈ orthoComp U ↔ ∀ u ∈ U, dotProduct w u = 0 := Iff.rfl

lemma finrank_orthoComp {k : ℕ} (U : Submodule F2 (Fin k → F2)) :
    Module.finrank F2 (orthoComp U) + Module.finrank F2 U = k := by
  let b := Module.finBasis F2 U
  let Φ : (Fin k → F2) →ₗ[F2] (Fin (Module.finrank F2 U) → F2) :=
    { toFun := fun w i => dotProduct w (b i).val
      map_add' := fun x y => by funext i; exact add_dotProduct x y (b i).val
      map_smul' := fun c x => by funext i; simp [smul_dotProduct] }
  have hker : LinearMap.ker Φ = orthoComp U := by
    ext w
    simp only [LinearMap.mem_ker, mem_orthoComp]
    constructor
    · intro hw u hu
      have hrep : (⟨u, hu⟩ : U) = ∑ i, b.repr ⟨u, hu⟩ i • b i := (b.sum_repr ⟨u, hu⟩).symm
      have hu_eq : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i).val := by
        have hval := congrArg Subtype.val hrep
        simp only [Submodule.coe_sum, SetLike.val_smul] at hval
        exact hval
      rw [hu_eq, dotProduct_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [dotProduct_smul, smul_eq_mul]
      have hwi : dotProduct w (b i).val = 0 := congrFun hw i
      rw [hwi, mul_zero]
    · intro hw
      funext i
      exact hw (b i).val (b i).property
  have hsurj : LinearMap.range Φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro target
    let f : U →ₗ[F2] F2 :=
      { toFun := fun u => ∑ i, target i * b.repr u i
        map_add' := fun x y => by simp only [map_add, Finsupp.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := fun c x => by
          simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring }
    obtain ⟨V', hcompl⟩ := Submodule.exists_isCompl U
    let π : (Fin k → F2) →ₗ[F2] U := Submodule.linearProjOfIsCompl U V' hcompl
    let g : (Fin k → F2) →ₗ[F2] F2 := f.comp π
    let w : Fin k → F2 := fun j => g (Pi.single j 1)
    refine ⟨w, ?_⟩
    funext i
    have hgx : ∀ x : Fin k → F2, dotProduct w x = g x := by
      intro x
      conv_rhs => rw [vec_eq_sum_single x]
      rw [map_sum]
      simp only [dotProduct, map_smul, smul_eq_mul, w]
      refine Finset.sum_congr rfl fun j _ => by ring
    change dotProduct w (b i).val = target i
    rw [hgx (b i).val]
    have hpi : π (b i).val = b i := Submodule.linearProjOfIsCompl_apply_left hcompl (b i)
    simp only [g, LinearMap.comp_apply, hpi, f, LinearMap.coe_mk, AddHom.coe_mk, Module.Basis.repr_self]
    simp [Finsupp.single_apply]
  have hrk := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hsurj, hker, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrk
  omega

lemma sum_sign_dot_submodule {k : ℕ} (U : Submodule F2 (Fin k → F2)) (w : Fin k → F2) :
    (∑ u : U, signBool (decide (dotProduct w u.val = 1))) =
      if w ∈ orthoComp U then (2 : ℤ) ^ Module.finrank F2 U else 0 := by
  by_cases hw : w ∈ orthoComp U
  · simp only [hw, ↓reduceIte]
    have hterm : ∀ u : U, signBool (decide (dotProduct w u.val = 1)) = 1 := by
      intro u
      rw [hw u.val u.property]
      rfl
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      card_submodule_zmod2, Nat.cast_pow, Nat.cast_ofNat]
  · simp only [hw, ↓reduceIte]
    have hex : ∃ u0 ∈ U, dotProduct w u0 = 1 := by
      by_contra hnot
      apply hw
      intro u hu
      rcases zmod2_cases (dotProduct w u) with h0 | h1
      · exact h0
      · exact absurd ⟨u, hu, h1⟩ hnot
    rcases hex with ⟨u0, hu0, hdot⟩
    let e : U ≃ U :=
      { toFun := fun u => u + ⟨u0, hu0⟩
        invFun := fun u => u + ⟨u0, hu0⟩
        left_inv := fun u => Subtype.ext (by
          show u.val + u0 + u0 = u.val
          rw [add_assoc, zmod2_vec_add_self, add_zero])
        right_inv := fun u => Subtype.ext (by
          show u.val + u0 + u0 = u.val
          rw [add_assoc, zmod2_vec_add_self, add_zero]) }
    set S := ∑ u : U, signBool (decide (dotProduct w u.val = 1))
    have hS : S = -S := by
      calc S = ∑ u : U, signBool (decide (dotProduct w (e u).val = 1)) :=
            (Equiv.sum_comp e (fun u : U => signBool (decide (dotProduct w u.val = 1)))).symm
        _ = ∑ u : U, -signBool (decide (dotProduct w u.val = 1)) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            show signBool (decide (dotProduct w (u.val + u0) = 1)) = _
            rw [dotProduct_add, hdot, zmod2_add_decide]
            cases decide (dotProduct w u.val = 1) <;> rfl
        _ = -S := by rw [Finset.sum_neg_distrib]
    omega

lemma sum_sign_dot_univ {k : ℕ} (w : Fin k → F2) (hw : w ≠ 0) :
    (∑ x : Fin k → F2, signBool (decide (dotProduct w x = 1))) = 0 := by
  have hex : ∃ j : Fin k, w j = 1 := by
    by_contra hnot; push Not at hnot
    apply hw; funext j
    rcases zmod2_cases (w j) with h0 | h1
    · exact h0
    · exact absurd h1 (hnot j)
  rcases hex with ⟨j, hj⟩
  let u0 : Fin k → F2 := Pi.single j 1
  have hdot : dotProduct w u0 = 1 := by
    simp [u0, dotProduct_single, hj]
  let e : (Fin k → F2) ≃ (Fin k → F2) :=
    { toFun := fun x => x + u0
      invFun := fun x => x + u0
      left_inv := fun x => by dsimp only; rw [add_assoc, zmod2_vec_add_self, add_zero]
      right_inv := fun x => by dsimp only; rw [add_assoc, zmod2_vec_add_self, add_zero] }
  set S := ∑ x : Fin k → F2, signBool (decide (dotProduct w x = 1))
  have hS : S = -S := by
    calc S = ∑ x : Fin k → F2, signBool (decide (dotProduct w (e x) = 1)) :=
          (Equiv.sum_comp e (fun x => signBool (decide (dotProduct w x = 1)))).symm
      _ = ∑ x : Fin k → F2, -signBool (decide (dotProduct w x = 1)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          show signBool (decide (dotProduct w (x + u0) = 1)) = _
          rw [dotProduct_add, hdot, zmod2_add_decide]
          cases decide (dotProduct w x = 1) <;> rfl
      _ = -S := by rw [Finset.sum_neg_distrib]
  omega

lemma cost_zero_affine {k : ℕ} (gs : List Gate) (hleg : legalGates k gs) (hcost : costGates gs = 0) :
    ∀ w < k + gs.length, ∃ (lin : Fin k → F2) (c : F2), ∀ y : Fin k → F2,
      (wiresOf gs (bitsOf k y)).getD w false = decide (dotProduct lin y + c = 1) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w hw
    simp only [List.length_nil, Nat.add_zero] at hw
    refine ⟨Pi.single ⟨w, hw⟩ 1, 0, fun y => ?_⟩
    change (bitsOf k y).getD (⟨w, hw⟩ : Fin k).val false = _
    rw [bitsOf_getD, single_dotProduct, one_mul, add_zero]
  | append_singleton gs g ih =>
    have hpre := legalGates_prefix hleg
    have hcost_app : costGates gs + costGates [g] = 0 := by
      rw [← costGates_append]; exact hcost
    have hcost_gs : costGates gs = 0 := by omega
    have hnot_nl : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) := by
      intro hnl
      have h1 : costGates (gs ++ [g]) = costGates gs + 1 := costGates_snoc_one gs g hnl
      omega
    have hih := ih hpre.1 hcost_gs
    intro w hw
    simp only [List.length_append, List.length_singleton] at hw
    by_cases hlt : w < k + gs.length
    · obtain ⟨lin, c, hlin⟩ := hih w hlt
      refine ⟨lin, c, fun y => ?_⟩
      rw [wiresOf_append_getD_lt gs [g] (bitsOf k y) (by rw [bitsOf_len]; exact hlt)]
      exact hlin y
    · have hweq : w = k + gs.length := by omega
      subst hweq
      have hback := hpre.2.1
      have hshape := hpre.2.2
      have eval_snoc : ∀ y : Fin k → F2,
          (wiresOf (gs ++ [g]) (bitsOf k y)).getD (k + gs.length) false =
            g.op.eval (g.inputs.map fun i => (wiresOf gs (bitsOf k y)).getD i false) :=
        fun y => wiresOf_snoc_last_eq gs g (bitsOf k y) (bitsOf_len k y)
      rcases hshape.2 with hop | hop | hop | ⟨hop, hlen1⟩
      · rcases hg : g.inputs with _ | ⟨w0, rest⟩
        · refine ⟨0, 1, fun y => ?_⟩
          rw [eval_snoc y, hop, hg]; simp [GateOp.eval]
        · rcases rest with _ | ⟨w1, rest2⟩
          · obtain ⟨lin, c, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
            refine ⟨lin, c, fun y => ?_⟩
            rw [eval_snoc y, hop, hg]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact hlin y
          · rcases rest2 with _ | ⟨_, _⟩
            · exfalso; exact hnot_nl ⟨Or.inl hop, by rw [hg]; rfl⟩
            · exfalso; have := hshape.1; rw [hg] at this; simp at this
      · rcases hg : g.inputs with _ | ⟨w0, rest⟩
        · refine ⟨0, 0, fun y => ?_⟩
          rw [eval_snoc y, hop, hg]; simp [GateOp.eval]
        · rcases rest with _ | ⟨w1, rest2⟩
          · obtain ⟨lin, c, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
            refine ⟨lin, c, fun y => ?_⟩
            rw [eval_snoc y, hop, hg]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact hlin y
          · rcases rest2 with _ | ⟨_, _⟩
            · exfalso; exact hnot_nl ⟨Or.inr hop, by rw [hg]; rfl⟩
            · exfalso; have := hshape.1; rw [hg] at this; simp at this
      · rcases hg : g.inputs with _ | ⟨w0, rest⟩
        · refine ⟨0, 1, fun y => ?_⟩
          rw [eval_snoc y, hop, hg]; simp [GateOp.eval]
        · rcases rest with _ | ⟨w1, rest2⟩
          · obtain ⟨lin, c, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
            refine ⟨lin, c + 1, fun y => ?_⟩
            rw [eval_snoc y, hop, hg]
            simp only [List.map_cons, List.map_nil, hlin y, GateOp.eval]
            rcases zmod2_cases (dotProduct lin y + c) with h | h <;> rw [← add_assoc, h] <;> decide
          · rcases rest2 with _ | ⟨_, _⟩
            · obtain ⟨lin0, c0, hlin0⟩ := hih w0 (hback w0 (by rw [hg]; simp))
              obtain ⟨lin1, c1, hlin1⟩ := hih w1 (hback w1 (by rw [hg]; simp))
              refine ⟨lin0 + lin1, c0 + c1 + 1, fun y => ?_⟩
              rw [eval_snoc y, hop, hg]
              simp only [List.map_cons, List.map_nil, hlin0 y, hlin1 y, GateOp.eval, add_dotProduct]
              have hrw : dotProduct lin0 y + dotProduct lin1 y + (c0 + c1 + 1) =
                  (dotProduct lin0 y + c0) + (dotProduct lin1 y + c1) + 1 := by ring
              rw [hrw]
              rcases zmod2_cases (dotProduct lin0 y + c0) with h0 | h0 <;>
                rcases zmod2_cases (dotProduct lin1 y + c1) with h1 | h1 <;>
                rw [h0, h1] <;> decide
            · exfalso; have := hshape.1; rw [hg] at this; simp at this
      · rcases hg : g.inputs with _ | ⟨w0, rest⟩
        · simp [hg] at hlen1
        · rcases rest with _ | ⟨_, _⟩
          · obtain ⟨lin, c, hlin⟩ := hih w0 (hback w0 (by rw [hg]; simp))
            refine ⟨lin, c + 1, fun y => ?_⟩
            rw [eval_snoc y, hop, hg]
            simp only [List.map_cons, List.map_nil, hlin y, GateOp.eval, List.headD_cons]
            rcases zmod2_cases (dotProduct lin y + c) with h | h <;> rw [← add_assoc, h] <;> decide
          · simp [hg] at hlen1

def isQuad {s : ℕ} (q : (Fin s → F2) → F2) : Prop :=
  ∃ (b : F2) (a : Fin s → F2) (M : Fin s → Fin s → F2), ∀ v,
    q v = b + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j

lemma isQuad_const {s : ℕ} (b : F2) : isQuad (s := s) (fun _ => b) :=
  ⟨b, 0, fun _ _ => 0, fun _ => by simp⟩

lemma isQuad_affine {s : ℕ} (a : Fin s → F2) (b : F2) :
    isQuad (s := s) (fun v => dotProduct a v + b) :=
  ⟨b, a, fun _ _ => 0, fun v => by simp [add_comm]⟩

lemma isQuad_add {s : ℕ} {q1 q2 : (Fin s → F2) → F2} (h1 : isQuad q1) (h2 : isQuad q2) :
    isQuad (fun v => q1 v + q2 v) := by
  rcases h1 with ⟨b1, a1, M1, h1⟩
  rcases h2 with ⟨b2, a2, M2, h2⟩
  refine ⟨b1 + b2, a1 + a2, fun i j => M1 i j + M2 i j, fun v => ?_⟩
  dsimp only
  rw [h1 v, h2 v, add_dotProduct]
  have hsum : (∑ i : Fin s, ∑ j : Fin s, (M1 i j + M2 i j) * v i * v j) =
      (∑ i : Fin s, ∑ j : Fin s, M1 i j * v i * v j) +
      (∑ i : Fin s, ∑ j : Fin s, M2 i j * v i * v j) := by
    simp only [add_mul, Finset.sum_add_distrib]
  rw [hsum]; ring

lemma isQuad_mul_affine {s : ℕ} (u1 u2 : Fin s → F2) (c1 c2 : F2) :
    isQuad (fun v => (dotProduct u1 v + c1) * (dotProduct u2 v + c2)) := by
  refine ⟨c1 * c2, c2 • u1 + c1 • u2, fun i j => u1 i * u2 j, fun v => ?_⟩
  dsimp only
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have hprod : dotProduct u1 v * dotProduct u2 v =
      ∑ i : Fin s, ∑ j : Fin s, u1 i * u2 j * v i * v j := by
    simp only [dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [← hprod]; ring

lemma isQuad_finset_sum {s : ℕ} {ι : Type*} (S : Finset ι) (f : ι → (Fin s → F2) → F2)
    (hf : ∀ i ∈ S, isQuad (f i)) :
    isQuad (fun v => ∑ i ∈ S, f i v) := by
  induction S using Finset.induction_on with
  | empty => simpa using isQuad_const (s := s) 0
  | @insert a S ha ih =>
    have hfa := hf a (Finset.mem_insert_self a S)
    have hfs := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have heq : (fun v => ∑ i ∈ insert a S, f i v) = (fun v => f a v + ∑ i ∈ S, f i v) := by
      funext v; exact Finset.sum_insert ha
    rw [heq]
    exact isQuad_add hfa hfs

lemma linear_comp_affine {k s : ℕ} (B : (Fin s → F2) →ₗ[F2] (Fin k → F2))
    (a : Fin k → F2) (u : Fin k → F2) (c : F2) :
    ∃ (u' : Fin s → F2) (c' : F2), ∀ v : Fin s → F2,
      dotProduct u (a + B v) + c = dotProduct u' v + c' := by
  refine ⟨fun i => dotProduct u (B (Pi.single i 1)), dotProduct u a + c, fun v => ?_⟩
  rw [dotProduct_add]
  have hBv : dotProduct u (B v) = dotProduct (fun i => dotProduct u (B (Pi.single i 1))) v := by
    conv_lhs => rw [vec_eq_sum_single v, map_sum, dotProduct_sum]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hBv]; ring

lemma forward_decomp_bounds (k s : ℕ) (g : (Fin k → F2) → F2) (C : Circuit)
    (hleg : legalGates (2 * k) C.gates) (hcost : costGates C.gates ≤ s) :
    ∃ (N : ℕ) (r : Fin N → ℕ) (W : Fin N → Submodule F2 (Fin k → F2))
      (a : Fin N → (Fin k → F2)) (D : Fin N → Circuit) (tap : Fin N → Fin k → ℕ),
      let pos := fun (i : Fin N) (y : Fin k → F2) (j : Fin k) =>
        if ((D i).wires (bitsOf k y)).getD (tap i j) false then (1 : F2) else 0
      let Bval := fun i : Fin N =>
        (∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0).natAbs
      0 < N ∧
      (∀ i, Module.finrank F2 (W i) = r i ∧ r i ≤ k ∧ legalGates k (D i).gates ∧
        costGates (D i).gates + r i ≤ s ∧ (D i).output < k + (D i).size ∧
        ∀ j, tap i j < k + (D i).size) ∧
      (∑ i : Fin N, 2 ^ (k - r i)) = 2 ^ k ∧
      (∀ i, Bval i ≤ 2 ^ (r i)) ∧
      (∑ x : Fin k → F2, ∑ y : Fin k → F2,
        if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs ≤ ∑ i : Fin N, 2 ^ (k - r i) * Bval i := by
  have hleg' : legalGates (k + k) C.gates := by rwa [show k + k = 2 * k by omega]
  rcases decomp_835 k k C hleg' with ⟨N, r, U, a, D, tap, hNpos, hmeta, hpart, heval⟩
  let pos := fun (i : Fin N) (y : Fin k → F2) (j : Fin k) =>
    if ((D i).wires (bitsOf k y)).getD (tap i j) false then (1 : F2) else 0
  let W : Fin N → Submodule F2 (Fin k → F2) := fun i => orthoComp (U i)
  have hW_dim : ∀ i, Module.finrank F2 (W i) = r i := by
    intro i
    dsimp only [W]
    have h1 := finrank_orthoComp (U i)
    have h2 := (hmeta i).1
    omega
  have hU_dim : ∀ i, Module.finrank F2 (U i) = k - r i := by
    intro i; have := (hmeta i).1; omega
  let hpart_equiv : ∀ y : Fin k → F2, (Σ i : Fin N, U i) ≃ (Fin k → F2) := fun y =>
    let idxOf : (Fin k → F2) → Fin N := fun x => (hpart y x).choose
    have hidx_mem : ∀ x, x - pos (idxOf x) y ∈ U (idxOf x) := fun x => (hpart y x).choose_spec.1
    have hidx_uniq : ∀ x i, x - pos i y ∈ U i → i = idxOf x := fun x i hi => (hpart y x).choose_spec.2 i hi
    { toFun := fun p => pos p.1 y + p.2.val
      invFun := fun x => ⟨idxOf x, ⟨x - pos (idxOf x) y, hidx_mem x⟩⟩
      left_inv := fun ⟨i, ⟨u, hu⟩⟩ => by
        have hmem : pos i y + u - pos i y ∈ U i := by simpa using hu
        have hi : idxOf (pos i y + u) = i := (hidx_uniq (pos i y + u) i hmem).symm
        dsimp only
        generalize hidx_mem (pos i y + u) = hjm
        revert hjm
        generalize idxOf (pos i y + u) = j at hi ⊢
        subst hi
        intro _
        congr 1
        apply Subtype.ext
        simp
      right_inv := fun x => by
        show pos (idxOf x) y + (x - pos (idxOf x) y) = x
        abel }
  have hsum_pow : (∑ i : Fin N, 2 ^ (k - r i)) = 2 ^ k := by
    have hcard_sig : Fintype.card (Σ i : Fin N, U i) = ∑ i : Fin N, 2 ^ (k - r i) := by
      rw [Fintype.card_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [card_submodule_zmod2, hU_dim i]
    have hcard_V : Fintype.card (Fin k → F2) = 2 ^ k := by simp [ZMod.card]
    rw [← hcard_sig, ← hcard_V]
    exact Fintype.card_congr (hpart_equiv 0)
  have hprof : ∀ y : Fin k → F2,
      (∑ x : Fin k → F2, signBool (Bool.xor (C.eval (bitsOf k x ++ bitsOf k y)) (decide (dotProduct x y = 1)))) =
      ∑ i : Fin N, (2 : ℤ) ^ (k - r i) *
        (if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1)))
        else 0) := by
    intro y
    rw [← Equiv.sum_comp (hpart_equiv y), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hterm : ∀ u : U i,
        signBool (Bool.xor (C.eval (bitsOf k (pos i y + u.val) ++ bitsOf k y))
          (decide (dotProduct (pos i y + u.val) y = 1))) =
        signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
          signBool (decide (dotProduct (y - a i) u.val = 1)) := by
      intro u
      rw [heval i y u.val u.property, add_dotProduct, zmod2_add_decide, signBool_xor, signBool_xor, signBool_xor]
      have hdot_eq : dotProduct (y - a i) u.val = dotProduct (a i) u.val + dotProduct u.val y := by
        rw [zmod2_vec_sub_eq_add, add_dotProduct, dotProduct_comm u.val y]; ring
      rw [hdot_eq, zmod2_add_decide, signBool_xor, signBool_xor]
      ring
    have heq_fn : ∀ u : U i, hpart_equiv y ⟨i, u⟩ = pos i y + u.val := fun _ => by dsimp [hpart_equiv]
    simp_rw [heq_fn, hterm, ← Finset.mul_sum, sum_sign_dot_submodule (U i) (y - a i), hU_dim i]
    dsimp only [W]
    split_ifs <;> ring
  refine ⟨N, r, W, a, D, tap, hNpos, ?_, hsum_pow, ?_, ?_⟩
  · intro i
    have hm := hmeta i
    exact ⟨hW_dim i, by omega, hm.2.1, by omega, hm.2.2.2.1, hm.2.2.2.2⟩
  · intro i
    dsimp only
    have hle : (∑ y : Fin k → F2, if y - a i ∈ W i then
        signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
          signBool (decide (g y = 1))
      else 0).natAbs ≤
        ∑ y : Fin k → F2, (if y - a i ∈ W i then (1 : ℕ) else 0) := by
      have htri := Finset.abs_sum_le_sum_abs
        (fun y : Fin k → F2 => if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0) Finset.univ
      have habs : ∀ y : Fin k → F2,
          |(if y - a i ∈ W i then
            signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
              signBool (decide (g y = 1))
          else 0)| = if y - a i ∈ W i then (1 : ℤ) else 0 := by
        intro y
        split_ifs
        · rw [abs_mul, signBool_abs_one, signBool_abs_one, mul_one]
        · simp
      simp_rw [habs] at htri
      have hnat : ((∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0).natAbs : ℤ) ≤ ∑ y : Fin k → F2, if y - a i ∈ W i then (1 : ℤ) else 0 := by
        simpa [Int.natCast_natAbs] using htri
      exact_mod_cast hnat
    have hcard_coset : (∑ y : Fin k → F2, if y - a i ∈ W i then (1 : ℕ) else 0) = 2 ^ (r i) := by
      rw [← Finset.card_filter]
      let eW : W i ≃ {y : Fin k → F2 // y - a i ∈ W i} :=
        { toFun := fun w => ⟨a i + w.val, by simpa using w.property⟩
          invFun := fun y => ⟨y.val - a i, y.property⟩
          left_inv := fun w => Subtype.ext (by show a i + w.val - a i = w.val; abel)
          right_inv := fun y => Subtype.ext (by show a i + (y.val - a i) = y.val; abel) }
      have hc : (Finset.univ.filter (fun y : Fin k → F2 => y - a i ∈ W i)).card =
          Fintype.card {y : Fin k → F2 // y - a i ∈ W i} := (Fintype.card_subtype _).symm
      rw [hc, ← Fintype.card_congr eW, card_submodule_zmod2, hW_dim i]
    exact le_trans hle (le_of_eq hcard_coset)
  · dsimp only
    have hsum_eq : (∑ x : Fin k → F2, ∑ y : Fin k → F2,
        if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1) =
        ∑ i : Fin N, (2 : ℤ) ^ (k - r i) *
          (∑ y : Fin k → F2, if y - a i ∈ W i then
            signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
              signBool (decide (g y = 1))
          else 0) := by
      rw [Finset.sum_comm]
      have hy : ∀ y : Fin k → F2,
          (∑ x : Fin k → F2, if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
            then (1 : ℤ) else -1) =
          (∑ i : Fin N, (2 : ℤ) ^ (k - r i) *
            (if y - a i ∈ W i then
              signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
                signBool (decide (g y = 1))
            else 0)) := by
        intro y
        have hstep : ∀ x : Fin k → F2,
            (if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1) then (1 : ℤ) else -1) =
            signBool (Bool.xor (C.eval (bitsOf k x ++ bitsOf k y)) (decide (dotProduct x y = 1))) *
              signBool (decide (g y = 1)) := by
          intro x
          rw [zmod2_add_decide, agree_eq_sign]
        simp_rw [hstep, ← Finset.sum_mul, hprof y, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> ring
      simp_rw [hy]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    rw [hsum_eq]
    have htri := Finset.abs_sum_le_sum_abs
      (fun i : Fin N => (2 : ℤ) ^ (k - r i) *
        (∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0)) Finset.univ
    have habs_term : ∀ i : Fin N,
        |(2 : ℤ) ^ (k - r i) *
          (∑ y : Fin k → F2, if y - a i ∈ W i then
            signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
              signBool (decide (g y = 1))
          else 0)| =
        ((2 ^ (k - r i) * (∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0).natAbs : ℕ) : ℤ) := by
      intro i
      rw [abs_mul, abs_of_nonneg (by positivity), ← Int.natCast_natAbs]
      push_cast; rfl
    simp_rw [habs_term] at htri
    have hnat : ((∑ i : Fin N, (2 : ℤ) ^ (k - r i) *
        (∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0)).natAbs : ℤ) ≤
        ((∑ i : Fin N, 2 ^ (k - r i) * (∑ y : Fin k → F2, if y - a i ∈ W i then
          signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
            signBool (decide (g y = 1))
        else 0).natAbs : ℕ) : ℤ) := by
      simpa [Int.natCast_natAbs, Nat.cast_sum] using htri
    exact Int.ofNat_le.mp hnat

lemma viaCircuit_to_viaFlat (k s : ℕ) (g : (Fin k → F2) → F2) (T : ℕ)
    (hbig : 2 ^ (k + s) < 2 * T)
    (C : Circuit) (hleg : legalGates (2 * k) C.gates) (hcost : costGates C.gates ≤ s)
    (hT : T ≤ (∑ x : Fin k → F2, ∑ y : Fin k → F2,
      if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1).natAbs) :
    ∃ (B : (Fin s → F2) →ₗ[F2] (Fin k → F2)) (a : Fin k → F2) (q : (Fin s → F2) → F2),
      Function.Injective B ∧ isQuad q ∧
      T ≤ 2 ^ k * (∑ v : Fin s → F2, if g (a + B v) = q v then (1 : ℤ) else -1).natAbs := by
  rcases forward_decomp_bounds k s g C hleg hcost with ⟨N, r, W, a, D, tap, hNpos, hmeta, hsum, hB, hraw⟩
  set pos := fun (i : Fin N) (y : Fin k → F2) (j : Fin k) =>
    if ((D i).wires (bitsOf k y)).getD (tap i j) false then (1 : F2) else 0
  set Bval := fun i : Fin N =>
    (∑ y : Fin k → F2, if y - a i ∈ W i then
      signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
        signBool (decide (g y = 1))
    else 0).natAbs
  have hex : ∃ i0 : Fin N, T ≤ 2 ^ k * Bval i0 := by
    by_contra hnot
    push Not at hnot
    have hlt_sum : ∑ i : Fin N, 2 ^ (k - r i) * (2 ^ k * Bval i) < ∑ i : Fin N, 2 ^ (k - r i) * T := by
      apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hNpos⟩⟩)
      intro i _
      exact Nat.mul_lt_mul_of_pos_left (hnot i) (Nat.pow_pos (by omega))
    have hlhs : ∑ i : Fin N, 2 ^ (k - r i) * (2 ^ k * Bval i) = 2 ^ k * ∑ i : Fin N, 2 ^ (k - r i) * Bval i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hrhs : ∑ i : Fin N, 2 ^ (k - r i) * T = 2 ^ k * T := by
      rw [← Finset.sum_mul, hsum]
    rw [hlhs, hrhs] at hlt_sum
    have hle : 2 ^ k * T ≤ 2 ^ k * ∑ i : Fin N, 2 ^ (k - r i) * Bval i :=
      Nat.mul_le_mul_left _ (le_trans hT hraw)
    omega
  rcases hex with ⟨i0, hi0⟩
  have hm := hmeta i0
  have hBi0 : Bval i0 ≤ 2 ^ (r i0) := hB i0
  have hpow_lt : 2 ^ (k + s) < 2 ^ (k + r i0 + 1) := by
    have h1 : 2 * T ≤ 2 * (2 ^ k * Bval i0) := Nat.mul_le_mul_left 2 hi0
    have h2 : 2 * (2 ^ k * Bval i0) ≤ 2 * (2 ^ k * 2 ^ (r i0)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (2 ^ k) hBi0)
    have h3 : 2 * (2 ^ k * 2 ^ (r i0)) = 2 ^ (k + r i0 + 1) := by
      rw [pow_succ, pow_add]; ring
    omega
  have hs_le_r : s ≤ r i0 := by
    by_contra hlt
    push Not at hlt
    have hle : 2 ^ (k + r i0 + 1) ≤ 2 ^ (k + s) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hr_eq : r i0 = s := by omega
  have hcost0 : costGates (D i0).gates = 0 := by omega
  have haff := cost_zero_affine (D i0).gates hm.2.2.1 hcost0
  obtain ⟨d_out, c_out, hd_out⟩ := haff (D i0).output hm.2.2.2.2.1
  have htap_aff : ∀ j : Fin k, ∃ (lin : Fin k → F2) (c : F2), ∀ y : Fin k → F2,
      pos i0 y j = dotProduct lin y + c := by
    intro j
    obtain ⟨lin, c, hlin⟩ := haff (tap i0 j) (hm.2.2.2.2.2 j)
    refine ⟨lin, c, fun y => ?_⟩
    dsimp only [pos]
    change (if (wiresOf (D i0).gates (bitsOf k y)).getD (tap i0 j) false then (1 : F2) else 0) = _
    rw [hlin y, zmod2_decide_bool]
  choose L_tap c_tap hL_tap using htap_aff
  have hdimW : Module.finrank F2 (W i0) = s := by rw [hm.1, hr_eq]
  let e : (Fin s → F2) ≃ₗ[F2] W i0 :=
    LinearEquiv.ofFinrankEq (Fin s → F2) (W i0) (by rw [Module.finrank_fin_fun, hdimW])
  let B : (Fin s → F2) →ₗ[F2] (Fin k → F2) := (W i0).subtype.comp e.toLinearMap
  have hB_inj : Function.Injective B := Subtype.val_injective.comp e.injective
  let Q : (Fin k → F2) → F2 := fun y =>
    (dotProduct d_out y + c_out) + ∑ j : Fin k, (dotProduct (L_tap j) y + c_tap j) * y j
  let q : (Fin s → F2) → F2 := fun v => Q (a i0 + B v)
  have hq_quad : isQuad q := by
    obtain ⟨u0, b0, hu0⟩ := linear_comp_affine B (a i0) d_out c_out
    have hq0 : isQuad (fun v => dotProduct d_out (a i0 + B v) + c_out) := by
      have : (fun v => dotProduct d_out (a i0 + B v) + c_out) = (fun v => dotProduct u0 v + b0) :=
        funext hu0
      rw [this]; exact isQuad_affine u0 b0
    have hq_sum : isQuad (fun v => ∑ j : Fin k, (dotProduct (L_tap j) (a i0 + B v) + c_tap j) * (a i0 + B v) j) := by
      apply isQuad_finset_sum Finset.univ
      intro j _
      obtain ⟨u1, b1, hu1⟩ := linear_comp_affine B (a i0) (L_tap j) (c_tap j)
      obtain ⟨u2, b2, hu2⟩ := linear_comp_affine B (a i0) (Pi.single j 1) 0
      have hprod : (fun v => (dotProduct (L_tap j) (a i0 + B v) + c_tap j) * (a i0 + B v) j) =
          (fun v => (dotProduct u1 v + b1) * (dotProduct u2 v + b2)) := by
        funext v
        have hcoord : (a i0 + B v) j = dotProduct u2 v + b2 := by
          have := hu2 v
          simpa [single_dotProduct] using this
        rw [hu1 v, hcoord]
      rw [hprod]
      exact isQuad_mul_affine u1 u2 b1 b2
    exact isQuad_add hq0 hq_sum
  have hBval_eq : Bval i0 = (∑ v : Fin s → F2, if g (a i0 + B v) = q v then (1 : ℤ) else -1).natAbs := by
    dsimp only [Bval]
    congr 1
    rw [← Finset.sum_filter]
    let f_inj : (Fin s → F2) → (Fin k → F2) := fun v => a i0 + B v
    have hbij : Finset.univ.image f_inj = Finset.univ.filter (fun y : Fin k → F2 => y - a i0 ∈ W i0) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f_inj]
      constructor
      · rintro ⟨v, rfl⟩
        have : a i0 + B v - a i0 = (e v).val := by
          show a i0 + (e v).val - a i0 = (e v).val; abel
        rw [this]; exact (e v).property
      · intro hy
        refine ⟨e.symm ⟨y - a i0, hy⟩, ?_⟩
        show a i0 + (e (e.symm ⟨y - a i0, hy⟩)).val = y
        rw [LinearEquiv.apply_symm_apply]
        exact add_sub_cancel (a i0) y
    rw [← hbij, Finset.sum_image (fun v1 _ v2 _ h => hB_inj (add_left_cancel h))]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hDeval : (D i0).eval (bitsOf k (f_inj v)) = decide (dotProduct d_out (f_inj v) + c_out = 1) :=
      hd_out (f_inj v)
    have hdotp : dotProduct (pos i0 (f_inj v)) (f_inj v) =
        ∑ j : Fin k, (dotProduct (L_tap j) (f_inj v) + c_tap j) * (f_inj v) j := by
      simp only [dotProduct, hL_tap]
    rw [hDeval, hdotp, ← zmod2_add_decide]
    change signBool (decide (q v = 1)) * signBool (decide (g (a i0 + B v) = 1)) = _
    rw [eq_f2_sign, mul_comm]
  refine ⟨B, a i0, q, hB_inj, hq_quad, ?_⟩
  rwa [← hBval_eq]

lemma andStep (N : ℕ) (gs : List Gate) (a b : ℕ)
    (hl : legalGates N gs) (ha : a < N + gs.length) (hb : b < N + gs.length) :
    let out := N + gs.length
    let next := gs ++ [⟨.and, [a,b]⟩]
    legalGates N next ∧ costGates next = costGates gs + 1 ∧ out < N + next.length ∧
      ∀ w : List Bool, w.length = N →
        (wiresOf next w).getD out false =
          ((wiresOf gs w).getD a false && (wiresOf gs w).getD b false) := by
  refine ⟨legalGates_snoc hl ?_ ⟨by simp, Or.inl rfl⟩,
    costGates_snoc_one gs _ ⟨Or.inl rfl, rfl⟩, by simp, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  · intro w hw
    rw [wiresOf_snoc_last_eq _ _ _ hw]
    simp [GateOp.eval]

lemma xorProducts {ι : Type} (N : ℕ) (A B : ι → ℕ) (base : List Gate)
    (hl : legalGates N base) (hb : ∀ i, A i < N + base.length ∧ B i < N + base.length)
    (S : Finset ι) :
    ∃ (ext : List Gate) (out : ℕ),
      legalGates N (base ++ ext) ∧
      costGates (base ++ ext) = costGates base + S.card ∧ out < N + (base ++ ext).length ∧
      ∀ w : List Bool, w.length = N →
        (wiresOf (base ++ ext) w).getD out false = decide ((∑ i ∈ S,
          (if (wiresOf base w).getD (A i) false then (1 : F2) else 0) *
          (if (wiresOf base w).getD (B i) false then (1 : F2) else 0)) = 1) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨[⟨.or, []⟩], N + base.length, ?_, ?_, by simp, ?_⟩
    · exact legalGates_snoc hl (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
    · exact costGates_snoc_zero base _ (by simp)
    · intro w hw
      rw [wiresOf_snoc_last_eq _ _ _ hw]
      simp [GateOp.eval]
  | @insert i S hi ih =>
    rcases ih with ⟨ext, acc, hleg, hcost, hacc, hsem⟩
    let gs := base ++ ext
    let prod := N + gs.length
    let gs' := gs ++ [⟨.and, [A i, B i]⟩]
    obtain ⟨hleg', hcost', hprod, hsem'⟩ :=
      andStep N gs (A i) (B i) hleg
        (by simp [gs]; have := (hb i).1; omega)
        (by simp [gs]; have := (hb i).2; omega)
    have hacc' : acc < N + gs'.length := by
      simp only [gs', List.length_append, List.length_singleton]
      exact Nat.lt_succ_of_lt hacc
    obtain ⟨hleg'', hcost'', hlen'', hsem''⟩ :=
      addXor_step N gs' acc prod hleg' hacc' hprod
    let add : List Gate := [⟨.and, [A i, B i]⟩, ⟨.mod 2, [acc,prod]⟩, ⟨.not, [N + gs'.length]⟩]
    have heq : base ++ (ext ++ add) = gs' ++ [⟨.mod 2, [acc,prod]⟩, ⟨.not, [N + gs'.length]⟩] := by
      simp [gs', gs, add, List.append_assoc]
    refine ⟨ext ++ add, N + gs'.length + 1, ?_, ?_, ?_, ?_⟩
    · rw [heq]
      exact hleg''
    · rw [heq, hcost'', hcost', Finset.card_insert_of_notMem hi]
      rw [hcost, Nat.add_assoc]
    · rw [heq, hlen'']
      omega
    · intro w hw
      rw [heq, hsem'' w hw, hsem' w hw]
      have preserve (j : ℕ) (hj : j < N + base.length) :
          (wiresOf gs w).getD j false = (wiresOf base w).getD j false :=
        wiresOf_append_getD_lt base ext w (by rwa [hw])
      rw [wiresOf_append_getD_lt gs _ w (by rwa [hw]), hsem w hw,
        preserve _ (hb i).1, preserve _ (hb i).2, Finset.sum_insert hi,
        zmod2_add_decide, zmod2_mul_decide, zmod2_bool_decide, zmod2_bool_decide,
        Bool.xor_comm]

lemma appended_input {k : ℕ} (x y : Fin k → F2) (i : Fin k) :
    (bitsOf k x ++ bitsOf k y).getD i.val false = decide (x i = 1) ∧
    (bitsOf k x ++ bitsOf k y).getD (k + i.val) false = decide (y i = 1) := by
  constructor
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa [bitsOf] using i.isLt)]
    exact bitsOf_getD k x i
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [bitsOf])]
    rw [bitsOf_len, Nat.add_sub_cancel_left]
    exact bitsOf_getD k y i

lemma witnessCircuit {n : ℕ} (a b c : Fin n) :
    ∃ C : Circuit, legalGates (2 * (n+1)) C.gates ∧ costGates C.gates = n+1 ∧
      ∀ x y : Fin (n+1) → F2, C.eval (bitsOf _ x ++ bitsOf _ y) = decide
        ((∑ i : Fin n, x i.succ * y i.succ) + y a.succ * y b.succ * y c.succ = 1) := by
  classical
  let k := n+1
  let N := 2*k
  let Y := fun (i : Fin n) => k + i.succ.val
  let s : List Gate := [⟨.and,[Y b,Y c]⟩]
  have hy (i : Fin n) : Y i < N := by dsimp [Y,N,k]; have := i.isLt; omega
  have hnil : legalGates N [] := ⟨fun j hj => by simp at hj, by simp⟩
  obtain ⟨hs, hsc, hst, hse⟩ := andStep N [] (Y b) (Y c) hnil
    (by simpa using hy b) (by simpa using hy c)
  change legalGates N s at hs
  change costGates s = costGates [] + 1 at hsc
  change N < N + s.length at hst
  have hxa : a.succ.val < N + s.length := by dsimp [N,k]; have := a.isLt; omega
  let base := s ++ [⟨.mod 2,[a.succ.val,N]⟩,⟨.not,[N+s.length]⟩]
  let splice := N+s.length+1
  obtain ⟨hl, hcost, hlen, hsplice⟩ := addXor_step N s a.succ.val N hs hxa hst
  change legalGates N base at hl
  change costGates base = costGates s at hcost
  change base.length = s.length+2 at hlen
  let A := fun i : Fin n => if i = a then splice else i.succ.val
  have hbound (i : Fin n) : A i < N + base.length ∧ Y i < N + base.length := by
    refine ⟨?_, by have := hy i; omega⟩
    simp only [A]
    split_ifs
    · dsimp [splice]; omega
    · dsimp [N,k]; have := i.isLt; omega
  obtain ⟨ext,out,hcl,hcc,_,hce⟩ := xorProducts N A Y base hl hbound Finset.univ
  refine ⟨⟨base ++ ext,out⟩,hcl,?_,?_⟩
  · rw [hcc, hcost, hsc]
    simp [costGates]
    omega
  · intro x y
    let w := bitsOf k x ++ bitsOf k y
    have hw : w.length = N := by simp [w,N,bitsOf]; omega
    change (wiresOf (base ++ ext) w).getD out false = _
    rw [hce w hw]
    have hY (i : Fin n) : (wiresOf base w).getD (Y i) false = decide (y i.succ = 1) := by
      rw [wiresOf_getD_lt _ _ (by rw [hw]; exact hy i)]
      exact (appended_input x y i.succ).2
    have hX (i : Fin n) :
        (wiresOf base w).getD (A i) false =
          decide (x i.succ + (if i = a then y b.succ * y c.succ else 0) = 1) := by
      by_cases hi : i = a
      · subst i
        simp only [A, if_pos]
        rw [hsplice w hw]
        have hsval : (wiresOf s w).getD N false =
            (decide (y b.succ = 1) && decide (y c.succ = 1)) := by
          exact (hse w hw).trans (by
            change (w.getD (Y b) false && w.getD (Y c) false) = _
            rw [(appended_input x y b.succ).2, (appended_input x y c.succ).2])
        rw [wiresOf_getD_lt _ _ (by rw [hw]; dsimp [N,k]; have := a.isLt; omega),
          (appended_input x y a.succ).1, hsval, zmod2_add_decide, zmod2_mul_decide]
      · simp only [A, if_neg hi, add_zero]
        rw [wiresOf_getD_lt _ _ (by rw [hw]; dsimp [N,k]; have := i.isLt; omega)]
        exact (appended_input x y i.succ).1
    simp_rw [hX,hY,zmod2_decide_bool,add_mul,Finset.sum_add_distrib]
    have he (i : Fin n) :
        (if i = a then y b.succ * y c.succ else 0) * y i.succ =
          if i = a then y b.succ * y c.succ * y a.succ else 0 := by
      split_ifs with h <;> simp [h]
    simp_rw [he]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ a)]
    ring_nf

lemma rawWitness {n : ℕ} (a b c : Fin n) (g : (Fin (n+1) → F2) → F2)
    (hg : ∀ y, y 0 = 0 → g y = y a.succ * y b.succ * y c.succ) :
    ∃ C : Circuit, legalGates (2 * (n+1)) C.gates ∧ costGates C.gates ≤ n+1 ∧
      2 * (∑ x : Fin (n+1) → F2, ∑ y : Fin (n+1) → F2,
        if C.eval (bitsOf _ x ++ bitsOf _ y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs = 2^(2*(n+1)) := by
  classical
  obtain ⟨C,hl,hc,he⟩ := witnessCircuit a b c
  refine ⟨C,hl,hc.le,?_⟩
  rw [Finset.sum_comm]
  have inner (y : Fin (n+1) → F2) :
      (∑ x : Fin (n+1) → F2, if C.eval (bitsOf _ x ++ bitsOf _ y) =
        decide (dotProduct x y + g y = 1) then (1 : ℤ) else -1) =
      if y 0 = 0 then (2 : ℤ)^(n+1) else 0 := by
    rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n+1) => F2), Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    have hterm (t : F2) (u : Fin n → F2) :
        (if C.eval (bitsOf _ (Fin.cons t u) ++ bitsOf _ y) =
          decide (dotProduct (Fin.cons t u) y + g y = 1) then (1 : ℤ) else -1) =
        signBool (decide (t * y 0 + (g y + y a.succ * y b.succ * y c.succ) = 1)) := by
      rw [he]
      have heq : dotProduct (Fin.cons t u) y = t * y 0 + ∑ i : Fin n, u i * y i.succ := by
        rw [dotProduct, Fin.sum_univ_succ]
        rfl
      simp only [Fin.cons_succ, heq]
      suffices ∀ d p g' t' : F2,
          (if decide (d + p = 1) = decide (t' + d + g' = 1) then (1 : ℤ) else -1) =
            signBool (decide (t' + (g' + p) = 1)) from this _ _ _ _
      intro d p g' t'
      fin_cases d <;> fin_cases p <;> fin_cases g' <;> fin_cases t' <;> decide
    have hcomp (t : F2) (u : Fin n → F2) :
        (Fin.consEquiv fun _ : Fin (n+1) => F2) (t,u) = Fin.cons t u := rfl
    simp_rw [hcomp,hterm]
    have htwo (f : F2 → ℤ) : ∑ t : F2, f t = f 0 + f 1 := by
      exact Fin.sum_univ_two f
    simp_rw [htwo]
    rcases zmod2_cases (y 0) with h | h
    · rw [if_pos h]
      simp [h, hg y h, show ∀ d : F2, d+d=0 by intro d; fin_cases d <;> decide,
        signBool, ZMod.card, pow_succ]
    · rw [if_neg (h ▸ by decide)]
      have hv : ∀ z : F2, signBool (decide (z = 1)) +
          signBool (decide (z = 0)) = 0 := by
        intro z
        fin_cases z <;> decide
      simp [h, hv]
  simp_rw [inner]
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n+1) => F2), Fintype.sum_prod_type]
  have htwo (f : F2 → ℤ) : ∑ t : F2, f t = f 0 + f 1 := Fin.sum_univ_two f
  rw [htwo]
  simp [ZMod.card, pow_succ, Int.natAbs_mul, Int.natAbs_pow]
  ring
lemma isQuad_affine_precomp {k s : ℕ} {q : (Fin k → F2) → F2} (hq : isQuad q)
    (B : (Fin s → F2) →ₗ[F2] (Fin k → F2)) (a : Fin k → F2) :
    isQuad (fun v => q (a + B v)) := by
  obtain ⟨b,d,M,hq⟩ := hq
  simp_rw [hq]
  apply isQuad_add
  · obtain ⟨d',b',h⟩ := linear_comp_affine B a d b
    exact (funext fun v => (add_comm b _).trans (h v)) ▸ isQuad_affine d' b'
  · apply isQuad_finset_sum Finset.univ
    intro i _
    apply isQuad_finset_sum Finset.univ
    intro j _
    obtain ⟨u,c,hu⟩ := linear_comp_affine B a (Pi.single i (M i j)) 0
    obtain ⟨w,d,hw⟩ := linear_comp_affine B a (Pi.single j 1) 0
    have hprod : (fun v => M i j * (a + B v) i * (a + B v) j) =
        (fun v => (dotProduct u v + c) * (dotProduct w v + d)) := by
      funext v
      rw [← hu v, ← hw v]
      simp [single_dotProduct, mul_add]
    rw [hprod]
    exact isQuad_mul_affine u w c d

lemma rawUpper {k : ℕ} (g : (Fin k → F2) → F2)
    (hg : ∀ q, isQuad q →
      2 * (∑ y : Fin k → F2, if q y = g y then (1 : ℤ) else -1).natAbs < 2^k)
    (C : Circuit) (hl : legalGates (2*k) C.gates) (hc : costGates C.gates ≤ k) :
    2 * (∑ x : Fin k → F2, ∑ y : Fin k → F2,
      if C.eval (bitsOf _ x ++ bitsOf _ y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1).natAbs ≤ 2^(2*k) := by
  by_contra! hh
  rw [two_mul] at hh
  obtain ⟨B,a,q,hB,hq,hcorr⟩ := viaCircuit_to_viaFlat k k g _ hh C hl hc le_rfl
  let Eₗ := LinearEquiv.ofBijective B ⟨hB, Finite.surjective_of_injective hB⟩
  let E := Eₗ.toEquiv
  let e : (Fin k → F2) ≃ (Fin k → F2) := E.trans (Equiv.addLeft a)
  let q' := fun y => q (e.symm y)
  have hinv (y : Fin k → F2) : e.symm y = E.symm (y - a) := by
    change E.symm (-a + y) = E.symm (y - a)
    rw [sub_eq_neg_add]
  let L := Eₗ.symm.toLinearMap
  have hq' : isQuad q' := by
    convert isQuad_affine_precomp hq L (L (-a)) using 1
    funext y
    change q (e.symm y) = q (L (-a) + L y)
    rw [hinv, ← map_add, ← sub_eq_neg_add]
    rfl
  have hrew : (∑ v : Fin k → F2, if g (a + B v) = q v then (1 : ℤ) else -1) =
      ∑ y : Fin k → F2, if q' y = g y then (1 : ℤ) else -1 := by
    rw [← Equiv.sum_comp e (fun y => if q' y = g y then (1 : ℤ) else -1)]
    refine Finset.sum_congr rfl fun v _ => ?_
    change (if g (a + B v) = q v then (1 : ℤ) else -1) =
      if q (e.symm (e v)) = g (a + B v) then 1 else -1
    rw [e.symm_apply_apply]
    simp only [eq_comm]
  rw [hrew] at hcorr
  let T := (∑ x : Fin k → F2, ∑ y : Fin k → F2,
    if C.eval (bitsOf _ x ++ bitsOf _ y) = decide (dotProduct x y + g y = 1)
    then (1 : ℤ) else -1).natAbs
  have hbound : 2 * T ≤ 2 ^ k *
      (2 * (∑ y : Fin k → F2, if q' y = g y then (1 : ℤ) else -1).natAbs) := by
    calc
      2 * T ≤ 2 * (2 ^ k * _) := Nat.mul_le_mul_left 2 hcorr
      _ = _ := by ring
  have hlt := Nat.mul_lt_mul_of_pos_left (hg q' hq') (Nat.pow_pos (by decide) : 0 < 2 ^ k)
  rw [← pow_add] at hlt
  change 2 ^ (k+k) < 2 * T at hh
  omega

end CircuitProof

namespace Bias

abbrev F2 := ZMod 2

def consF2 {m : ℕ} (b : F2) (u : Fin m → F2) : Fin (m + 1) → F2 :=
  Fin.cons (α := fun _ => F2) b u

lemma consF2_zero {m : ℕ} (b : F2) (u : Fin m → F2) : consF2 b u 0 = b := rfl

lemma consF2_succ {m : ℕ} (b : F2) (u : Fin m → F2) (i : Fin m) :
    consF2 b u i.succ = u i := rfl

lemma consF2_self_tail {m : ℕ} (y : Fin (m + 1) → F2) : consF2 (y 0) (Fin.tail y) = y :=
  Fin.cons_self_tail y

lemma consF2_inj {m : ℕ} (b : F2) : Function.Injective (consF2 (m := m) b) := by
  intro u v huv
  funext i
  have := congrFun huv i.succ
  simpa [consF2_succ] using this

lemma f2_add_self (a : F2) : a + a = 0 := by
  fin_cases a <;> decide

lemma f2_sub_eq_add (a b : F2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

lemma f2_cases (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma f2_vec_add_self {ι : Type*} (x : ι → F2) : x + x = 0 := by
  funext i
  exact f2_add_self (x i)

lemma card_filter_add_not {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_filter]
  tauto

def chi (a : F2) : ℤ := if a = 0 then 1 else -1

lemma chi_zero : chi 0 = 1 := rfl

lemma chi_one : chi 1 = -1 := rfl

lemma chi_add (a b : F2) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> rfl

lemma chi_eq (a b : F2) : (if a = b then (1 : ℤ) else -1) = chi (a + b) := by
  fin_cases a <;> fin_cases b <;> rfl

lemma chi_abs (a : F2) : |chi a| = 1 := by
  fin_cases a <;> decide

lemma chi_le_one (a : F2) : chi a ≤ 1 := by
  fin_cases a <;> decide

lemma chi_sum {α : Type*} (s : Finset α) (f : α → F2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

lemma sum_chi_addHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Finset (ι → F2)) (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (φ : (ι → F2) → F2) (hφ : ∀ x ∈ H, ∀ y ∈ H, φ (x + y) = φ x + φ y) :
    (∑ x ∈ H, chi (φ x)) = if ∀ x ∈ H, φ x = 0 then (H.card : ℤ) else 0 := by
  split_ifs with hall
  · have h1 : ∀ x ∈ H, chi (φ x) = 1 := fun x hx => by rw [hall x hx]; rfl
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  · push Not at hall
    obtain ⟨x₀, hx₀, hne⟩ := hall
    have hx₀1 : φ x₀ = 1 := by
      rcases f2_cases (φ x₀) with h | h
      · exact absurd h hne
      · exact h
    have hbij : ∑ x ∈ H, chi (φ x) = ∑ x ∈ H, chi (φ (x + x₀)) := by
      refine Finset.sum_bij (fun x _ => x + x₀) ?_ ?_ ?_ ?_
      · intro x hx; exact hadd x hx x₀ hx₀
      · intro x _ y _ hxy
        have := congrArg (· + x₀) hxy
        simpa [add_assoc, f2_vec_add_self] using this
      · intro y hy
        refine ⟨y + x₀, hadd y hy x₀ hx₀, ?_⟩
        simp [add_assoc, f2_vec_add_self]
      · intro x _
        congr 2
        rw [add_assoc, f2_vec_add_self, add_zero]
    have hneg : ∑ x ∈ H, chi (φ (x + x₀)) = - ∑ x ∈ H, chi (φ x) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hφ x hx x₀ hx₀, hx₀1, chi_add, chi_one]
      ring
    linarith

lemma sum_chi_dot {m : ℕ} (a : Fin m → F2) :
    (∑ x : Fin m → F2, chi (dotProduct a x)) = if a = 0 then (2 : ℤ) ^ m else 0 := by
  have h := sum_chi_addHom (Finset.univ : Finset (Fin m → F2))
    (fun _ _ _ _ => Finset.mem_univ _) (fun x => dotProduct a x)
    (fun x _ y _ => dotProduct_add a x y)
  have hiff : (∀ x ∈ (Finset.univ : Finset (Fin m → F2)), dotProduct a x = 0) ↔ a = 0 := by
    constructor
    · intro hall
      funext i
      have hi := hall (Pi.single i 1) (Finset.mem_univ _)
      simpa [dotProduct_single] using hi
    · intro ha x _
      rw [ha, zero_dotProduct]
  rw [h]
  by_cases ha : a = 0
  · simp only [ha, ↓reduceIte]
    have hall : ∀ x ∈ (Finset.univ : Finset (Fin m → F2)), dotProduct 0 x = 0 :=
      fun x _ => zero_dotProduct x
    simp [hall]
  · simp only [mt hiff.mp ha, ha, ↓reduceIte]

def IsQuad {ι : Type*} [Fintype ι] (q : (ι → F2) → F2) : Prop :=
  ∃ (b : F2) (a : ι → F2) (M : ι → ι → F2), ∀ x,
    q x = b + dotProduct a x + ∑ i, ∑ j, M i j * x i * x j

def polar {ι : Type*} (q : (ι → F2) → F2) (h t : ι → F2) : F2 :=
  q (h + t) + q h + q t + q 0

lemma polar_of_quad {ι : Type*} [Fintype ι] (b : F2) (a : ι → F2) (M : ι → ι → F2)
    (q : (ι → F2) → F2)
    (hq : ∀ x, q x = b + dotProduct a x + ∑ i, ∑ j, M i j * x i * x j) (h t : ι → F2) :
    polar q h t = ∑ i, ∑ j, (M i j + M j i) * h i * t j := by
  unfold polar
  rw [hq (h + t), hq h, hq t, hq 0]
  have h0 : dotProduct a (0 : ι → F2) = 0 := dotProduct_zero a
  have hm0 : (∑ i : ι, ∑ j : ι, M i j * (0 : ι → F2) i * (0 : ι → F2) j) = 0 := by simp
  rw [h0, hm0, dotProduct_add]
  have hba : (b + (dotProduct a h + dotProduct a t) +
      ∑ i, ∑ j, M i j * (h + t) i * (h + t) j) +
      (b + dotProduct a h + ∑ i, ∑ j, M i j * h i * h j) +
      (b + dotProduct a t + ∑ i, ∑ j, M i j * t i * t j) + (b + 0 + 0) =
      ((∑ i, ∑ j, M i j * (h + t) i * (h + t) j) +
        (∑ i, ∑ j, M i j * h i * h j) +
        (∑ i, ∑ j, M i j * t i * t j)) := by
    have hbb : b + b = 0 := f2_add_self b
    have hdh : dotProduct a h + dotProduct a h = 0 := f2_add_self _
    have hdt : dotProduct a t + dotProduct a t = 0 := f2_add_self _
    calc _ = (b + b) + (b + b) + (dotProduct a h + dotProduct a h) +
          (dotProduct a t + dotProduct a t) +
          ((∑ i, ∑ j, M i j * (h + t) i * (h + t) j) +
            (∑ i, ∑ j, M i j * h i * h j) +
            (∑ i, ∑ j, M i j * t i * t j)) := by ring
      _ = _ := by rw [hbb, hdh, hdt]; ring
  rw [hba]
  have hterm : ∀ i j : ι,
      M i j * (h + t) i * (h + t) j + M i j * h i * h j + M i j * t i * t j =
      M i j * h i * t j + M i j * t i * h j := by
    intro i j
    simp only [Pi.add_apply]
    have h1 : M i j * h i * h j + M i j * h i * h j = 0 := f2_add_self _
    have h2 : M i j * t i * t j + M i j * t i * t j = 0 := f2_add_self _
    calc M i j * (h i + t i) * (h j + t j) + M i j * h i * h j + M i j * t i * t j
        = (M i j * h i * h j + M i j * h i * h j) +
          (M i j * t i * t j + M i j * t i * t j) +
          (M i j * h i * t j + M i j * t i * h j) := by ring
      _ = M i j * h i * t j + M i j * t i * h j := by rw [h1, h2]; ring
  have hcomb : (∑ i, ∑ j, M i j * (h + t) i * (h + t) j) +
      (∑ i, ∑ j, M i j * h i * h j) + (∑ i, ∑ j, M i j * t i * t j) =
      ∑ i, ∑ j, (M i j * h i * t j + M i j * t i * h j) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
  rw [hcomb]
  simp only [Finset.sum_add_distrib]
  have hswap : (∑ i, ∑ j, M i j * t i * h j) = ∑ i, ∑ j, M j i * h i * t j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => by ring

lemma quad_add_eq {ι : Type*} (q : (ι → F2) → F2) (h t : ι → F2) :
    q (h + t) = q h + q t + q 0 + polar q h t := by
  unfold polar
  have h1 : q h + q h = 0 := f2_add_self _
  have h2 : q t + q t = 0 := f2_add_self _
  have h3 : q 0 + q 0 = 0 := f2_add_self _
  calc q (h + t) = q (h + t) + (q h + q h) + (q t + q t) + (q 0 + q 0) := by
        rw [h1, h2, h3]; ring
    _ = q h + q t + q 0 + (q (h + t) + q h + q t + q 0) := by ring

lemma pow_two_eq_sq_even : ∀ N c : ℕ, c ^ 2 = 2 ^ N → Even N := by
  intro N
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    intro c hc
    match N with
    | 0 => exact ⟨0, rfl⟩
    | 1 =>
      have : c ≤ 1 ∨ 2 ≤ c := by omega
      rcases this with h | h
      · have : c ^ 2 ≤ 1 := by nlinarith
        omega
      · have : 4 ≤ c ^ 2 := by nlinarith
        omega
    | N + 2 =>
      have h2dvd : 2 ∣ c ^ 2 := by
        rw [hc, pow_succ, pow_succ]
        exact ⟨2 ^ N * 2, by ring⟩
      have h2c : 2 ∣ c := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2dvd
      obtain ⟨c', rfl⟩ := h2c
      have hc' : c' ^ 2 = 2 ^ N := by
        have h1 : 4 * c' ^ 2 = 4 * 2 ^ N := by
          calc 4 * c' ^ 2 = (2 * c') ^ 2 := by ring
            _ = 2 ^ (N + 2) := hc
            _ = 4 * 2 ^ N := by ring
        omega
      obtain ⟨k, hk⟩ := ih N (by omega) c' hc'
      exact ⟨k + 1, by omega⟩

lemma walsh_quad_structure {m : ℕ} (R : (Fin m → F2) → F2) (hR : IsQuad R) :
    ∃ (H : Finset (Fin m → F2)) (s : ℕ),
      0 ∈ H ∧
      (∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) ∧
      2 * s ≤ m ∧
      H.card = 2 ^ (m - 2 * s) ∧
      ∀ α : Fin m → F2,
        |∑ z : Fin m → F2, chi (R z + dotProduct α z)| =
          (2 : ℤ) ^ s * ∑ h ∈ H, chi (R h + R 0 + dotProduct α h) := by
  classical
  obtain ⟨b, a, M, hReq⟩ := hR
  let L : (Fin m → F2) →ₗ[F2] (Fin m → F2) :=
    { toFun := fun h j => ∑ i, (M i j + M j i) * h i
      map_add' := fun x y => by
        funext j
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }
  have hpol_dot : ∀ h t : Fin m → F2, polar R h t = dotProduct (L h) t := by
    intro h t
    rw [polar_of_quad b a M R hReq h t]
    simp only [dotProduct, L, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
    rw [Finset.sum_comm]
  let K : Submodule F2 (Fin m → F2) := LinearMap.ker L
  let H : Finset (Fin m → F2) := Finset.univ.filter (fun h => h ∈ K)
  have hH_mem : ∀ h, h ∈ H ↔ L h = 0 := by
    intro h
    simp [H, K, LinearMap.mem_ker]
  have h0H : 0 ∈ H := (hH_mem 0).mpr (map_zero L)
  have haddH : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H := by
    intro x hx y hy
    rw [hH_mem] at hx hy ⊢
    rw [map_add, hx, hy, add_zero]
  let d : ℕ := Module.finrank F2 K
  have hd_le : d ≤ m := by
    have h1 : Module.finrank F2 K ≤ Module.finrank F2 (Fin m → F2) := Submodule.finrank_le K
    simpa [Module.finrank_fin_fun] using h1
  have hH_card : H.card = 2 ^ d := by
    have hsub : H.card = Fintype.card K := by
      simpa [H] using (Fintype.card_subtype (fun h : Fin m → F2 => h ∈ K)).symm
    rw [hsub, Module.card_eq_pow_finrank (K := F2) (V := K)]
    have hF2 : Fintype.card F2 = 2 := rfl
    rw [hF2]
  let W : (Fin m → F2) → ℤ := fun α => ∑ z : Fin m → F2, chi (R z + dotProduct α z)
  have hW_sq : ∀ α : Fin m → F2,
      W α ^ 2 = (2 : ℤ) ^ m * ∑ h ∈ H, chi (R h + R 0 + dotProduct α h) := by
    intro α
    have h1 : W α ^ 2 = ∑ z : Fin m → F2, ∑ w : Fin m → F2,
        chi (R z + dotProduct α z + (R w + dotProduct α w)) := by
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => (chi_add _ _).symm
    have h2 : ∀ z : Fin m → F2,
        (∑ w : Fin m → F2, chi (R z + dotProduct α z + (R w + dotProduct α w))) =
        ∑ h : Fin m → F2, chi (R h + R 0 + dotProduct α h) * chi (polar R h z) := by
      intro z
      refine Finset.sum_bij (fun w _ => w + z) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro w₁ _ w₂ _ h12
        have := congrArg (· + z) h12
        simpa [add_assoc, f2_vec_add_self] using this
      · intro h _
        exact ⟨h + z, Finset.mem_univ _, by simp [add_assoc, f2_vec_add_self]⟩
      · intro w _
        rw [← chi_add]
        congr 1
        have hda : dotProduct α (w + z) = dotProduct α w + dotProduct α z := dotProduct_add α w z
        have hpol : polar R (w + z) z = R w + R (w + z) + R z + R 0 := by
          unfold polar
          rw [show (w + z) + z = w by simp [add_assoc, f2_vec_add_self]]
        rw [hpol, hda]
        have hrr : R (w + z) + R (w + z) = 0 := f2_add_self _
        have hr0 : R 0 + R 0 = 0 := f2_add_self _
        calc R z + dotProduct α z + (R w + dotProduct α w)
            = (R (w + z) + R (w + z)) + (R 0 + R 0) +
              (R z + dotProduct α z + (R w + dotProduct α w)) := by rw [hrr, hr0]; ring
          _ = R (w + z) + R 0 + (dotProduct α w + dotProduct α z) +
              (R w + R (w + z) + R z + R 0) := by ring
    rw [h1]
    simp_rw [h2]
    rw [Finset.sum_comm]
    have h3 : ∀ h : Fin m → F2,
        (∑ z : Fin m → F2, chi (R h + R 0 + dotProduct α h) * chi (polar R h z)) =
        if h ∈ H then (2 : ℤ) ^ m * chi (R h + R 0 + dotProduct α h) else 0 := by
      intro h
      rw [← Finset.mul_sum]
      simp_rw [hpol_dot]
      rw [sum_chi_dot]
      by_cases hh : h ∈ H
      · simp only [hh, (hH_mem h).mp hh, ↓reduceIte]; ring
      · simp only [hh, mt (hH_mem h).mpr hh, ↓reduceIte, mul_zero]
    simp_rw [h3]
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have hfilt : Finset.univ.filter (fun h : Fin m → F2 => h ∈ H) = H := by
      ext h; simp
    rw [hfilt]
  have hlin : ∀ α : Fin m → F2, ∀ x ∈ H, ∀ y ∈ H,
      (R (x + y) + R 0 + dotProduct α (x + y)) =
      (R x + R 0 + dotProduct α x) + (R y + R 0 + dotProduct α y) := by
    intro α x hx y _
    have hpxy : polar R x y = 0 := by
      rw [hpol_dot, (hH_mem x).mp hx, zero_dotProduct]
    rw [quad_add_eq R x y, hpxy, dotProduct_add]
    have hr0 : R 0 + R 0 = 0 := f2_add_self _
    calc R x + R y + R 0 + 0 + R 0 + (dotProduct α x + dotProduct α y)
        = (R 0 + R 0) + (R x + R y + (dotProduct α x + dotProduct α y)) := by ring
      _ = (R x + R 0 + dotProduct α x) + (R y + R 0 + dotProduct α y) := by ring
  have hH_sum_val : ∀ α : Fin m → F2,
      (∑ h ∈ H, chi (R h + R 0 + dotProduct α h)) =
      if ∀ h ∈ H, R h + R 0 + dotProduct α h = 0 then (H.card : ℤ) else 0 := fun α =>
    sum_chi_addHom H haddH (fun h => R h + R 0 + dotProduct α h) (hlin α)
  have hparseval : ∑ α : Fin m → F2, W α ^ 2 = (2 : ℤ) ^ (2 * m) := by
    have h1 : ∑ α : Fin m → F2, W α ^ 2 =
        ∑ z : Fin m → F2, ∑ w : Fin m → F2,
          chi (R z + R w) * ∑ α : Fin m → F2, chi (dotProduct (z + w) α) := by
      calc ∑ α : Fin m → F2, W α ^ 2
          = ∑ α : Fin m → F2, ∑ z : Fin m → F2, ∑ w : Fin m → F2,
              chi (R z + R w) * chi (dotProduct (z + w) α) := by
            refine Finset.sum_congr rfl fun α _ => ?_
            rw [sq, Finset.sum_mul]
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun w _ => ?_
            rw [← chi_add, ← chi_add, add_dotProduct, dotProduct_comm z α, dotProduct_comm w α]
            congr 1; ring
        _ = ∑ z : Fin m → F2, ∑ α : Fin m → F2, ∑ w : Fin m → F2,
              chi (R z + R w) * chi (dotProduct (z + w) α) := Finset.sum_comm
        _ = ∑ z : Fin m → F2, ∑ w : Fin m → F2, ∑ α : Fin m → F2,
              chi (R z + R w) * chi (dotProduct (z + w) α) := by
            refine Finset.sum_congr rfl fun z _ => Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
            rw [← Finset.mul_sum]
    rw [h1]
    have h2 : ∀ z : Fin m → F2,
        (∑ w : Fin m → F2, chi (R z + R w) * ∑ α : Fin m → F2, chi (dotProduct (z + w) α)) =
        (2 : ℤ) ^ m := by
      intro z
      have hterm : ∀ w : Fin m → F2,
          chi (R z + R w) * ∑ α : Fin m → F2, chi (dotProduct (z + w) α) =
          if w = z then (2 : ℤ) ^ m else 0 := by
        intro w
        rw [sum_chi_dot]
        by_cases hwz : w = z
        · subst hwz
          simp only [f2_vec_add_self, f2_add_self, chi_zero, one_mul, ↓reduceIte]
        · have hne : z + w ≠ 0 := by
            intro hzw
            apply hwz
            have := congrArg (· + w) hzw
            simpa [add_assoc, f2_vec_add_self] using this.symm
          simp only [hne, hwz, ↓reduceIte, mul_zero]
      simp_rw [hterm]
      simp
    simp_rw [h2]
    simp [← pow_add, two_mul]
  have hex : ∃ α₀ : Fin m → F2, W α₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have hzero : ∑ α : Fin m → F2, W α ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [hall α]; ring
    rw [hzero] at hparseval
    have hpos : (0 : ℤ) < (2 : ℤ) ^ (2 * m) := by positivity
    linarith
  obtain ⟨α₀, hα₀⟩ := hex
  have hsq0 : (W α₀).natAbs ^ 2 = 2 ^ (m + d) := by
    have hsqZ : W α₀ ^ 2 = (2 : ℤ) ^ (m + d) := by
      rw [hW_sq α₀, hH_sum_val α₀]
      split_ifs with hcond
      · rw [hH_card, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
      · exfalso
        apply hα₀
        have : W α₀ ^ 2 = 0 := by
          rw [hW_sq α₀, hH_sum_val α₀]
          split_ifs <;> first | contradiction | ring
        exact sq_eq_zero_iff.mp this
    have hcast : ((W α₀).natAbs ^ 2 : ℤ) = ((2 ^ (m + d) : ℕ) : ℤ) := by
      rw [Nat.cast_pow, Int.natAbs_sq, hsqZ]
      norm_cast
    exact Int.ofNat.inj hcast
  have heven : Even (m + d) := pow_two_eq_sq_even (m + d) (W α₀).natAbs hsq0
  obtain ⟨t, ht⟩ := heven
  let s : ℕ := (m - d) / 2
  have hsle : 2 * s ≤ m := by omega
  have hd_eq : d = m - 2 * s := by omega
  refine ⟨H, s, h0H, haddH, hsle, by rw [hH_card, hd_eq], ?_⟩
  intro α
  rw [hH_sum_val α]
  change |W α| = _
  split_ifs with hcond
  · rw [hH_card, hd_eq]
    have hsqZ : W α ^ 2 = ((2 : ℤ) ^ (m - s)) ^ 2 := by
      rw [hW_sq α, hH_sum_val α]
      split_ifs <;> first
      | contradiction
      | rw [hH_card, hd_eq, Nat.cast_pow, Nat.cast_ofNat, ← pow_add, ← pow_mul]
        congr 1; omega
    have habs : |W α| = (2 : ℤ) ^ (m - s) := by
      have h1 : |W α| ^ 2 = ((2 : ℤ) ^ (m - s)) ^ 2 := by rw [sq_abs, hsqZ]
      have h2 := sq_eq_sq₀ (abs_nonneg (W α)) (by positivity : (0 : ℤ) ≤ (2 : ℤ) ^ (m - s))
      exact h2.mp h1
    rw [habs, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
    congr 1; omega
  · rw [mul_zero]
    have hsqZ : W α ^ 2 = 0 := by
      rw [hW_sq α, hH_sum_val α]
      split_ifs <;> first | contradiction | ring
    rw [sq_eq_zero_iff.mp hsqZ, abs_zero]

def wt {m : ℕ} (h : Fin m → F2) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => h i = 1)).card

lemma wt_le {m : ℕ} (h : Fin m → F2) : wt h ≤ m := by
  unfold wt
  calc (Finset.univ.filter (fun i : Fin m => h i = 1)).card
      ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := Finset.card_fin m

lemma wt_cons {m : ℕ} (b : F2) (u : Fin m → F2) :
    wt (consF2 b u) = (if b = 1 then 1 else 0) + wt u := by
  unfold wt
  have hsplit : Finset.univ.filter (fun i : Fin (m + 1) => consF2 b u i = 1) =
      (if b = 1 then ({0} : Finset (Fin (m + 1))) else ∅) ∪
      (Finset.univ.filter (fun j : Fin m => u j = 1)).map (Fin.succEmb m) := by
    ext i
    cases i using Fin.cases with
    | zero =>
      rcases f2_cases b with rfl | rfl <;> simp [Fin.succEmb, consF2_zero]
    | succ j =>
      rcases f2_cases b with rfl | rfl <;> simp [Fin.succEmb, consF2_succ]
  rw [hsplit, Finset.card_union_of_disjoint, Finset.card_map]
  · rcases f2_cases b with rfl | rfl <;> simp
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx2
    obtain ⟨j, _, rfl⟩ := hx2
    rcases f2_cases b with rfl | rfl
    · simp at hx1
    · simp only [↓reduceIte, Finset.mem_singleton] at hx1
      exact Fin.succ_ne_zero j hx1

lemma pow_two_wt_fourier {m : ℕ} (u : Fin m → F2) :
    (2 : ℤ) ^ m * (2 : ℤ) ^ (m - wt u) =
      ∑ S : Finset (Fin m), (3 : ℤ) ^ (Finset.univ \ S).card * chi (∑ i ∈ S, u i) := by
  have hprod : (2 : ℤ) ^ m * (2 : ℤ) ^ (m - wt u) = ∏ i : Fin m, (chi (u i) + 3) := by
    have hfactor : ∀ i : Fin m, chi (u i) + 3 = (2 : ℤ) * (if u i = 1 then 1 else 2) := by
      intro i
      rcases f2_cases (u i) with h | h <;> rw [h] <;> decide
    simp_rw [hfactor, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
    congr 1
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    have hcompl : (Finset.univ.filter (fun i : Fin m => u i = 1)).card +
        (Finset.univ.filter (fun i : Fin m => ¬ u i = 1)).card = m := by
      simpa [Finset.card_fin] using card_filter_add_not (Finset.univ : Finset (Fin m)) (fun i => u i = 1)
    unfold wt
    omega
  rw [hprod, Finset.prod_add]
  have hpow : (Finset.univ : Finset (Fin m)).powerset = Finset.univ := by
    ext S; simp
  rw [hpow]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_const, ← chi_sum, mul_comm]

lemma coset_wt_le {m : ℕ} (H : Finset (Fin m → F2))
    (hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) (u0 : Fin m → F2) :
    ∑ u ∈ H, (2 : ℤ) ^ (m - wt (u + u0)) ≤ ∑ u ∈ H, (2 : ℤ) ^ (m - wt u) := by
  suffices h : (2 : ℤ) ^ m * ∑ u ∈ H, (2 : ℤ) ^ (m - wt (u + u0)) ≤
      (2 : ℤ) ^ m * ∑ u ∈ H, (2 : ℤ) ^ (m - wt u) from
    le_of_mul_le_mul_left h (by positivity)
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [pow_two_wt_fourier]
  rw [Finset.sum_comm, Finset.sum_comm (s := H)]
  refine Finset.sum_le_sum fun S _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hshift : ∑ u ∈ H, chi (∑ i ∈ S, (u + u0) i) =
      chi (∑ i ∈ S, u0 i) * ∑ u ∈ H, chi (∑ i ∈ S, u i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Pi.add_apply, Finset.sum_add_distrib, chi_add]
    ring
  rw [hshift]
  have hnonneg : 0 ≤ ∑ u ∈ H, chi (∑ i ∈ S, u i) := by
    rw [sum_chi_addHom H hadd (fun u => ∑ i ∈ S, u i)
      (fun x _ y _ => by simp only [Pi.add_apply, Finset.sum_add_distrib])]
    split_ifs <;> positivity
  calc chi (∑ i ∈ S, u0 i) * ∑ u ∈ H, chi (∑ i ∈ S, u i)
      ≤ 1 * ∑ u ∈ H, chi (∑ i ∈ S, u i) :=
        mul_le_mul_of_nonneg_right (chi_le_one _) hnonneg
    _ = ∑ u ∈ H, chi (∑ i ∈ S, u i) := one_mul _

lemma subgroup_wt_bound : ∀ (m : ℕ) (H : Finset (Fin m → F2)) (d : ℕ),
    0 ∈ H → (∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) → H.card = 2 ^ d →
    ∑ h ∈ H, (2 : ℤ) ^ (m - wt h) ≤ (2 : ℤ) ^ (m - d) * (3 : ℤ) ^ d := by
  intro m
  induction m with
  | zero =>
    intro H d h0 _ hcard
    have hH : H = {0} := by
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro _; exact Subsingleton.elim x 0
      · rintro rfl; exact h0
    have hd : d = 0 := by
      have : 2 ^ d = 1 := by rw [← hcard, hH]; simp
      rcases d with _ | d
      · rfl
      · have : 2 ≤ 2 ^ (d + 1) := Nat.le_self_pow (Nat.succ_ne_zero d) 2
        omega
    subst hd
    rw [hH]
    simp [wt]
  | succ m ih =>
    intro H d h0 hadd hcard
    classical
    let emb0 : (Fin m → F2) ↪ (Fin (m + 1) → F2) := ⟨consF2 0, consF2_inj 0⟩
    let emb1 : (Fin m → F2) ↪ (Fin (m + 1) → F2) := ⟨consF2 1, consF2_inj 1⟩
    let H0 : Finset (Fin m → F2) := Finset.univ.filter (fun u => consF2 0 u ∈ H)
    let H1 : Finset (Fin m → F2) := Finset.univ.filter (fun u => consF2 1 u ∈ H)
    have hsplit : H = H0.map emb0 ∪ H1.map emb1 := by
      ext h
      simp only [Finset.mem_union, Finset.mem_map, emb0, emb1, Function.Embedding.coeFn_mk,
        H0, H1, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hh
        have heq : consF2 (h 0) (Fin.tail h) = h := consF2_self_tail h
        rcases f2_cases (h 0) with h0v | h0v
        · left; refine ⟨Fin.tail h, ?_, ?_⟩
          · rw [← h0v, heq]; exact hh
          · rw [← h0v, heq]
        · right; refine ⟨Fin.tail h, ?_, ?_⟩
          · rw [← h0v, heq]; exact hh
          · rw [← h0v, heq]
      · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) <;> exact hu
    have hdisj : Disjoint (H0.map emb0) (H1.map emb1) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_map, emb0, emb1, Function.Embedding.coeFn_mk] at hx1 hx2
      obtain ⟨u, _, rfl⟩ := hx1
      obtain ⟨v, _, hv⟩ := hx2
      have := congrFun hv 0
      simp [consF2_zero] at this
    have h0_H0 : 0 ∈ H0 := by
      simp only [H0, Finset.mem_filter, Finset.mem_univ, true_and]
      convert h0 using 1
      ext i
      cases i using Fin.cases with
      | zero => rfl
      | succ j => rfl
    have hadd_H0 : ∀ x ∈ H0, ∀ y ∈ H0, x + y ∈ H0 := by
      intro x hx y hy
      simp only [H0, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
      have hxy := hadd _ hx _ hy
      convert hxy using 1
      ext i
      cases i using Fin.cases with
      | zero => simp [consF2_zero]
      | succ j => simp [consF2_succ]
    have hsum_split : ∑ h ∈ H, (2 : ℤ) ^ (m + 1 - wt h) =
        2 * (∑ u ∈ H0, (2 : ℤ) ^ (m - wt u)) + ∑ u ∈ H1, (2 : ℤ) ^ (m - wt u) := by
      rw [hsplit, Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun u _ => ?_
        change (2 : ℤ) ^ (m + 1 - wt (consF2 0 u)) = 2 * (2 : ℤ) ^ (m - wt u)
        rw [wt_cons]
        have hle := wt_le u
        have hne : (0 : F2) ≠ 1 := by decide
        simp only [hne, ↓reduceIte, zero_add]
        rw [show m + 1 - wt u = (m - wt u) + 1 by omega, pow_succ']
      · refine Finset.sum_congr rfl fun u _ => ?_
        change (2 : ℤ) ^ (m + 1 - wt (consF2 1 u)) = (2 : ℤ) ^ (m - wt u)
        rw [wt_cons]
        simp only [↓reduceIte]
        congr 1; omega
    have hcard_split : H.card = H0.card + H1.card := by
      rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]
    by_cases hH1 : H1.Nonempty
    · obtain ⟨u0, hu0⟩ := hH1
      have hu0H : consF2 1 u0 ∈ H := (Finset.mem_filter.mp hu0).2
      have hH1_eq : H1 = H0.image (· + u0) := by
        ext v
        simp only [H1, H0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hv
          refine ⟨v + u0, ?_, by simp [add_assoc, f2_vec_add_self]⟩
          have hsum := hadd _ hv _ hu0H
          convert hsum using 1
          ext i
          cases i using Fin.cases with
          | zero => simp [consF2_zero, f2_add_self]
          | succ j => simp [consF2_succ]
        · rintro ⟨u, hu, rfl⟩
          have hsum := hadd _ hu _ hu0H
          convert hsum using 1
          ext i
          cases i using Fin.cases with
          | zero => simp [consF2_zero]
          | succ j => simp [consF2_succ]
      have hcard1 : H1.card = H0.card := by
        rw [hH1_eq, Finset.card_image_of_injective]
        intro x y hxy
        have := congrArg (· + u0) hxy
        simpa [add_assoc, f2_vec_add_self] using this
      have hH0_pos : 0 < H0.card := Finset.card_pos.mpr ⟨0, h0_H0⟩
      have hd_pos : 0 < d := by
        rcases d with _ | d
        · omega
        · omega
      have hcard0 : H0.card = 2 ^ (d - 1) := by
        have : 2 * H0.card = 2 * 2 ^ (d - 1) := by
          calc 2 * H0.card = H.card := by omega
            _ = 2 ^ d := hcard
            _ = 2 * 2 ^ (d - 1) := by
              conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ']
        omega
      have hd_le_m1 : d ≤ m + 1 := by
        have h1 : H.card ≤ Fintype.card (Fin (m + 1) → F2) := Finset.card_le_univ H
        rw [hcard, Fintype.card_fun, Fintype.card_fin] at h1
        have hF2 : Fintype.card F2 = 2 := rfl
        rw [hF2] at h1
        exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp h1
      have hih := ih H0 (d - 1) h0_H0 hadd_H0 hcard0
      have hcoset : ∑ u ∈ H1, (2 : ℤ) ^ (m - wt u) ≤ ∑ u ∈ H0, (2 : ℤ) ^ (m - wt u) := by
        rw [hH1_eq, Finset.sum_image]
        · exact coset_wt_le H0 hadd_H0 u0
        · intro x _ y _ hxy
          have := congrArg (· + u0) hxy
          simpa [add_assoc, f2_vec_add_self] using this
      rw [hsum_split]
      calc 2 * ∑ u ∈ H0, (2 : ℤ) ^ (m - wt u) + ∑ u ∈ H1, (2 : ℤ) ^ (m - wt u)
          ≤ 3 * ∑ u ∈ H0, (2 : ℤ) ^ (m - wt u) := by linarith
        _ ≤ 3 * ((2 : ℤ) ^ (m - (d - 1)) * (3 : ℤ) ^ (d - 1)) := by linarith
        _ = (2 : ℤ) ^ (m + 1 - d) * (3 : ℤ) ^ d := by
          rw [show m - (d - 1) = m + 1 - d by omega]
          conv_rhs => rhs; rw [show d = (d - 1) + 1 by omega, pow_succ']
          ring
    · rw [Finset.not_nonempty_iff_eq_empty] at hH1
      have hcard0 : H0.card = 2 ^ d := by
        rw [hH1, Finset.card_empty, add_zero] at hcard_split
        omega
      have hd_le_m : d ≤ m := by
        have h1 : H0.card ≤ Fintype.card (Fin m → F2) := Finset.card_le_univ H0
        rw [hcard0, Fintype.card_fun, Fintype.card_fin] at h1
        have hF2 : Fintype.card F2 = 2 := rfl
        rw [hF2] at h1
        exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp h1
      have hih := ih H0 d h0_H0 hadd_H0 hcard0
      rw [hsum_split, hH1, Finset.sum_empty, add_zero]
      calc 2 * ∑ u ∈ H0, (2 : ℤ) ^ (m - wt u)
          ≤ 2 * ((2 : ℤ) ^ (m - d) * (3 : ℤ) ^ d) := by linarith
        _ = (2 : ℤ) ^ (m + 1 - d) * (3 : ℤ) ^ d := by
          rw [show m + 1 - d = (m - d) + 1 by omega, pow_succ']
          ring

lemma prod_le_prod_nonneg {α : Type*} (s : Finset α) (f g : α → ℤ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (hle : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa0 : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
    have hfal : f a ≤ g a := hle a (Finset.mem_insert_self a s)
    have hga0 : 0 ≤ g a := hfa0.trans hfal
    have hs0 : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have hsle : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
      ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
         (fun i hi => hle i (Finset.mem_insert_of_mem hi))
    exact mul_le_mul hfal hsle hs0 hga0

lemma two_bit_bound (c d1 d2 : F2) :
    |∑ p : F2 × F2, chi (c * p.1 * p.2 + d1 * p.1 + d2 * p.2)| ≤
      if c = 0 then 4 else 2 := by
  fin_cases c <;> fin_cases d1 <;> fin_cases d2 <;> decide

lemma sum_uv_factor {m : ℕ} (h d1 d2 : Fin m → F2) :
    (∑ u : Fin m → F2, ∑ v : Fin m → F2,
      chi (∑ j : Fin m, (h j * u j * v j + d1 j * u j + d2 j * v j))) =
    ∏ j : Fin m, ∑ p : F2 × F2, chi (h j * p.1 * p.2 + d1 j * p.1 + d2 j * p.2) := by
  let F : Fin m → F2 × F2 → ℤ := fun j p => chi (h j * p.1 * p.2 + d1 j * p.1 + d2 j * p.2)
  have hps : (∏ j : Fin m, ∑ p : F2 × F2, F j p) = ∑ f : Fin m → F2 × F2, ∏ j : Fin m, F j (f j) :=
    Fintype.prod_sum F
  rw [hps]
  let ePair : ((Fin m → F2) × (Fin m → F2)) ≃ (Fin m → F2 × F2) :=
    { toFun := fun p j => (p.1 j, p.2 j)
      invFun := fun f => (fun j => (f j).1, fun j => (f j).2)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.sum_prod_type', ← ePair.sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [chi_sum]
  rfl

def pack {m : ℕ} (z u v : Fin m → F2) (p : Fin m × Fin 3) : F2 :=
  match p.2 with
  | ⟨0, _⟩ => z p.1
  | ⟨1, _⟩ => u p.1
  | ⟨2, _⟩ => v p.1

def packEquiv (m : ℕ) :
    ((Fin m → F2) × (Fin m → F2) × (Fin m → F2)) ≃ ((Fin m × Fin 3) → F2) where
  toFun := fun x => pack x.1 x.2.1 x.2.2
  invFun := fun w => (fun i => w (i, 0), fun i => w (i, 1), fun i => w (i, 2))
  left_inv := by
    rintro ⟨z, u, v⟩
    ext i <;> rfl
  right_inv := by
    intro w
    funext ⟨i, j⟩
    fin_cases j <;> rfl

lemma pack_add_split {m : ℕ} (z u v : Fin m → F2) :
    pack z u v = pack z 0 0 + pack 0 u v := by
  funext ⟨i, j⟩
  fin_cases j <;> simp [pack]

theorem disjoint_triples_core (m : ℕ) (q : ((Fin m × Fin 3) → F2) → F2) (hq : IsQuad q) :
    |∑ w : (Fin m × Fin 3) → F2,
      chi (q w + ∑ i : Fin m, w (i, 0) * w (i, 1) * w (i, 2))| ≤ (6 : ℤ) ^ m := by
  classical
  obtain ⟨b, a, M, hqeq⟩ := hq
  let R : (Fin m → F2) → F2 := fun z => q (pack z 0 0)
  have hR_quad : IsQuad R := by
    refine ⟨b, fun i => a (i, 0), fun i j => M (i, 0) (j, 0), fun z => ?_⟩
    dsimp only [R]
    rw [hqeq (pack z 0 0)]
    have h1 : dotProduct a (pack z 0 0) = dotProduct (fun i => a (i, 0)) z := by
      simp only [dotProduct, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.sum_univ_three]
      simp [pack]
    have h2 : (∑ p : Fin m × Fin 3, ∑ p' : Fin m × Fin 3,
        M p p' * pack z 0 0 p * pack z 0 0 p') =
        ∑ i : Fin m, ∑ j : Fin m, M (i, 0) (j, 0) * z i * z j := by
      simp only [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.sum_univ_three]
      simp only [pack, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.sum_univ_three]
      simp
    rw [h1, h2]
  let C : (Fin m → F2) → (Fin m → F2) → F2 := fun u v => q (pack 0 u v) + q 0
  let A1 : Fin m → Fin m → F2 := fun i j => M (i, 0) (j, 1) + M (j, 1) (i, 0)
  let A2 : Fin m → Fin m → F2 := fun i j => M (i, 0) (j, 2) + M (j, 2) (i, 0)
  let alpha : (Fin m → F2) → (Fin m → F2) → (Fin m → F2) := fun u v i =>
    u i * v i + (∑ j, A1 i j * u j) + (∑ j, A2 i j * v j)
  have hpol_split : ∀ z u v : Fin m → F2,
      polar q (pack z 0 0) (pack 0 u v) =
        ∑ i : Fin m, ((∑ j, A1 i j * u j) + (∑ j, A2 i j * v j)) * z i := by
    intro z u v
    rw [polar_of_quad b a M q hqeq]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_three]
    simp only [pack, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rw [add_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.sum_univ_three]
    simp only [mul_zero, zero_add, A1, A2]
    ring
  have hdecomp : ∀ z u v : Fin m → F2,
      q (pack z u v) + (∑ i : Fin m, z i * u i * v i) =
        C u v + (R z + dotProduct (alpha u v) z) := by
    intro z u v
    rw [pack_add_split, quad_add_eq q (pack z 0 0) (pack 0 u v), hpol_split]
    have hdot : dotProduct (alpha u v) z =
        (∑ i : Fin m, z i * u i * v i) +
        ∑ i : Fin m, ((∑ j, A1 i j * u j) + (∑ j, A2 i j * v j)) * z i := by
      simp only [dotProduct, alpha, add_mul, Finset.sum_add_distrib]
      rw [add_assoc]
      congr 1
      refine Finset.sum_congr rfl fun i _ => by ring
    dsimp only [R, C]
    rw [hdot]
    ring
  obtain ⟨H, s, h0H, haddH, hsle, hHcard, hWalsh⟩ := walsh_quad_structure R hR_quad
  have hsum_eq : (∑ w : (Fin m × Fin 3) → F2,
      chi (q w + ∑ i : Fin m, w (i, 0) * w (i, 1) * w (i, 2))) =
      ∑ u : Fin m → F2, ∑ v : Fin m → F2,
        chi (C u v) * ∑ z : Fin m → F2, chi (R z + dotProduct (alpha u v) z) := by
    rw [← (packEquiv m).sum_comp]
    simp only [packEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← chi_add, ← hdecomp z u v]
    congr 1
  have hstep1 : |∑ w : (Fin m × Fin 3) → F2,
      chi (q w + ∑ i : Fin m, w (i, 0) * w (i, 1) * w (i, 2))| ≤
      ∑ u : Fin m → F2, ∑ v : Fin m → F2,
        |∑ z : Fin m → F2, chi (R z + dotProduct (alpha u v) z)| := by
    rw [hsum_eq]
    calc |∑ u : Fin m → F2, ∑ v : Fin m → F2,
            chi (C u v) * ∑ z : Fin m → F2, chi (R z + dotProduct (alpha u v) z)|
        ≤ ∑ u : Fin m → F2, |∑ v : Fin m → F2,
            chi (C u v) * ∑ z : Fin m → F2, chi (R z + dotProduct (alpha u v) z)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u : Fin m → F2, ∑ v : Fin m → F2,
            |chi (C u v) * ∑ z : Fin m → F2, chi (R z + dotProduct (alpha u v) z)| :=
          Finset.sum_le_sum fun u _ => Finset.abs_sum_le_sum_abs _ _
      _ = ∑ u : Fin m → F2, ∑ v : Fin m → F2,
            |∑ z : Fin m → F2, chi (R z + dotProduct (alpha u v) z)| := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
          rw [abs_mul, chi_abs, one_mul]
  have hstep2 : (∑ u : Fin m → F2, ∑ v : Fin m → F2,
      |∑ z : Fin m → F2, chi (R z + dotProduct (alpha u v) z)|) =
      (2 : ℤ) ^ s * ∑ h ∈ H, chi (R h + R 0) *
        ∑ u : Fin m → F2, ∑ v : Fin m → F2, chi (dotProduct (alpha u v) h) := by
    simp_rw [hWalsh]
    simp_rw [← Finset.mul_sum]
    congr 1
    calc ∑ u : Fin m → F2, ∑ v : Fin m → F2, ∑ h ∈ H, chi (R h + R 0 + dotProduct (alpha u v) h)
        = ∑ u : Fin m → F2, ∑ h ∈ H, ∑ v : Fin m → F2,
            chi (R h + R 0 + dotProduct (alpha u v) h) :=
          Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ h ∈ H, ∑ u : Fin m → F2, ∑ v : Fin m → F2,
            chi (R h + R 0 + dotProduct (alpha u v) h) := Finset.sum_comm
      _ = ∑ h ∈ H, chi (R h + R 0) *
            ∑ u : Fin m → F2, ∑ v : Fin m → F2, chi (dotProduct (alpha u v) h) := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => chi_add _ _
  have hfactor : ∀ h : Fin m → F2,
      |∑ u : Fin m → F2, ∑ v : Fin m → F2, chi (dotProduct (alpha u v) h)| ≤
        (2 : ℤ) ^ m * (2 : ℤ) ^ (m - wt h) := by
    intro h
    let d1 : Fin m → F2 := fun j => ∑ i, A1 i j * h i
    let d2 : Fin m → F2 := fun j => ∑ i, A2 i j * h i
    have hdot_uv : ∀ u v : Fin m → F2,
        dotProduct (alpha u v) h =
          ∑ j : Fin m, (h j * u j * v j + d1 j * u j + d2 j * v j) := by
      intro u v
      simp only [dotProduct, alpha, add_mul, Finset.sum_add_distrib]
      have h1 : (∑ i : Fin m, (∑ j : Fin m, A1 i j * u j) * h i) = ∑ j : Fin m, d1 j * u j := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp only [d1]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => by ring
      have h2 : (∑ i : Fin m, (∑ j : Fin m, A2 i j * v j) * h i) = ∑ j : Fin m, d2 j * v j := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp only [d2]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [h1, h2]
      congr 1
      congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
    have hprod_eq : (∑ u : Fin m → F2, ∑ v : Fin m → F2, chi (dotProduct (alpha u v) h)) =
        ∏ j : Fin m, ∑ p : F2 × F2, chi (h j * p.1 * p.2 + d1 j * p.1 + d2 j * p.2) := by
      simp_rw [hdot_uv]
      exact sum_uv_factor h d1 d2
    rw [hprod_eq, Finset.abs_prod]
    calc ∏ j : Fin m, |∑ p : F2 × F2, chi (h j * p.1 * p.2 + d1 j * p.1 + d2 j * p.2)|
        ≤ ∏ j : Fin m, (if h j = 0 then (4 : ℤ) else 2) :=
          prod_le_prod_nonneg Finset.univ _ _ (fun j _ => abs_nonneg _)
            (fun j _ => two_bit_bound (h j) (d1 j) (d2 j))
      _ = (2 : ℤ) ^ m * (2 : ℤ) ^ (m - wt h) := by
          have hite : ∀ j : Fin m,
              (if h j = 0 then (4 : ℤ) else 2) = (2 : ℤ) * (if h j = 1 then 1 else 2) := by
            intro j
            rcases f2_cases (h j) with hj | hj <;> rw [hj] <;> decide
          simp_rw [hite, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
          congr 1
          rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
          congr 1
          have hcompl : (Finset.univ.filter (fun j : Fin m => h j = 1)).card +
              (Finset.univ.filter (fun j : Fin m => ¬ h j = 1)).card = m := by
            simpa [Finset.card_fin] using
              card_filter_add_not (Finset.univ : Finset (Fin m)) (fun j => h j = 1)
          unfold wt
          omega
  have hwt := subgroup_wt_bound m H (m - 2 * s) h0H haddH hHcard
  have hbound : |∑ w : (Fin m × Fin 3) → F2,
      chi (q w + ∑ i : Fin m, w (i, 0) * w (i, 1) * w (i, 2))| ≤
      (2 : ℤ) ^ s * ((2 : ℤ) ^ m * ((2 : ℤ) ^ (2 * s) * (3 : ℤ) ^ (m - 2 * s))) := by
    have h3 : (∑ h ∈ H, chi (R h + R 0) *
        ∑ u : Fin m → F2, ∑ v : Fin m → F2, chi (dotProduct (alpha u v) h)) ≤
        (2 : ℤ) ^ m * ∑ h ∈ H, (2 : ℤ) ^ (m - wt h) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun h _ => ?_
      calc chi (R h + R 0) * ∑ u : Fin m → F2, ∑ v : Fin m → F2, chi (dotProduct (alpha u v) h)
          ≤ |chi (R h + R 0) * ∑ u : Fin m → F2, ∑ v : Fin m → F2, chi (dotProduct (alpha u v) h)| :=
            le_abs_self _
        _ = |∑ u : Fin m → F2, ∑ v : Fin m → F2, chi (dotProduct (alpha u v) h)| := by
            rw [abs_mul, chi_abs, one_mul]
        _ ≤ (2 : ℤ) ^ m * (2 : ℤ) ^ (m - wt h) := hfactor h
    have h4 : (2 : ℤ) ^ m * ∑ h ∈ H, (2 : ℤ) ^ (m - wt h) ≤
        (2 : ℤ) ^ m * ((2 : ℤ) ^ (2 * s) * (3 : ℤ) ^ (m - 2 * s)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      simpa [show m - (m - 2 * s) = 2 * s by omega] using hwt
    calc |∑ w : (Fin m × Fin 3) → F2,
            chi (q w + ∑ i : Fin m, w (i, 0) * w (i, 1) * w (i, 2))|
        ≤ (2 : ℤ) ^ s * ∑ h ∈ H, chi (R h + R 0) *
            ∑ u : Fin m → F2, ∑ v : Fin m → F2, chi (dotProduct (alpha u v) h) := by
          rw [← hstep2]; exact hstep1
      _ ≤ (2 : ℤ) ^ s * ((2 : ℤ) ^ m * ((2 : ℤ) ^ (2 * s) * (3 : ℤ) ^ (m - 2 * s))) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
  have hfinal : (2 : ℤ) ^ s * ((2 : ℤ) ^ m * ((2 : ℤ) ^ (2 * s) * (3 : ℤ) ^ (m - 2 * s))) ≤
      (6 : ℤ) ^ m := by
    suffices h : (3 : ℤ) ^ (2 * s) *
        ((2 : ℤ) ^ s * ((2 : ℤ) ^ m * ((2 : ℤ) ^ (2 * s) * (3 : ℤ) ^ (m - 2 * s)))) ≤
        (3 : ℤ) ^ (2 * s) * (6 : ℤ) ^ m from
      le_of_mul_le_mul_left h (by positivity)
    have hlhs : (3 : ℤ) ^ (2 * s) *
        ((2 : ℤ) ^ s * ((2 : ℤ) ^ m * ((2 : ℤ) ^ (2 * s) * (3 : ℤ) ^ (m - 2 * s)))) =
        (8 : ℤ) ^ s * (6 : ℤ) ^ m := by
      calc (3 : ℤ) ^ (2 * s) *
            ((2 : ℤ) ^ s * ((2 : ℤ) ^ m * ((2 : ℤ) ^ (2 * s) * (3 : ℤ) ^ (m - 2 * s))))
          = ((2 : ℤ) ^ s * (2 : ℤ) ^ (2 * s)) *
            ((2 : ℤ) ^ m * ((3 : ℤ) ^ (2 * s) * (3 : ℤ) ^ (m - 2 * s))) := by ring
        _ = (2 : ℤ) ^ (3 * s) * ((2 : ℤ) ^ m * (3 : ℤ) ^ m) := by
            rw [← pow_add, ← pow_add, show s + 2 * s = 3 * s by omega,
              show 2 * s + (m - 2 * s) = m by omega]
        _ = ((2 : ℤ) ^ 3) ^ s * ((2 : ℤ) * 3) ^ m := by
            rw [mul_pow, ← pow_mul]
        _ = (8 : ℤ) ^ s * (6 : ℤ) ^ m := by norm_num
    have hrhs : (3 : ℤ) ^ (2 * s) * (6 : ℤ) ^ m = (9 : ℤ) ^ s * (6 : ℤ) ^ m := by
      rw [pow_mul]; norm_num
    rw [hlhs, hrhs]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast Nat.pow_le_pow_left (by omega : 8 ≤ 9) s
  exact hbound.trans hfinal

lemma quad_restrict_emb {m n : ℕ} (pos : (Fin m × Fin 3) ↪ Fin n)
    (q : (Fin n → F2) → F2) (hq : IsQuad q)
    (r : {t : Fin n // t ∉ Set.range pos} → F2) :
    IsQuad (fun w : (Fin m × Fin 3) → F2 =>
      q (fun t => if h : ∃ p, pos p = t then w (Classical.choose h) else r ⟨t, h⟩)) := by
  classical
  obtain ⟨b, a, M, hqeq⟩ := hq
  let embVal : ((Fin m × Fin 3) → F2) → Fin n → F2 := fun w t =>
    if h : ∃ p, pos p = t then w (Classical.choose h) else r ⟨t, h⟩
  have hemb_pos : ∀ w p, embVal w (pos p) = w p := by
    intro w p
    dsimp only [embVal]
    have hex : ∃ p', pos p' = pos p := ⟨p, rfl⟩
    simp only [hex, ↓reduceDIte]
    congr 1
    exact pos.injective (Classical.choose_spec hex)
  let S : Finset (Fin n) := Finset.univ.image pos
  let Sc : Finset (Fin n) := Finset.univ \ S
  have hmemS : ∀ t, t ∈ S ↔ ∃ p, pos p = t := by
    intro t; simp [S]
  have hemb_out : ∀ w t (ht : t ∈ Sc), embVal w t = r ⟨t, by
      intro hex; exact (Finset.mem_sdiff.mp ht).2 ((hmemS t).mpr hex)⟩ := by
    intro w t ht
    dsimp only [embVal]
    have hno : ¬ ∃ p, pos p = t := fun hex => (Finset.mem_sdiff.mp ht).2 ((hmemS t).mpr hex)
    simp only [hno, ↓reduceDIte]
  let cVal : Fin n → F2 := fun t => if h : t ∈ Sc then embVal 0 t else 0
  have hemb_out_const : ∀ w t, t ∈ Sc → embVal w t = cVal t := by
    intro w t ht
    simp only [cVal, ht, ↓reduceDIte, hemb_out w t ht, hemb_out 0 t ht]
  let b' : F2 := b + (∑ t ∈ Sc, a t * cVal t) + ∑ t ∈ Sc, ∑ u ∈ Sc, M t u * cVal t * cVal u
  let a' : (Fin m × Fin 3) → F2 := fun p =>
    a (pos p) + (∑ u ∈ Sc, M (pos p) u * cVal u) + (∑ t ∈ Sc, M t (pos p) * cVal t)
  let M' : (Fin m × Fin 3) → (Fin m × Fin 3) → F2 := fun p p' => M (pos p) (pos p')
  refine ⟨b', a', M', fun w => ?_⟩
  change q (embVal w) = b' + dotProduct a' w + ∑ p, ∑ p', M' p p' * w p * w p'
  rw [hqeq (embVal w)]
  have hpart : ∀ f : Fin n → F2, ∑ t : Fin n, f t = (∑ p : Fin m × Fin 3, f (pos p)) + ∑ t ∈ Sc, f t := by
    intro f
    have hdisj : Disjoint S Sc := disjoint_sdiff_self_right
    have hunion : S ∪ Sc = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ S)
    rw [← hunion, Finset.sum_union hdisj, Finset.sum_image (fun p1 _ p2 _ h => pos.injective h)]
  have hlin : dotProduct a (embVal w) =
      (∑ p : Fin m × Fin 3, a (pos p) * w p) + ∑ t ∈ Sc, a t * cVal t := by
    dsimp only [dotProduct]
    rw [hpart]
    congr 1
    · refine Finset.sum_congr rfl fun p _ => by rw [hemb_pos]
    · refine Finset.sum_congr rfl fun t ht => by rw [hemb_out_const w t ht]
  have hquad : (∑ t : Fin n, ∑ u : Fin n, M t u * embVal w t * embVal w u) =
      (∑ p, ∑ p', M (pos p) (pos p') * w p * w p') +
      (∑ p, (∑ u ∈ Sc, M (pos p) u * cVal u) * w p) +
      (∑ p', (∑ t ∈ Sc, M t (pos p') * cVal t) * w p') +
      (∑ t ∈ Sc, ∑ u ∈ Sc, M t u * cVal t * cVal u) := by
    rw [hpart]
    have hleft_pt : ∀ p : Fin m × Fin 3,
        (∑ u : Fin n, M (pos p) u * embVal w (pos p) * embVal w u) =
        (∑ p' : Fin m × Fin 3, M (pos p) (pos p') * w p * w p') +
        (∑ u ∈ Sc, M (pos p) u * cVal u) * w p := by
      intro p
      rw [hpart]
      refine congrArg₂ (· + ·) ?_ ?_
      · refine Finset.sum_congr rfl fun p' _ => by rw [hemb_pos, hemb_pos]
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun u hu => by rw [hemb_pos, hemb_out_const w u hu]; ring
    have hleft : (∑ p : Fin m × Fin 3, ∑ u : Fin n, M (pos p) u * embVal w (pos p) * embVal w u) =
        (∑ p, ∑ p', M (pos p) (pos p') * w p * w p') +
        (∑ p, (∑ u ∈ Sc, M (pos p) u * cVal u) * w p) := by
      rw [Finset.sum_congr rfl fun p _ => hleft_pt p, Finset.sum_add_distrib]
    have hright : (∑ t ∈ Sc, ∑ u : Fin n, M t u * embVal w t * embVal w u) =
        (∑ p', (∑ t ∈ Sc, M t (pos p') * cVal t) * w p') +
        (∑ t ∈ Sc, ∑ u ∈ Sc, M t u * cVal t * cVal u) := by
      have hsplit : ∀ t ∈ Sc, (∑ u : Fin n, M t u * embVal w t * embVal w u) =
          (∑ p' : Fin m × Fin 3, M t (pos p') * cVal t * w p') +
          (∑ u ∈ Sc, M t u * cVal t * cVal u) := by
        intro t ht
        rw [hpart]
        refine congrArg₂ (· + ·) ?_ ?_
        · refine Finset.sum_congr rfl fun p' _ => by rw [hemb_out_const w t ht, hemb_pos]
        · refine Finset.sum_congr rfl fun u hu => by rw [hemb_out_const w t ht, hemb_out_const w u hu]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      refine congrArg₂ (· + ·) ?_ rfl
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p' _ => ?_
      rw [Finset.sum_mul]
    rw [hleft, hright]
    ring
  rw [hlin, hquad]
  have ha' : dotProduct a' w =
      (∑ p : Fin m × Fin 3, a (pos p) * w p) +
      (∑ p : Fin m × Fin 3, (∑ u ∈ Sc, M (pos p) u * cVal u) * w p) +
      (∑ p : Fin m × Fin 3, (∑ t ∈ Sc, M t (pos p) * cVal t) * w p) := by
    simp only [dotProduct, a', add_mul, Finset.sum_add_distrib]
  dsimp only [b', M']
  rw [ha']
  ring

theorem disjoint_triples_quad_bias (m n : ℕ) (pos : (Fin m × Fin 3) ↪ Fin n)
    (q : (Fin n → F2) → F2) (hq : IsQuad q) :
    4 ^ m * (∑ z : Fin n → F2,
      if q z = ∑ i : Fin m, z (pos (i, 0)) * z (pos (i, 1)) * z (pos (i, 2))
      then (1 : ℤ) else -1).natAbs ≤ 3 ^ m * 2 ^ n := by
  classical
  let Rest := {t : Fin n // t ∉ Set.range pos}
  let e : (((Fin m × Fin 3) → F2) × (Rest → F2)) ≃ (Fin n → F2) :=
    { toFun := fun wr t =>
        if h : ∃ p, pos p = t then wr.1 (Classical.choose h) else wr.2 ⟨t, h⟩
      invFun := fun z => (fun p => z (pos p), fun t => z t.1)
      left_inv := by
        rintro ⟨w, r⟩
        ext p
        · have hex : ∃ p', pos p' = pos p := ⟨p, rfl⟩
          simp only [hex, ↓reduceDIte]
          congr 1
          exact pos.injective (Classical.choose_spec hex)
        · have hno : ¬ ∃ p', pos p' = p.1 := p.2
          simp only [hno, ↓reduceDIte]
          rfl
      right_inv := by
        intro z
        funext t
        by_cases h : ∃ p, pos p = t
        · simp only [h, ↓reduceDIte, Classical.choose_spec h]
        · simp only [h, ↓reduceDIte] }
  have h3m_le : 3 * m ≤ n := by
    have hcard := Fintype.card_le_of_injective pos pos.injective
    simp only [Fintype.card_prod, Fintype.card_fin] at hcard
    omega
  have hRest_card : Fintype.card Rest = n - 3 * m := by
    have h1 : Fintype.card Rest = (Finset.univ.filter (fun t : Fin n => t ∉ Set.range pos)).card :=
      Fintype.card_subtype _
    have h2 : (Finset.univ.filter (fun t : Fin n => t ∈ Set.range pos)) =
        Finset.univ.image pos := by
      ext t; simp
    have h3 : (Finset.univ.filter (fun t : Fin n => t ∈ Set.range pos)).card +
        (Finset.univ.filter (fun t : Fin n => t ∉ Set.range pos)).card = n := by
      simpa [Finset.card_fin] using
        card_filter_add_not (Finset.univ : Finset (Fin n)) (fun t => t ∈ Set.range pos)
    have h4 : (Finset.univ.image pos).card = 3 * m := by
      rw [Finset.card_image_of_injective _ pos.injective, Finset.card_univ, Fintype.card_prod]
      simp only [Fintype.card_fin]
      ring
    rw [h2, h4] at h3
    omega
  have hsum_abs : |∑ z : Fin n → F2,
      if q z = ∑ i : Fin m, z (pos (i, 0)) * z (pos (i, 1)) * z (pos (i, 2))
      then (1 : ℤ) else -1| ≤ (2 : ℤ) ^ (n - 3 * m) * (6 : ℤ) ^ m := by
    rw [← e.sum_comp, Fintype.sum_prod_type_right]
    calc |∑ r : Rest → F2, ∑ w : (Fin m × Fin 3) → F2,
            if q (e (w, r)) = ∑ i : Fin m,
              e (w, r) (pos (i, 0)) * e (w, r) (pos (i, 1)) * e (w, r) (pos (i, 2))
            then (1 : ℤ) else -1|
        ≤ ∑ r : Rest → F2, |∑ w : (Fin m × Fin 3) → F2,
            if q (e (w, r)) = ∑ i : Fin m,
              e (w, r) (pos (i, 0)) * e (w, r) (pos (i, 1)) * e (w, r) (pos (i, 2))
            then (1 : ℤ) else -1| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : Rest → F2, (6 : ℤ) ^ m := by
          refine Finset.sum_le_sum fun r _ => ?_
          have hcongr : ∀ w : (Fin m × Fin 3) → F2,
              (if q (e (w, r)) = ∑ i : Fin m,
                e (w, r) (pos (i, 0)) * e (w, r) (pos (i, 1)) * e (w, r) (pos (i, 2))
               then (1 : ℤ) else -1) =
              chi (q (e (w, r)) + ∑ i : Fin m, w (i, 0) * w (i, 1) * w (i, 2)) := by
            intro w
            rw [chi_eq]
            have hep : ∀ p, e (w, r) (pos p) = w p := fun p => by
              dsimp only [e, Equiv.coe_fn_mk]
              have hex : ∃ p', pos p' = pos p := ⟨p, rfl⟩
              simp only [hex, ↓reduceDIte]
              congr 1
              exact pos.injective (Classical.choose_spec hex)
            simp_rw [hep]
          simp_rw [hcongr]
          exact disjoint_triples_core m (fun w => q (e (w, r))) (quad_restrict_emb pos q hq r)
      _ = (2 : ℤ) ^ (n - 3 * m) * (6 : ℤ) ^ m := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, hRest_card]
          have hF2 : Fintype.card F2 = 2 := rfl
          rw [hF2]
          norm_cast
  have hnat : (∑ z : Fin n → F2,
      if q z = ∑ i : Fin m, z (pos (i, 0)) * z (pos (i, 1)) * z (pos (i, 2))
      then (1 : ℤ) else -1).natAbs ≤ 2 ^ (n - 3 * m) * 6 ^ m := by
    have hZ : (((∑ z : Fin n → F2,
        if q z = ∑ i : Fin m, z (pos (i, 0)) * z (pos (i, 1)) * z (pos (i, 2))
        then (1 : ℤ) else -1).natAbs : ℕ) : ℤ) ≤ ((2 ^ (n - 3 * m) * 6 ^ m : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      simpa using hsum_abs
    exact Int.ofNat_le.mp hZ
  calc 4 ^ m * (∑ z : Fin n → F2,
        if q z = ∑ i : Fin m, z (pos (i, 0)) * z (pos (i, 1)) * z (pos (i, 2))
        then (1 : ℤ) else -1).natAbs
      ≤ 4 ^ m * (2 ^ (n - 3 * m) * 6 ^ m) := Nat.mul_le_mul_left _ hnat
    _ = 3 ^ m * (2 ^ (3 * m) * 2 ^ (n - 3 * m)) := by
        calc 4 ^ m * (2 ^ (n - 3 * m) * 6 ^ m)
            = (4 * 6) ^ m * 2 ^ (n - 3 * m) := by rw [mul_pow]; ring
          _ = (3 * 2 ^ 3) ^ m * 2 ^ (n - 3 * m) := by norm_num
          _ = 3 ^ m * (2 ^ (3 * m) * 2 ^ (n - 3 * m)) := by
              rw [mul_pow, ← pow_mul]; ring
    _ = 3 ^ m * 2 ^ n := by
        rw [← pow_add, show 3 * m + (n - 3 * m) = n by omega]

lemma quad_restrict_head {n : ℕ} (c : F2) (q : (Fin (n + 1) → F2) → F2) (hq : IsQuad q) :
    IsQuad (fun z : Fin n → F2 => q (consF2 c z)) := by
  obtain ⟨b, a, M, hqeq⟩ := hq
  refine ⟨b + a 0 * c + M 0 0 * c * c,
    fun i => a i.succ + M 0 i.succ * c + M i.succ 0 * c,
    fun i j => M i.succ j.succ, fun z => ?_⟩
  dsimp only
  rw [hqeq (consF2 c z)]
  have h1 : dotProduct a (consF2 c z) = a 0 * c + ∑ i : Fin n, a i.succ * z i := by
    simp [dotProduct, Fin.sum_univ_succ, consF2_zero, consF2_succ]
  have h2 : (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M i j * consF2 c z i * consF2 c z j) =
      M 0 0 * c * c +
      (∑ j : Fin n, M 0 j.succ * c * z j) +
      (∑ i : Fin n, M i.succ 0 * z i * c) +
      (∑ i : Fin n, ∑ j : Fin n, M i.succ j.succ * z i * z j) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [consF2_zero, consF2_succ]
    have htail : (∑ i : Fin n, ∑ j : Fin (n + 1), M i.succ j * z i * consF2 c z j) =
        (∑ i : Fin n, M i.succ 0 * z i * c) +
        (∑ i : Fin n, ∑ j : Fin n, M i.succ j.succ * z i * z j) := by
      simp_rw [Fin.sum_univ_succ, consF2_zero, consF2_succ]
      rw [Finset.sum_add_distrib]
    rw [htail]
    ring
  rw [h1, h2]
  simp only [dotProduct, add_mul, Finset.sum_add_distrib]
  have hswap : (∑ i : Fin n, M i.succ 0 * c * z i) = ∑ i : Fin n, M i.succ 0 * z i * c := by
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hswap]
  ring

lemma three_pow_lt_four_pow_pred {m : ℕ} (hm : 5 ≤ m) : 3 ^ m < 4 ^ (m - 1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h5 : m = 4
    · subst h5; norm_num
    · have hm5 : 5 ≤ m := by omega
      have hlt := ih hm5
      calc 3 ^ (m + 1) = 3 * 3 ^ m := by rw [pow_succ']
        _ < 3 * 4 ^ (m - 1) := by omega
        _ < 4 * 4 ^ (m - 1) := by
            have : 0 < 4 ^ (m - 1) := by positivity
            omega
        _ = 4 ^ m := by
            rw [← pow_succ', show m - 1 + 1 = m by omega]

theorem switched_cubic_quad_bias :
  ∀ (m n : ℕ),
    let k := n + 1
    let F := ZMod 2
    let V := Fin k → F
    5 ≤ m → ∀ (pos : (Fin m × Fin 3) ↪ Fin n) (i₀ : Fin m),
      let trip := fun (y : V) (i : Fin m) =>
        y (pos (i, 0)).succ * y (pos (i, 1)).succ * y (pos (i, 2)).succ
      let g := fun y : V => if y 0 = 0 then trip y i₀ else ∑ i, trip y i
      let quad := fun (q : V → F) =>
        ∃ (b : F) (a : V) (M : Fin k → Fin k → F), ∀ y,
          q y = b + dotProduct a y + ∑ i, ∑ j, M i j * y i * y j
      ∀ q : V → F, quad q →
        let v := (∑ y : V, if q y = g y then (1 : ℤ) else -1).natAbs
        2 * 4 ^ m * v ≤ (3 * 4 ^ (m - 1) + 3 ^ m) * 2 ^ k ∧ 2 * v < 2 ^ k := by
  intro m n k F V hm pos i₀ trip g quad q hq v
  let eHead : (F2 × (Fin n → F2)) ≃ (Fin (n + 1) → F2) :=
    { toFun := fun p => consF2 p.1 p.2
      invFun := fun y => (y 0, Fin.tail y)
      left_inv := fun ⟨b, z⟩ => by
        refine Prod.ext (consF2_zero b z) ?_
        funext i
        exact consF2_succ b z i
      right_inv := fun y => consF2_self_tail y }
  let S0 : ℤ := ∑ z : Fin n → F2,
    if q (consF2 0 z) = z (pos (i₀, 0)) * z (pos (i₀, 1)) * z (pos (i₀, 2))
    then (1 : ℤ) else -1
  let S1 : ℤ := ∑ z : Fin n → F2,
    if q (consF2 1 z) = ∑ i : Fin m, z (pos (i, 0)) * z (pos (i, 1)) * z (pos (i, 2))
    then (1 : ℤ) else -1
  have hsplit : (∑ y : V, if q y = g y then (1 : ℤ) else -1) = S0 + S1 := by
    rw [← eHead.sum_comp, Fintype.sum_prod_type]
    have hF2sum : ∀ f : F2 → ℤ, ∑ b : F2, f b = f 0 + f 1 := fun f => Fin.sum_univ_two f
    rw [hF2sum]
    have hL : (∑ z : Fin n → F2, if q (eHead (0, z)) = g (eHead (0, z)) then (1 : ℤ) else -1) = S0 := by
      refine Finset.sum_congr rfl fun z _ => ?_
      dsimp only [eHead, Equiv.coe_fn_mk, g, trip]
      simp [consF2_zero, consF2_succ]
    have hR : (∑ z : Fin n → F2, if q (eHead (1, z)) = g (eHead (1, z)) then (1 : ℤ) else -1) = S1 := by
      refine Finset.sum_congr rfl fun z _ => ?_
      dsimp only [eHead, Equiv.coe_fn_mk, g, trip]
      have hne : (1 : F2) ≠ 0 := by decide
      simp [consF2_zero, consF2_succ, hne]
    exact congrArg₂ (· + ·) hL hR
  have hv_le : v ≤ S0.natAbs + S1.natAbs := by
    dsimp only [v]
    rw [hsplit]
    exact Int.natAbs_add_le S0 S1
  let pos1 : (Fin 1 × Fin 3) ↪ Fin n :=
    ⟨fun p => pos (i₀, p.2), fun p1 p2 h =>
      Prod.ext (Subsingleton.elim p1.1 p2.1) (Prod.mk.inj (pos.injective h)).2⟩
  have h0_raw := disjoint_triples_quad_bias 1 n pos1 (fun z => q (consF2 0 z))
    (quad_restrict_head 0 q hq)
  have hS0_eq : (∑ z : Fin n → F2,
      if q (consF2 0 z) = ∑ i : Fin 1, z (pos1 (i, 0)) * z (pos1 (i, 1)) * z (pos1 (i, 2))
      then (1 : ℤ) else -1) = S0 := by
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [Fin.sum_univ_one]
    rfl
  rw [hS0_eq] at h0_raw
  have h0_bound : 4 ^ m * S0.natAbs ≤ 3 * 4 ^ (m - 1) * 2 ^ n := by
    have hmul := Nat.mul_le_mul_left (4 ^ (m - 1)) h0_raw
    calc 4 ^ m * S0.natAbs = 4 ^ (m - 1) * (4 ^ 1 * S0.natAbs) := by
          rw [pow_one, ← mul_assoc, ← pow_succ, show m - 1 + 1 = m by omega]
      _ ≤ 4 ^ (m - 1) * (3 ^ 1 * 2 ^ n) := hmul
      _ = 3 * 4 ^ (m - 1) * 2 ^ n := by ring
  have h1_bound : 4 ^ m * S1.natAbs ≤ 3 ^ m * 2 ^ n :=
    disjoint_triples_quad_bias m n pos (fun z => q (consF2 1 z)) (quad_restrict_head 1 q hq)
  have hmain : 2 * 4 ^ m * v ≤ (3 * 4 ^ (m - 1) + 3 ^ m) * 2 ^ k := by
    have hhalf : 4 ^ m * v ≤ (3 * 4 ^ (m - 1) + 3 ^ m) * 2 ^ n := by
      calc 4 ^ m * v ≤ 4 ^ m * (S0.natAbs + S1.natAbs) := Nat.mul_le_mul_left _ hv_le
        _ = 4 ^ m * S0.natAbs + 4 ^ m * S1.natAbs := Nat.mul_add _ _ _
        _ ≤ 3 * 4 ^ (m - 1) * 2 ^ n + 3 ^ m * 2 ^ n := Nat.add_le_add h0_bound h1_bound
        _ = (3 * 4 ^ (m - 1) + 3 ^ m) * 2 ^ n := by ring
    calc 2 * 4 ^ m * v = 2 * (4 ^ m * v) := by ring
      _ ≤ 2 * ((3 * 4 ^ (m - 1) + 3 ^ m) * 2 ^ n) := Nat.mul_le_mul_left 2 hhalf
      _ = (3 * 4 ^ (m - 1) + 3 ^ m) * 2 ^ k := by
        dsimp only [k]
        rw [pow_succ']
        ring
  refine ⟨hmain, ?_⟩
  have h34 : 3 ^ m < 4 ^ (m - 1) := three_pow_lt_four_pow_pred hm
  have hcoeff : 3 * 4 ^ (m - 1) + 3 ^ m < 4 ^ m := by
    calc 3 * 4 ^ (m - 1) + 3 ^ m < 3 * 4 ^ (m - 1) + 4 ^ (m - 1) := Nat.add_lt_add_left h34 _
      _ = 4 * 4 ^ (m - 1) := by ring
      _ = 4 ^ m := by rw [← pow_succ', show m - 1 + 1 = m by omega]
  have hstrict : 4 ^ m * (2 * v) < 4 ^ m * 2 ^ k := by
    calc 4 ^ m * (2 * v) = 2 * 4 ^ m * v := by ring
      _ ≤ (3 * 4 ^ (m - 1) + 3 ^ m) * 2 ^ k := hmain
      _ < 4 ^ m * 2 ^ k := Nat.mul_lt_mul_of_pos_right hcoeff (by positivity)
  exact Nat.lt_of_mul_lt_mul_left hstrict

end Bias

end PEqualNP.Outside.L_meta_29782_aux

theorem PEqualNP.Outside.L_meta_29782 : (∀ (m n : ℕ),
  let k := n+1
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let F := ZMod 2
  let legal := fun (n : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (n : ℕ) (u : Fin n → F) => List.ofFn (fun j : Fin n => decide (u j = 1))
  let V := Fin k → F
  let raw := fun (g : V → F) (C : Circ) => (∑ x : V, ∑ y : V,
    if C.eval (bits k x ++ bits k y) = decide (dotProduct x y + g y = 1)
    then (1 : ℤ) else -1).natAbs
  5 ≤ m → ∀ (pos : (Fin m × Fin 3) ↪ Fin n) (i₀ : Fin m),
    let trip := fun (y : V) (i : Fin m) =>
      y (pos (i,0)).succ * y (pos (i,1)).succ * y (pos (i,2)).succ
    let g := fun y : V => if y 0 = 0 then trip y i₀ else ∑ i, trip y i
    let quad := fun (q : V → F) =>
      ∃ (b : F) (a : V) (M : Fin k → Fin k → F), ∀ y,
        q y = b + dotProduct a y + ∑ i, ∑ j, M i j * y i * y j
    (∀ C : Circ, legal (2*k) C → cost C ≤ k → 2 * raw g C ≤ 2^(2*k)) ∧
    (∃ C : Circ, legal (2*k) C ∧ cost C ≤ k ∧ 2 * raw g C = 2^(2*k)) ∧
    (∀ q : V → F, quad q →
      let v := (∑ y : V, if q y = g y then (1 : ℤ) else -1).natAbs
      2 * 4^m * v ≤ (3*4^(m-1)+3^m) * 2^k ∧ 2*v < 2^k)) := by
  intro m n k Circ F legal cost bits V raw hm pos i₀ trip g quad
  have hquad : ∀ q : V → F, quad q →
      let v := (∑ y : V, if q y = g y then (1 : ℤ) else -1).natAbs
      2 * 4^m * v ≤ (3*4^(m-1)+3^m) * 2^k ∧ 2*v < 2^k :=
    PEqualNP.Outside.L_meta_29782_aux.Bias.switched_cubic_quad_bias m n hm pos i₀
  refine ⟨?_, ?_, hquad⟩
  · intro C hLegal hCost
    exact PEqualNP.Outside.L_meta_29782_aux.CircuitProof.rawUpper g
      (fun q hq => (hquad q hq).2) C hLegal hCost
  · apply PEqualNP.Outside.L_meta_29782_aux.CircuitProof.rawWitness (pos (i₀,0)) (pos (i₀,1)) (pos (i₀,2)) g
    intro y hy
    simp [g,hy,trip]
