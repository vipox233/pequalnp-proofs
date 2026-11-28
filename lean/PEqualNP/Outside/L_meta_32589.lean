import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32589_aux

-- Circuit splitting, character sums, and gate appenders adapted from the accepted
-- lean/PEqualNP/Outside/L_meta_32052.lean at d2903f50aab2ec49b64f2185520f812232258eca.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

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

open Classical

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

lemma appendConst_spec (n : ℕ) (gs : List Gate) (b : F2) (hgs : legalGates n gs) :
    let g := if b = 1 then Gate.mk .and [] else Gate.mk .or []
    let gs' := gs ++ [g]
    legalGates n gs' ∧
    costGates gs' = costGates gs ∧
    n + gs.length < n + gs'.length ∧
    ∀ x : List Bool, x.length = n →
      (wiresOf gs' x).getD (n + gs.length) false = decide (b = 1) := by
  intro g gs'
  have hshape : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)) := by
    dsimp only [g]; split_ifs
    · exact ⟨by simp, Or.inl rfl⟩
    · exact ⟨by simp, Or.inr (Or.inl rfl)⟩
  have hback : ∀ i ∈ g.inputs, i < n + gs.length := by
    dsimp only [g]; split_ifs <;> simp
  refine ⟨legalGates_snoc hgs hback hshape, ?_, by simp [gs'], ?_⟩
  · apply costGates_snoc_zero gs g
    dsimp only [g]; split_ifs <;> simp
  · intro x hx
    rw [wiresOf_snoc_last_eq gs g x hx]
    rcases zmod2_cases b with rfl | rfl <;> simp [g, GateOp.eval]

def appendAffineLoop (n : ℕ) (c : Fin n → F2) : (m : ℕ) → m ≤ n → List Gate → ℕ → List Gate × ℕ
  | 0, _, gs, acc => (gs, acc)
  | m + 1, hm, gs, acc =>
    let res := appendAffineLoop n c m (by omega) gs acc
    let gs1 := res.1
    let acc1 := res.2
    if c ⟨m, hm⟩ = 1 then
      (gs1 ++ [⟨.mod 2, [acc1, m]⟩, ⟨.not, [n + gs1.length]⟩], n + gs1.length + 1)
    else (gs1, acc1)

lemma appendAffineLoop_spec (n : ℕ) (c : Fin n → F2) :
    ∀ (m : ℕ) (hm : m ≤ n) (gs : List Gate) (acc : ℕ),
      legalGates n gs → acc < n + gs.length →
      let res := appendAffineLoop n c m hm gs acc
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates n res.1 ∧
        costGates res.1 = costGates gs ∧
        res.2 < n + res.1.length ∧
        ∀ u : Fin n → F2,
          (wiresOf res.1 (bitsOf n u)).getD res.2 false =
            Bool.xor ((wiresOf gs (bitsOf n u)).getD acc false)
              (decide ((∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < m), c j * u j) = 1)) := by
  intro m
  induction m with
  | zero =>
    intro hm gs acc hleg hacc
    refine ⟨[], by simp [appendAffineLoop], hleg, rfl, hacc, fun u => ?_⟩
    have hemp : Finset.univ.filter (fun j : Fin n => j.val < 0) = ∅ := by ext j; simp
    simp [appendAffineLoop, hemp]
  | succ m ih =>
    intro hm gs acc hleg hacc
    rcases ih (by omega) gs acc hleg hacc with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set gs1 := (appendAffineLoop n c m (by omega) gs acc).1
    set acc1 := (appendAffineLoop n c m (by omega) gs acc).2
    have hsplit : (Finset.univ.filter (fun j : Fin n => j.val < m + 1)) =
        insert ⟨m, hm⟩ (Finset.univ.filter (fun j : Fin n => j.val < m)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hnotmem : (⟨m, hm⟩ : Fin n) ∉ Finset.univ.filter (fun j : Fin n => j.val < m) := by simp
    by_cases hcm : c ⟨m, hm⟩ = 1
    · have hstep := addXor_step n gs1 acc1 m h1leg h1lt (by omega)
      refine ⟨ext1 ++ [⟨.mod 2, [acc1, m]⟩, ⟨.not, [n + gs1.length]⟩], ?_, ?_, ?_, ?_, ?_⟩
      · simp [appendAffineLoop, hcm, gs1, acc1, h1eq, List.append_assoc]
      · simpa [appendAffineLoop, hcm, gs1, acc1] using hstep.1
      · simpa [appendAffineLoop, hcm, gs1, acc1, h1cost] using hstep.2.1
      · simp only [appendAffineLoop, hcm, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]
        omega
      · intro u
        simp only [appendAffineLoop, hcm, ↓reduceIte]
        change (wiresOf (gs1 ++ [⟨.mod 2, [acc1, m]⟩, ⟨.not, [n + gs1.length]⟩]) (bitsOf n u)).getD (n + gs1.length + 1) false = _
        rw [hstep.2.2.2 (bitsOf n u) (bitsOf_len n u), h1sem u]
        have hm_wire : (wiresOf gs1 (bitsOf n u)).getD m false = decide (u ⟨m, hm⟩ = 1) := by
          rw [wiresOf_getD_lt gs1 (bitsOf n u) (by rw [bitsOf_len]; exact hm)]
          exact bitsOf_getD n u ⟨m, hm⟩
        rw [hm_wire, hsplit, Finset.sum_insert hnotmem, hcm, one_mul, zmod2_add_decide]
        cases (wiresOf gs (bitsOf n u)).getD acc false <;>
          cases decide (u ⟨m, hm⟩ = 1) <;>
          cases decide ((∑ x ∈ Finset.univ.filter (fun j : Fin n => j.val < m), c x * u x) = 1) <;> decide
    · have hcm0 : c ⟨m, hm⟩ = 0 := by
        rcases zmod2_cases (c ⟨m, hm⟩) with h0 | h1
        · exact h0
        · exact absurd h1 hcm
      refine ⟨ext1, ?_, ?_, ?_, ?_, ?_⟩
      · simp [appendAffineLoop, hcm, gs1, h1eq]
      · simpa [appendAffineLoop, hcm, gs1] using h1leg
      · simpa [appendAffineLoop, hcm, gs1] using h1cost
      · simpa [appendAffineLoop, hcm, gs1, acc1] using h1lt
      · intro u
        simp only [appendAffineLoop, hcm, ↓reduceIte]
        rw [h1sem u, hsplit, Finset.sum_insert hnotmem, hcm0, zero_mul, zero_add]

def appendAffine (n : ℕ) (gs : List Gate) (c : Fin n → F2) (b : F2) : List Gate × ℕ :=
  let g0 := if b = 1 then Gate.mk .and [] else Gate.mk .or []
  appendAffineLoop n c n (le_refl n) (gs ++ [g0]) (n + gs.length)

lemma appendAffine_spec (n : ℕ) (gs : List Gate) (c : Fin n → F2) (b : F2) (hgs : legalGates n gs) :
    let res := appendAffine n gs c b
    ∃ ext : List Gate,
      res.1 = gs ++ ext ∧
      legalGates n res.1 ∧
      costGates res.1 = costGates gs ∧
      res.2 < n + res.1.length ∧
      ∀ u : Fin n → F2,
        (wiresOf res.1 (bitsOf n u)).getD res.2 false = decide (dotProduct c u + b = 1) := by
  have hc := appendConst_spec n gs b hgs
  let g0 := if b = 1 then Gate.mk .and [] else Gate.mk .or []
  rcases appendAffineLoop_spec n c n (le_refl n) (gs ++ [g0]) (n + gs.length) hc.1 hc.2.2.1 with
    ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
  refine ⟨[g0] ++ ext1, ?_, h1leg, ?_, h1lt, ?_⟩
  · simpa [appendAffine, g0, List.append_assoc] using h1eq
  · dsimp only [appendAffine]
    rw [h1cost, hc.2.1]
  · intro u
    change (wiresOf (appendAffineLoop n c n (le_refl n) (gs ++ [g0]) (n + gs.length)).1 (bitsOf n u)).getD
        (appendAffineLoop n c n (le_refl n) (gs ++ [g0]) (n + gs.length)).2 false = _
    rw [h1sem u, hc.2.2.2 (bitsOf n u) (bitsOf_len n u)]
    have huniv : Finset.univ.filter (fun j : Fin n => j.val < n) = Finset.univ := by
      ext j; simp [j.isLt]
    rw [huniv]
    change Bool.xor (decide (b = 1)) (decide (dotProduct c u = 1)) = _
    rw [zmod2_add_decide, Bool.xor_comm]

def appendSumProdsLoop (n s : ℕ) (cA cB : Fin s → Fin n → F2) (bA bB : Fin s → F2) :
    (m : ℕ) → m ≤ s → List Gate → ℕ → List Gate × ℕ
  | 0, _, gs, acc => (gs, acc)
  | m + 1, hm, gs, acc =>
    let res1 := appendSumProdsLoop n s cA cB bA bB m (by omega) gs acc
    let gs1 := res1.1
    let acc1 := res1.2
    let resA := appendAffine n gs1 (cA ⟨m, hm⟩) (bA ⟨m, hm⟩)
    let gs2 := resA.1
    let wA := resA.2
    let resB := appendAffine n gs2 (cB ⟨m, hm⟩) (bB ⟨m, hm⟩)
    let gs3 := resB.1
    let wB := resB.2
    let gs4 := gs3 ++ [⟨.and, [wA, wB]⟩]
    let wP := n + gs3.length
    (gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩], n + gs4.length + 1)

lemma appendSumProdsLoop_spec (n s : ℕ) (cA cB : Fin s → Fin n → F2) (bA bB : Fin s → F2) :
    ∀ (m : ℕ) (hm : m ≤ s) (gs : List Gate) (acc : ℕ),
      legalGates n gs → acc < n + gs.length →
      let res := appendSumProdsLoop n s cA cB bA bB m hm gs acc
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates n res.1 ∧
        costGates res.1 = costGates gs + m ∧
        res.2 < n + res.1.length ∧
        ∀ u : Fin n → F2,
          (wiresOf res.1 (bitsOf n u)).getD res.2 false =
            Bool.xor ((wiresOf gs (bitsOf n u)).getD acc false)
              (decide ((∑ i ∈ Finset.univ.filter (fun i : Fin s => i.val < m),
                (dotProduct (cA i) u + bA i) * (dotProduct (cB i) u + bB i)) = 1)) := by
  intro m
  induction m with
  | zero =>
    intro hm gs acc hleg hacc
    refine ⟨[], by simp [appendSumProdsLoop], hleg, by simp [appendSumProdsLoop], hacc, fun u => ?_⟩
    have hemp : Finset.univ.filter (fun i : Fin s => i.val < 0) = ∅ := by ext i; simp
    simp [appendSumProdsLoop, hemp]
  | succ m ih =>
    intro hm gs acc hleg hacc
    rcases ih (by omega) gs acc hleg hacc with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set res1 := appendSumProdsLoop n s cA cB bA bB m (by omega) gs acc
    set gs1 := res1.1
    set acc1 := res1.2
    rcases appendAffine_spec n gs1 (cA ⟨m, hm⟩) (bA ⟨m, hm⟩) h1leg with ⟨extA, hAeq, hAleg, hAcost, hAlt, hAsem⟩
    set resA := appendAffine n gs1 (cA ⟨m, hm⟩) (bA ⟨m, hm⟩)
    set gs2 := resA.1
    set wA := resA.2
    rcases appendAffine_spec n gs2 (cB ⟨m, hm⟩) (bB ⟨m, hm⟩) hAleg with ⟨extB, hBeq, hBleg, hBcost, hBlt, hBsem⟩
    set resB := appendAffine n gs2 (cB ⟨m, hm⟩) (bB ⟨m, hm⟩)
    set gs3 := resB.1
    set wB := resB.2
    have hwA_lt3 : wA < n + gs3.length := by rw [hBeq, List.length_append]; omega
    set gs4 := gs3 ++ [⟨.and, [wA, wB]⟩]
    set wP := n + gs3.length
    have h4leg : legalGates n gs4 :=
      legalGates_snoc hBleg (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hwA_lt3; exact hBlt)
        ⟨by simp, Or.inl rfl⟩
    have h4cost : costGates gs4 = costGates gs3 + 1 :=
      costGates_snoc_one gs3 ⟨.and, [wA, wB]⟩ ⟨Or.inl rfl, rfl⟩
    have hacc1_lt4 : acc1 < n + gs4.length := by
      simp only [gs4, hBeq, hAeq, List.length_append, List.length_singleton]; omega
    have hwP_lt4 : wP < n + gs4.length := by simp [gs4, wP]
    have hstep := addXor_step n gs4 acc1 wP h4leg hacc1_lt4 hwP_lt4
    refine ⟨ext1 ++ extA ++ extB ++ [⟨.and, [wA, wB]⟩, ⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩],
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only [appendSumProdsLoop]
      change gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩] = _
      simp only [gs4, hBeq, hAeq, h1eq, List.append_assoc, List.cons_append, List.nil_append]
    · exact hstep.1
    · change costGates (gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩]) = _
      rw [hstep.2.1, h4cost, hBcost, hAcost, h1cost]; omega
    · change n + gs4.length + 1 < n + (gs4 ++ ([⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩] : List Gate)).length
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro u
      change (wiresOf (gs4 ++ [⟨.mod 2, [acc1, wP]⟩, ⟨.not, [n + gs4.length]⟩]) (bitsOf n u)).getD (n + gs4.length + 1) false = _
      rw [hstep.2.2.2 (bitsOf n u) (bitsOf_len n u)]
      have hacc1_eq : (wiresOf gs4 (bitsOf n u)).getD acc1 false = (wiresOf gs1 (bitsOf n u)).getD acc1 false := by
        have hgs4_eq : gs4 = gs1 ++ (extA ++ extB ++ [⟨.and, [wA, wB]⟩]) := by
          simp only [gs4, hBeq, hAeq, List.append_assoc]
        rw [hgs4_eq, wiresOf_append_getD_lt gs1 _ (bitsOf n u) (by rw [bitsOf_len]; exact h1lt)]
      have hwP_eq : (wiresOf gs4 (bitsOf n u)).getD wP false =
          decide ((dotProduct (cA ⟨m, hm⟩) u + bA ⟨m, hm⟩) * (dotProduct (cB ⟨m, hm⟩) u + bB ⟨m, hm⟩) = 1) := by
        change (wiresOf (gs3 ++ [⟨.and, [wA, wB]⟩]) (bitsOf n u)).getD (n + gs3.length) false = _
        rw [wiresOf_snoc_last_eq gs3 ⟨.and, [wA, wB]⟩ (bitsOf n u) (bitsOf_len n u)]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        have hwA_val : (wiresOf gs3 (bitsOf n u)).getD wA false = decide (dotProduct (cA ⟨m, hm⟩) u + bA ⟨m, hm⟩ = 1) := by
          rw [hBeq, wiresOf_append_getD_lt gs2 extB (bitsOf n u) (by rw [bitsOf_len]; exact hAlt)]
          exact hAsem u
        rw [hwA_val, hBsem u, zmod2_mul_decide]
      rw [hacc1_eq, h1sem u, hwP_eq]
      have hsplit : (Finset.univ.filter (fun i : Fin s => i.val < m + 1)) =
          insert ⟨m, hm⟩ (Finset.univ.filter (fun i : Fin s => i.val < m)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      have hnotmem : (⟨m, hm⟩ : Fin s) ∉ Finset.univ.filter (fun i : Fin s => i.val < m) := by simp
      rw [hsplit, Finset.sum_insert hnotmem, zmod2_add_decide]
      cases (wiresOf gs (bitsOf n u)).getD acc false <;>
        cases decide ((dotProduct (cA ⟨m, hm⟩) u + bA ⟨m, hm⟩) * (dotProduct (cB ⟨m, hm⟩) u + bB ⟨m, hm⟩) = 1) <;>
        cases decide ((∑ x ∈ Finset.univ.filter (fun i : Fin s => i.val < m),
          (dotProduct (cA x) u + bA x) * (dotProduct (cB x) u + bB x)) = 1) <;> decide

lemma build_sum_prods_circuit (n s : ℕ) (c0 : Fin n → F2) (b0 : F2)
    (cA cB : Fin s → Fin n → F2) (bA bB : Fin s → F2) :
    ∃ C : Circuit, legalGates n C.gates ∧ costGates C.gates = s ∧
      ∀ u : Fin n → F2, C.eval (bitsOf n u) =
        decide ((dotProduct c0 u + b0) +
          ∑ i : Fin s, (dotProduct (cA i) u + bA i) * (dotProduct (cB i) u + bB i) = 1) := by
  have hnil : legalGates n [] := ⟨fun j hj => by simp at hj, fun h hh => by simp at hh⟩
  rcases appendAffine_spec n [] c0 b0 hnil with ⟨_, _, h0leg, h0cost, h0lt, h0sem⟩
  set res0 := appendAffine n [] c0 b0
  rcases appendSumProdsLoop_spec n s cA cB bA bB s (le_refl s) res0.1 res0.2 h0leg h0lt with
    ⟨_, _, hleg, hcost, _, hsem⟩
  set res := appendSumProdsLoop n s cA cB bA bB s (le_refl s) res0.1 res0.2
  refine ⟨⟨res.1, res.2⟩, hleg, ?_, fun u => ?_⟩
  · have hc0 : costGates ([] : List Gate) = 0 := by simp [costGates]
    dsimp only [res, res0] at hcost h0cost ⊢
    omega
  · change (wiresOf res.1 (bitsOf n u)).getD res.2 false = _
    rw [hsem u, h0sem u]
    have huniv : Finset.univ.filter (fun i : Fin s => i.val < s) = Finset.univ := by
      ext i; simp
    rw [huniv, ← zmod2_add_decide]

def concatVec {k : ℕ} (x y : Fin k → F2) : Fin (2 * k) → F2 :=
  fun idx => if h : idx.val < k then x ⟨idx.val, h⟩ else y ⟨idx.val - k, by omega⟩

lemma bitsOf_concatVec {k : ℕ} (x y : Fin k → F2) :
    bitsOf k x ++ bitsOf k y = bitsOf (2 * k) (concatVec x y) := by
  apply List.ext_getElem
  · simp [bitsOf_len]; omega
  · intro i h1 h2
    simp only [bitsOf]
    by_cases hik : i < k
    · rw [List.getElem_append_left (by simp; exact hik)]
      simp [concatVec, hik]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [concatVec, hik]

lemma dotProduct_concatVec {k : ℕ} (u v x y : Fin k → F2) :
    dotProduct (concatVec u v) (concatVec x y) = dotProduct u x + dotProduct v y := by
  simp only [dotProduct]
  let e : Fin k ⊕ Fin k ≃ Fin (2 * k) :=
    { toFun := Sum.elim (fun i => ⟨i.val, by omega⟩) (fun i => ⟨k + i.val, by omega⟩)
      invFun := fun i => if h : i.val < k then Sum.inl ⟨i.val, h⟩ else Sum.inr ⟨i.val - k, by omega⟩
      left_inv := fun s => by
        cases s with
        | inl i => simp [i.isLt]
        | inr i =>
          have hnot : ¬ (k + i.val < k) := by omega
          simp [hnot]
      right_inv := fun i => by
        by_cases h : i.val < k
        · simp [h]
        · simp only [h, ↓reduceDIte, Sum.elim_inr]
          apply Fin.ext; dsimp; omega }
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [e, concatVec, i.isLt]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hnot : ¬ (k + i.val < k) := by omega
    simp [e, concatVec, hnot]

lemma linear_map_left_inv {k s : ℕ} (B : (Fin s → F2) →ₗ[F2] (Fin k → F2))
    (hB : Function.Injective B) :
    ∃ L : (Fin k → F2) →ₗ[F2] (Fin s → F2), ∀ v : Fin s → F2, L (B v) = v := by
  obtain ⟨V', hcompl⟩ := Submodule.exists_isCompl (LinearMap.range B)
  let π : (Fin k → F2) →ₗ[F2] LinearMap.range B := Submodule.linearProjOfIsCompl (LinearMap.range B) V' hcompl
  let e : (Fin s → F2) ≃ₗ[F2] LinearMap.range B := LinearEquiv.ofInjective B hB
  refine ⟨e.symm.toLinearMap.comp π, fun v => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hmem : B v ∈ LinearMap.range B := ⟨v, rfl⟩
  have hpi : π (B v) = ⟨B v, hmem⟩ := Submodule.linearProjOfIsCompl_apply_left hcompl ⟨B v, hmem⟩
  rw [hpi]
  have hev : e v = ⟨B v, hmem⟩ := rfl
  rw [← hev, LinearEquiv.symm_apply_apply]

lemma linear_coord_dot {k : ℕ} (ℓ : (Fin k → F2) →ₗ[F2] F2) :
    ∃ r : Fin k → F2, ∀ y : Fin k → F2, ℓ y = dotProduct r y := by
  refine ⟨fun j => ℓ (Pi.single j 1), fun y => ?_⟩
  conv_lhs => rw [vec_eq_sum_single y, map_sum]
  simp only [dotProduct, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

private lemma appendAffineFamily (n l : ℕ) (gs : List Gate)
    (hl : legalGates n gs) (c : Fin l → Fin n → F2) (b : Fin l → F2) :
    ∃ (ext : List Gate) (tap : Fin l → ℕ),
      legalGates n (gs ++ ext) ∧ costGates (gs ++ ext) = costGates gs ∧
      (∀ j, tap j < n + (gs ++ ext).length) ∧
      ∀ x j, (wiresOf (gs ++ ext) (bitsOf n x)).getD (tap j) false =
        decide (dotProduct (c j) x + b j = 1) := by
  induction l with
  | zero =>
      exact ⟨[], Fin.elim0, by simpa, by simp, fun j => j.elim0, fun _ j => j.elim0⟩
  | succ l ih =>
      obtain ⟨ext, tap, hl₀, hc₀, ht₀, hs₀⟩ :=
        ih (fun j => c j.castSucc) (fun j => b j.castSucc)
      let res := appendAffine n (gs ++ ext) (c (Fin.last l)) (b (Fin.last l))
      obtain ⟨new, hnew, hl₁, hc₁, ht₁, hs₁⟩ :=
        appendAffine_spec n (gs ++ ext) (c (Fin.last l)) (b (Fin.last l)) hl₀
      change res.1 = (gs ++ ext) ++ new at hnew
      change legalGates n res.1 at hl₁
      change costGates res.1 = costGates (gs ++ ext) at hc₁
      change res.2 < n + res.1.length at ht₁
      refine ⟨ext ++ new, Fin.lastCases res.2 tap, ?_, ?_, ?_, ?_⟩
      · simpa only [hnew, List.append_assoc] using hl₁
      · simpa only [hnew, List.append_assoc] using hc₁.trans hc₀
      · intro j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa only [Fin.lastCases_last, hnew, List.append_assoc] using ht₁
        · simp only [Fin.lastCases_castSucc, List.length_append]
          have := ht₀ i
          simp only [List.length_append] at this
          omega
      · intro x j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · have hs : (wiresOf res.1 (bitsOf n x)).getD res.2 false =
              decide (dotProduct (c (Fin.last l)) x + b (Fin.last l) = 1) := hs₁ x
          simpa only [Fin.lastCases_last, hnew, List.append_assoc] using hs
        · simp only [Fin.lastCases_castSucc]
          rw [← List.append_assoc, wiresOf_append_getD_lt]
          · exact hs₀ x i
          · simpa only [bitsOf_len] using ht₀ i

private def relabelWire {n : ℕ} (offset : ℕ) (tap : Fin n → ℕ) (j : ℕ) : ℕ :=
  if hj : j < n then tap ⟨j, hj⟩ else offset + (j - n)

private def relabelGate (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

private lemma appendRelabelled {n width : ℕ} (pre gs : List Gate) (tap : Fin n → ℕ)
    (hpre : legalGates width pre) (hgs : legalGates n gs)
    (htap : ∀ j, tap j < width + pre.length) :
    let ren := relabelWire (width + pre.length) tap
    let all := pre ++ gs.map (relabelGate ren)
    legalGates width all ∧ costGates all = costGates pre + costGates gs ∧
    ∀ (x : List Bool) (hx : x.length = width) (v : Fin n → F2),
      (∀ j, (wiresOf pre x).getD (tap j) false = decide (v j = 1)) →
      ∀ j < n + gs.length,
        (wiresOf all x).getD (ren j) false = (wiresOf gs (bitsOf n v)).getD j false := by
  let ren := relabelWire (width + pre.length) tap
  have hren {j q : ℕ} (hj : j < n + q) : ren j < width + pre.length + q := by
    by_cases hlt : j < n
    · simpa [ren, relabelWire, hlt] using
        (lt_of_lt_of_le (htap ⟨j, hlt⟩) (Nat.le_add_right _ q))
    · simp only [ren, relabelWire, hlt, ↓reduceDIte]
      omega
  change legalGates width (pre ++ gs.map (relabelGate ren)) ∧
    costGates (pre ++ gs.map (relabelGate ren)) = costGates pre + costGates gs ∧ _
  induction gs using List.reverseRecOn with
  | nil =>
      refine ⟨by simpa, by simp [costGates], ?_⟩
      intro x _ v hv j hj
      have hj' : j < n := by simpa using hj
      simp only [List.map_nil, List.append_nil, wiresOf, Circuit.wires, List.foldl_nil]
      change (wiresOf pre x).getD (ren j) false = (bitsOf n v).getD j false
      rw [bitsOf_getD n v ⟨j, hj'⟩]
      simpa only [ren, relabelWire, hj', ↓reduceDIte] using hv ⟨j, hj'⟩
  | append_singleton gs g ih =>
      let all := pre ++ gs.map (relabelGate ren)
      have hnext : pre ++ (gs ++ [g]).map (relabelGate ren) =
          all ++ [relabelGate ren g] := by simp [all, List.append_assoc]
      have hg := legalGates_prefix hgs
      obtain ⟨hleg, hcost, hsem⟩ := ih hg.1
      have hlen : all.length = pre.length + gs.length := by simp [all]
      rw [hnext]
      have hop : (relabelGate ren g).op = g.op := rfl
      have hin : (relabelGate ren g).inputs.length = g.inputs.length := by simp [relabelGate]
      refine ⟨legalGates_snoc hleg ?_ (by simpa only [hin, hop] using hg.2.2), ?_, ?_⟩
      · intro w hw
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp
          (show w ∈ g.inputs.map ren from hw)
        rw [hlen, ← Nat.add_assoc]
        exact hren (hg.2.1 j hj)
      · have hcoin : costGates [relabelGate ren g] = costGates [g] := by
          simp [costGates, hop, hin]
        rw [costGates_append, costGates_append gs, hcoin, hcost, Nat.add_assoc]
      · intro x hx v hv j hj
        by_cases hlt : j < n + gs.length
        · rw [wiresOf_append_getD_lt all, wiresOf_append_getD_lt gs]
          · exact hsem x hx v hv j hlt
          · simpa only [bitsOf_len] using hlt
          · rw [hx, hlen, ← Nat.add_assoc]
            exact hren hlt
        · have heq : j = n + gs.length := by simpa using
            (show j = n + gs.length from by
              simp only [List.length_append, List.length_singleton] at hj
              omega)
          subst j
          have hren' : ren (n + gs.length) = width + all.length := by
            simp only [ren, relabelWire, hlen]
            split <;> omega
          change (wiresOf (all ++ [relabelGate ren g]) x).getD (ren (n + gs.length)) false = _

          rw [hren', wiresOf_snoc_last_eq all _ x hx,
            wiresOf_snoc_last_eq gs g _ (bitsOf_len n v)]
          change g.op.eval (List.map (fun i => (wiresOf all x).getD i false)
              (g.inputs.map ren)) =
            g.op.eval (List.map (fun i => (wiresOf gs (bitsOf n v)).getD i false) g.inputs)
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact hsem x hx v hv i (hg.2.1 i hi)

private lemma appendRelabelledCircuit {n width : ℕ} (pre : List Gate) (C : Circuit)
    (tap : Fin n → ℕ) (hpre : legalGates width pre) (hC : legalGates n C.gates)
    (htap : ∀ j, tap j < width + pre.length) :
    ∃ (T : Circuit) (idx : ℕ → ℕ),
      legalGates width T.gates ∧ costGates T.gates ≤ costGates pre + costGates C.gates ∧
      T.output < width + T.gates.length ∧
      (∀ j < n + C.gates.length, idx j < width + T.gates.length) ∧
      ∀ (x : List Bool) (hx : x.length = width) (v : Fin n → F2),
        (∀ j, (wiresOf pre x).getD (tap j) false = decide (v j = 1)) →
        T.eval x = C.eval (bitsOf n v) ∧
        ∀ j < n + C.gates.length,
          (T.wires x).getD (idx j) false = (C.wires (bitsOf n v)).getD j false := by
  let idx := relabelWire (width + pre.length) tap
  let all := pre ++ C.gates.map (relabelGate idx)
  obtain ⟨hl, hc, hs⟩ := appendRelabelled pre C.gates tap hpre hC htap
  have hidx (j : ℕ) (hj : j < n + C.gates.length) : idx j < width + all.length := by
    have hlen : all.length = pre.length + C.gates.length := by simp [all]
    rw [hlen]
    by_cases hlt : j < n
    · simp only [idx, relabelWire, hlt, ↓reduceDIte]
      have := htap ⟨j, hlt⟩
      omega
    · simp only [idx, relabelWire, hlt, ↓reduceDIte]
      omega
  by_cases ho : C.output < n + C.gates.length
  · exact ⟨⟨all, idx C.output⟩, idx, hl, hc.le, hidx _ ho, hidx,
      fun x hx v hv => ⟨hs x hx v hv _ ho, hs x hx v hv⟩⟩
  · let last : Gate := ⟨.or, []⟩
    let out := width + all.length
    refine ⟨⟨all ++ [last], out⟩, idx, legalGates_snoc hl (by simp [last])
      ⟨by simp [last], Or.inr (Or.inl rfl)⟩, ?_, by simp [out],
      fun j hj => ?_, ?_⟩
    · rw [costGates_snoc_zero all last (by simp [last])]
      exact hc.le
    · exact (hidx j hj).trans_le (by simp)
    · intro x hx v hv
      constructor
      · change (wiresOf (all ++ [last]) x).getD out false =
          (wiresOf C.gates (bitsOf n v)).getD C.output false
        rw [wiresOf_snoc_last_eq all last x hx, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none]
        · rfl
        · rw [wiresOf_len, bitsOf_len]
          exact le_of_not_gt ho
      · intro j hj
        change (wiresOf (all ++ [last]) x).getD (idx j) false = _
        rw [wiresOf_append_getD_lt all _ x (by rw [hx]; exact hidx _ hj)]
        exact hs x hx v hv j hj

private lemma appendAndFamily (n t : ℕ) (pre : List Gate) (hpre : legalGates n pre)
    (left right : Fin t → ℕ) (hleft : ∀ i, left i < n + pre.length)
    (hright : ∀ i, right i < n + pre.length) :
    ∃ (ext : List Gate) (tap : Fin t → ℕ),
      legalGates n (pre ++ ext) ∧ costGates (pre ++ ext) = costGates pre + t ∧
      (∀ j, tap j < n + (pre ++ ext).length) ∧
      ∀ x : List Bool, x.length = n → ∀ j,
        (wiresOf (pre ++ ext) x).getD (tap j) false =
          ((wiresOf pre x).getD (left j) false && (wiresOf pre x).getD (right j) false) := by
  induction t with
  | zero =>
      exact ⟨[], Fin.elim0, by simpa, by simp, fun j => j.elim0, fun _ _ j => j.elim0⟩
  | succ t ih =>
      obtain ⟨ext, tap, hl, hc, ht, hs⟩ :=
        ih (fun j => left j.castSucc) (fun j => right j.castSucc)
          (fun j => hleft j.castSucc) (fun j => hright j.castSucc)
      let last : Gate := ⟨.and, [left (Fin.last t), right (Fin.last t)]⟩
      let out := n + (pre ++ ext).length
      have hback {w : ℕ} (hw : w < n + pre.length) : w < n + (pre ++ ext).length := by
        simp only [List.length_append]; omega
      have hleg : legalGates n ((pre ++ ext) ++ [last]) :=
        legalGates_snoc hl (by
          intro w hw
          simp only [last, List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl
          · exact hback (hleft _)
          · exact hback (hright _)) (by simp [last])
      refine ⟨ext ++ [last], Fin.lastCases out tap, ?_, ?_, ?_, ?_⟩
      · simpa only [List.append_assoc] using hleg
      · rw [← List.append_assoc, costGates_snoc_one _ _ (by simp [last]), hc, Nat.add_assoc]
      · intro j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp [out, List.length_append]
        · simp only [Fin.lastCases_castSucc, List.length_append]
          have hi := ht i
          simp only [List.length_append] at hi
          omega
      · intro x hx j
        have hpersist {w : ℕ} (hw : w < n + pre.length) :
            (wiresOf (pre ++ ext) x).getD w false = (wiresOf pre x).getD w false :=
          wiresOf_append_getD_lt _ _ _ (by simpa only [hx] using hw)
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp only [Fin.lastCases_last, ← List.append_assoc, out]
          rw [wiresOf_snoc_last_eq _ _ _ hx]
          simp only [last, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, hpersist (hleft _), hpersist (hright _)]
        · simp only [Fin.lastCases_castSucc, ← List.append_assoc]
          rw [wiresOf_append_getD_lt _ _ _ (by rw [hx]; exact ht i)]
          exact hs x hx i

private lemma cubicDotProduct {n t : ℕ} (a x : Fin n → F2) (b y : Fin t → F2) :
    dotProduct (Fin.addCases a b) (Fin.addCases x y) = dotProduct a x + dotProduct b y := by
  simp [dotProduct, Fin.sum_univ_add]

private lemma build_cubic_circuit (n s t : ℕ)
    (c₀ : Fin n → F2) (d₀ : Fin t → F2) (b₀ : F2)
    (cL cR : Fin s → Fin n → F2) (dR : Fin s → Fin t → F2) (bL bR : Fin s → F2)
    (cU cV : Fin t → Fin n → F2) (bU bV : Fin t → F2) :
    ∃ C : Circuit, legalGates n C.gates ∧ costGates C.gates ≤ s + t ∧
      ∀ x : Fin n → F2,
        let aux : Fin t → F2 := fun j =>
          (dotProduct (cU j) x + bU j) * (dotProduct (cV j) x + bV j)
        C.eval (bitsOf n x) = decide (
          dotProduct c₀ x + dotProduct d₀ aux + b₀ +
            ∑ i : Fin s, (dotProduct (cL i) x + bL i) *
              (dotProduct (cR i) x + dotProduct (dR i) aux + bR i) = 1) := by
  have hnil : legalGates n [] := ⟨fun _ hj => by simp at hj, fun _ hh => by simp at hh⟩
  obtain ⟨pU, wU, hlU, hcU, htU, hsU⟩ := appendAffineFamily n t [] hnil cU bU
  simp only [List.nil_append] at hlU hcU htU hsU
  obtain ⟨pV, wV, hlV, hcV, htV, hsV⟩ := appendAffineFamily n t pU hlU cV bV
  have htU' (j : Fin t) : wU j < n + (pU ++ pV).length := by
    have := htU j
    simp only [List.length_append]; omega
  obtain ⟨ext, wA, hlA, hcA, htA, hsA⟩ :=
    appendAndFamily n t (pU ++ pV) hlV wU wV htU' htV
  let pre := (pU ++ pV) ++ ext
  let tap : Fin (n + t) → ℕ := Fin.addCases Fin.val wA
  have ht (i : Fin (n + t)) : tap i < n + pre.length := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [tap, Fin.addCases_left]
      exact j.isLt.trans_le (Nat.le_add_right _ _)
    · simpa only [tap, Fin.addCases_right] using htA j
  obtain ⟨outer, hl, hc, hs⟩ := build_sum_prods_circuit (n + t) s
    (Fin.addCases c₀ d₀) b₀ (fun i => Fin.addCases (cL i) (0 : Fin t → F2))
    (fun i => Fin.addCases (cR i) (dR i)) bL bR
  obtain ⟨C, _, hC, hcost, _, _, heval⟩ := appendRelabelledCircuit pre outer tap hlA hl ht
  refine ⟨C, hC, ?_, fun x => ?_⟩
  · have hz : costGates ([] : List Gate) = 0 := by simp [costGates]
    simpa only [pre, hcA, hcV, hcU, hz, zero_add, hc, Nat.add_comm t s] using hcost
  · let aux : Fin t → F2 := fun j =>
      (dotProduct (cU j) x + bU j) * (dotProduct (cV j) x + bV j)
    have hw (i : Fin (n + t)) :
        (wiresOf pre (bitsOf n x)).getD (tap i) false = decide ((Fin.addCases x aux i : F2) = 1) := by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [tap, Fin.addCases_left]
        rw [wiresOf_getD_lt pre _ (by rw [bitsOf_len]; exact j.isLt)]
        exact bitsOf_getD n x j
      · simp only [tap, Fin.addCases_right]
        rw [hsA _ (bitsOf_len n x) j,
          wiresOf_append_getD_lt pU pV _ (by rw [bitsOf_len]; exact htU j),
          hsU x j, hsV x j]
        exact (zmod2_mul_decide _ _).symm
    rw [(heval _ (bitsOf_len n x) _ hw).1, hs]
    simp only [cubicDotProduct, zero_dotProduct, add_zero, aux]

private abbrev Vec (n : ℕ) := Fin n → F2

private noncomputable def chi (v : F2) : ℝ :=
  (signBool (decide (v = 1)) : ℝ)

private def bitValue (b : Bool) : F2 := if b then 1 else 0

private lemma bitValue_xor (a b : Bool) : bitValue (Bool.xor a b) = bitValue a + bitValue b := by
  cases a <;> cases b <;> decide

private lemma chi_add (a b : F2) : chi (a + b) = chi a * chi b := by
  simp only [chi, zmod2_add_decide, signBool_xor, Int.cast_mul]

private lemma chi_le_one (a : F2) : chi a ≤ 1 := by
  unfold chi signBool
  split <;> norm_num

private lemma agree_chi (b : Bool) (v : F2) :
    (if b = decide (v = 1) then (1 : ℝ) else -1) = chi (bitValue b + v) := by
  have hb : decide (bitValue b = 1) = b := zmod2_bool_decide b
  simp only [chi, zmod2_add_decide, hb, signBool]
  cases b <;> cases decide (v = 1) <;> norm_num

private noncomputable def splitEquiv {n N : ℕ} (U : Fin N → Submodule F2 (Vec n))
    (pos : Fin N → Vec n) (hp : ∀ x, ∃! i, x - pos i ∈ U i) :
    (Σ i : Fin N, U i) ≃ Vec n := by
  classical
  let idx : Vec n → Fin N := fun x => (hp x).choose
  have hm (x : Vec n) : x - pos (idx x) ∈ U (idx x) := (hp x).choose_spec.1
  have hu (x : Vec n) (i : Fin N) : x - pos i ∈ U i → i = idx x :=
    (hp x).choose_spec.2 i
  refine ⟨fun p => pos p.1 + p.2.val,
    fun x => ⟨idx x, ⟨x - pos (idx x), hm x⟩⟩, ?_, ?_⟩
  · rintro ⟨i, ⟨u, hu₀⟩⟩
    have hm₀ : pos i + u - pos i ∈ U i := by simpa using hu₀
    have hi := (hu (pos i + u) i hm₀).symm
    dsimp only
    generalize hm (pos i + u) = hh
    revert hh
    generalize idx (pos i + u) = j at hi ⊢
    subst hi
    intro _
    congr 1
    exact Subtype.ext (by simp)
  · intro x
    change pos (idx x) + (x - pos (idx x)) = x
    abel

private noncomputable def avg {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ j, f j) / Fintype.card α

private lemma avg_le {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ)
    (t : ℝ) (ht : ∀ j, f j ≤ t) : avg f ≤ t := by
  have hpos : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hpos).2
  simpa [mul_comm] using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => ht j)

private lemma avgSplit {n N : ℕ} (U : Fin N → Submodule F2 (Vec n))
    (pos : Fin N → Vec n) (hp : ∀ x, ∃! i, x - pos i ∈ U i) (f : Vec n → ℝ) :
    avg f = ∑ i, ((Fintype.card (U i) : ℝ) / 2^n) *
      avg (fun u : U i => f (pos i + u.val)) := by
  classical
  have htotal : (Fintype.card (Vec n) : ℝ) = 2^n := by simp [Vec, ZMod.card]
  unfold avg
  rw [htotal, ← Equiv.sum_comp (splitEquiv U pos hp), Fintype.sum_sigma, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hpos : (Fintype.card (U i) : ℝ) ≠ 0 := by positivity
  change (∑ u : U i, f (pos i + u.val)) / 2^n = _
  field_simp

private lemma sliceWeights {n N : ℕ} (U : Fin N → Submodule F2 (Vec n))
    (pos : Fin N → Vec n) (hp : ∀ x, ∃! i, x - pos i ∈ U i) :
    (∑ i, (Fintype.card (U i) : ℝ) / 2^n) = 1 := by
  have hcard := Fintype.card_congr (splitEquiv U pos hp)
  rw [Fintype.card_sigma] at hcard
  have hv : Fintype.card (Vec n) = 2^n := by simp [Vec, ZMod.card]
  rw [← Finset.sum_div, ← Nat.cast_sum, hcard, hv]
  push_cast
  exact div_self (by positivity)

private lemma chiAvgOrtho {n : ℕ} (U : Submodule F2 (Vec n)) (v : Vec n) :
    avg (fun u : U => chi (dotProduct v u.val)) =
      if v ∈ orthoComp U then 1 else 0 := by
  classical
  have hc := congrArg (Int.cast : ℤ → ℝ) (sum_sign_dot_submodule U v)
  unfold chi avg
  rw [← Int.cast_sum, hc, card_submodule_zmod2]
  split_ifs <;> push_cast <;> simp

private lemma avgChiShift {α : Type*} [Fintype α] (f : α → F2) (a : F2) :
    avg (fun j => chi (a + f j)) = chi a * avg (fun j => chi (f j)) := by
  simp_rw [chi_add, avg, ← Finset.mul_sum, mul_div_assoc]

private lemma splitProfile {n N : ℕ} (C : Circuit) (U : Fin N → Submodule F2 (Vec n))
    (a : Fin N → Vec n) (D : Fin N → Circuit)
    (pos : Fin N → Vec n → Vec n)
    (hpart : ∀ y x : Vec n, ∃! i, x - pos i y ∈ U i)
    (heval : ∀ i y u, u ∈ U i →
      C.eval (bitsOf n (pos i y + u) ++ bitsOf n y) =
        Bool.xor ((D i).eval (bitsOf n y)) (decide (dotProduct (a i) u = 1))) (y : Vec n) (v : F2) :
    avg (fun x : Vec n => if C.eval (bitsOf n x ++ bitsOf n y) = decide (dotProduct x y + v = 1)
      then (1 : ℝ) else -1) =
      ∑ i, ((Fintype.card (U i) : ℝ) / 2^n) *
        (if y - a i ∈ orthoComp (U i) then
          chi (bitValue ((D i).eval (bitsOf n y)) + dotProduct (pos i y) y + v)
        else 0) := by
  classical
  rw [avgSplit U (fun i => pos i y) (hpart y)]
  refine Finset.sum_congr rfl fun i _ => congrArg (fun t => ((Fintype.card (U i) : ℝ) / 2^n) * t) ?_
  have hterm (u : U i) :
      (if C.eval (bitsOf n (pos i y + u.val) ++ bitsOf n y) =
        decide (dotProduct (pos i y + u.val) y + v = 1) then (1 : ℝ) else -1) =
      chi ((bitValue ((D i).eval (bitsOf n y)) + dotProduct (pos i y) y + v) +
        dotProduct (y - a i) u.val) := by
    rw [agree_chi, heval i y u.val u.property, bitValue_xor]
    change chi ((bitValue ((D i).eval (bitsOf n y)) +
      (if decide (dotProduct (a i) u.val = 1) then (1 : F2) else 0)) +
      (dotProduct (pos i y + u.val) y + v)) = _
    rw [zmod2_decide_bool, zmod2_vec_sub_eq_add, add_dotProduct, add_dotProduct,
      dotProduct_comm u.val y]
    congr 1
    ring
  simp_rw [hterm, avgChiShift, chiAvgOrtho]
  split_ifs <;> simp

private abbrev Data (m r : ℕ) := Vec m × (Vec m × Vec r)

private noncomputable def address (m r : ℕ) : ((Fin m ⊕ Fin m) ⊕ Fin r) ≃ Fin (2*m+r) :=
  Fintype.equivFinOfCardEq (by simp [two_mul])

private noncomputable def pack (m r : ℕ) : Data m r ≃ₗ[F2] Vec (2*m+r) where
  toFun w i := Sum.elim (Sum.elim w.1 w.2.1) w.2.2 ((address m r).symm i)
  invFun v := (fun i => v (address m r (.inl (.inl i))),
    fun i => v (address m r (.inl (.inr i))), fun i => v (address m r (.inr i)))
  left_inv := by intro w; simp
  right_inv := by
    intro v; funext i
    obtain ⟨j,rfl⟩ := (address m r).surjective i
    cases j with
    | inl j => cases j <;> simp
    | inr j => simp
  map_add' w v := by
    funext i; obtain ⟨j,rfl⟩ := (address m r).surjective i
    cases j with
    | inl j => cases j <;> simp
    | inr j => simp
  map_smul' a v := by
    funext i; obtain ⟨j,rfl⟩ := (address m r).surjective i
    cases j with
    | inl j => cases j <;> simp
    | inr j => simp

private def appendVec {d k : ℕ} (u : Vec d) (s : Vec k) : Vec (d + k) :=
  Fin.addCases u s

private lemma bitsOf_appendVec {d k : ℕ} (u : Vec d) (s : Vec k) :
    bitsOf d u ++ bitsOf k s = bitsOf (d+k) (appendVec u s) := by
  apply List.ext_getElem
  · simp [bitsOf_len]
  · intro i h₁ h₂
    have h₂' : i < d+k := by simpa [bitsOf_len] using h₂
    by_cases hi : i < d
    · rw [List.getElem_append_left (by simpa [bitsOf_len] using hi)]
      simp only [bitsOf, List.getElem_ofFn]
      change decide (u ⟨i, hi⟩ = 1) =
        decide (appendVec u s (Fin.castAdd k ⟨i, hi⟩) = 1)
      rw [appendVec, Fin.addCases_left]
    · rw [List.getElem_append_right (by simpa [bitsOf_len] using le_of_not_gt hi)]
      simp only [bitsOf, List.length_ofFn, List.getElem_ofFn]
      have hk : i - d < k := by omega
      have he : (⟨i, h₂'⟩ : Fin (d+k)) = (⟨i-d, hk⟩ : Fin k).natAdd d := by
        apply Fin.ext
        simp
        omega
      change decide (s ⟨i-d, hk⟩ = 1) = decide (appendVec u s ⟨i, h₂'⟩ = 1)
      rw [he]
      rw [appendVec, Fin.addCases_right]

private def headLinear (d k : ℕ) : Vec (d+k) →ₗ[F2] Vec d where
  toFun x j := x (j.castAdd k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def tailLinear (d k : ℕ) : Vec (d+k) →ₗ[F2] Vec k where
  toFun x j := x (j.natAdd d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma pullbackCircuit {n width : ℕ} (L : Vec width →ₗ[F2] Vec n) (C : Circuit)
    (hC : legalGates n C.gates) :
    ∃ (T : Circuit) (idx : ℕ → ℕ),
      legalGates width T.gates ∧ costGates T.gates ≤ costGates C.gates ∧
      (∀ j < n + C.gates.length, idx j < width + T.gates.length) ∧
      ∀ x : Vec width, T.eval (bitsOf width x) = C.eval (bitsOf n (L x)) ∧
        ∀ j < n + C.gates.length,
          (T.wires (bitsOf width x)).getD (idx j) false =
            (C.wires (bitsOf n (L x))).getD j false := by
  have hc j := linear_coord_dot ((LinearMap.proj j).comp L)
  choose rows hrows using hc
  have hnil : legalGates width [] := ⟨fun _ hj => by simp at hj, fun _ hh => by simp at hh⟩
  obtain ⟨pre, tap, hp, hcost, ht, hv⟩ :=
    appendAffineFamily width n [] hnil rows (fun _ => 0)
  have hz : costGates pre = 0 := by
    have h0 : costGates ([] : List Gate) = 0 := by simp [costGates]
    simpa only [List.nil_append, h0] using hcost
  simp only [List.nil_append] at hp ht hv
  obtain ⟨T, idx, hl, hc, _, hi, hs⟩ := appendRelabelledCircuit pre C tap hp hC ht
  refine ⟨T, idx, hl, by simpa only [hz, zero_add] using hc, hi, fun x => ?_⟩
  apply hs _ (bitsOf_len width x) (L x)
  intro j
  rw [hv x j, add_zero]
  exact congrArg (fun a : F2 => decide (a = 1)) ((hrows j x).symm)

private lemma payloadSplit {k m r n : ℕ}
    (e : Vec n ≃ₗ[F2] Vec k × Data m r) (D : Circuit) (hD : legalGates n D.gates) :
    ∃ (N : ℕ) (U : Fin N → Submodule F2 (Vec (2*m+r)))
      (pos : Fin N → Vec k → Vec (2*m+r)) (a : Fin N → ℕ → Vec k → F2)
      (slope : Fin N → ℕ → Vec (2*m+r)),
      (∀ i, 2*m+r ≤ Module.finrank F2 (U i) + costGates D.gates) ∧
      (∀ s v, ∃! i, v - pos i s ∈ U i) ∧
      ∀ i s (v : U i) j, j < n + D.gates.length →
        bitValue ((D.wires (bitsOf n (e.symm (s, (pack m r).symm (pos i s + v.val))))).getD j false) =
          a i j s + dotProduct (slope i j) v.val := by
  let d := 2*m+r
  let L : Vec (d+k) →ₗ[F2] Vec n := e.symm.toLinearMap.comp
    ((tailLinear d k).prod ((pack m r).symm.toLinearMap.comp (headLinear d k)))
  have hL (u : Vec d) (s : Vec k) : L (appendVec u s) = e.symm (s, (pack m r).symm u) := by
    change e.symm ((fun j => Fin.addCases u s (j.natAdd d)),
      (pack m r).symm (fun j => Fin.addCases u s (j.castAdd k))) = _
    simp
  obtain ⟨T, idx, hT, hc, hi, hs⟩ := pullbackCircuit L D hD
  obtain ⟨B, _, hb, hp⟩ := build_branch_list d k T.gates hT
  refine ⟨B.length, fun i => (B.get i).U, fun i => (B.get i).pos,
    fun i j s => bitValue ((wiresOf (B.get i).gates (bitsOf k s)).getD ((B.get i).off (idx j)) false),
    fun i j => (B.get i).slope (idx j), ?_, hp, ?_⟩
  · intro i
    have hm := hb _ (List.get_mem B i)
    have hr : Module.finrank F2 (B.get i).U + (B.get i).r = 2*m+r := hm.1
    have hc' : costGates (B.get i).gates + (B.get i).r ≤ costGates T.gates := hm.2.2.1
    change 2*m+r ≤ Module.finrank F2 (B.get i).U + costGates D.gates
    rw [← hr]
    exact Nat.add_le_add_left ((Nat.le_add_left _ _).trans (hc'.trans hc)) _
  · intro i s v j hj
    have hw := (hs (appendVec ((B.get i).pos s + v.val) s)).2 j hj
    rw [hL, ← bitsOf_appendVec] at hw
    change (wiresOf T.gates (bitsOf d ((B.get i).pos s + v.val) ++ bitsOf k s)).getD (idx j) false =
      (D.wires (bitsOf n (e.symm (s, (pack m r).symm ((B.get i).pos s + v.val))))).getD j false at hw
    rw [← hw, (hb _ (List.get_mem B i)).2.2.2.2.2 _ (hi j hj) s v.val v.property, bitValue_xor]
    congr 1
    exact zmod2_decide_bool _


noncomputable section SelectorTools
open Module
open scoped Affine


variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq V]

private theorem selector_bit (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx : x.val < 2 := x.val_lt
  rcases show x.val = 0 ∨ x.val = 1 by omega with h | h
  · exact Or.inl (ZMod.val_injective 2 (h.trans ZMod.val_zero.symm))
  · exact Or.inr (ZMod.val_injective 2 (h.trans (ZMod.val_one 2).symm))

omit [Module (ZMod 2) V] [DecidableEq V] in
private theorem selector_augmented_sum {E : Finset V} (heven : Even E.card)
    (hsum : (∑ x ∈ E, x) = 0) : (∑ x ∈ E, ((1 : ZMod 2), x)) = 0 := by
  apply Prod.ext
  · simpa only [Prod.fst_sum, Prod.fst_zero, Finset.sum_const, nsmul_one] using
      ZMod.natCast_eq_zero_iff_even.mpr heven
  · simpa only [Prod.snd_sum, Prod.snd_zero] using hsum

/-- Every deletion removes the only nontrivial dependence of the augmented selectors. -/
private theorem selector_augmented_independent_erase {E : Finset V} {d : V} (hd : d ∈ E)
    (hminimal : ∀ I : Finset V, I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ x ∈ I, x) ≠ 0) :
    LinearIndependent (ZMod 2) (fun x : E.erase d => ((1 : ZMod 2), (x : V))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro w hzero i
  rcases selector_bit (w i) with hi | hi
  · exact hi
  let T : Finset (E.erase d) := Finset.univ.filter fun j => w j = 1
  let I : Finset V := T.map (Function.Embedding.subtype _)
  have hT : (∑ j ∈ T, ((1 : ZMod 2), (j : V))) = 0 := by
    change (∑ j ∈ Finset.univ.filter (fun j => w j = 1), ((1 : ZMod 2), (j : V))) = 0
    rw [Finset.sum_filter]
    refine Eq.trans ?_ hzero
    apply Finset.sum_congr rfl
    intro j _
    rcases selector_bit (w j) with hj | hj <;> simp [hj]
  have hI : (∑ x ∈ I, ((1 : ZMod 2), x)) = 0 := by
    change (∑ x ∈ T.map (Function.Embedding.subtype _), ((1 : ZMod 2), x)) = 0
    rw [Finset.sum_map]
    exact hT
  have hIsub : I ⊆ E.erase d := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨j, _, rfl⟩
    exact j.property
  have hIne : I ≠ E := by
    intro h
    exact Finset.notMem_erase d E (hIsub (h.symm ▸ hd))
  have hInonempty : I.Nonempty :=
    ⟨i, Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩⟩
  have hIeven : Even I.card := ZMod.natCast_eq_zero_iff_even.mp (by
    simpa only [Prod.fst_sum, Prod.fst_zero, Finset.sum_const, nsmul_one] using
      congrArg Prod.fst hI)
  have hIsum : (∑ x ∈ I, x) = 0 := by
    simpa only [Prod.snd_sum, Prod.snd_zero] using congrArg Prod.snd hI
  exact (hminimal I (hIsub.trans (Finset.erase_subset _ _)) hInonempty hIne hIeven hIsum).elim

private theorem selector_affineIndependent_erase {E : Finset V} {d : V} (hd : d ∈ E)
    (hminimal : ∀ I : Finset V, I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ x ∈ I, x) ≠ 0) :
    AffineIndependent (ZMod 2) (fun x : E.erase d => (x : V)) := by
  intro t w hw hvec i hi
  rw [t.weightedVSub_eq_linear_combination hw] at hvec
  have hzero : (∑ j ∈ t, w j • ((1 : ZMod 2), (j : V))) = 0 := by
    apply Prod.ext
    · simp only [Prod.fst_sum, Prod.fst_zero]
      change (∑ j ∈ t, w j * 1) = 0
      simpa only [mul_one] using hw
    · simp only [Prod.snd_sum, Prod.snd_zero]
      change (∑ j ∈ t, w j • (j : V)) = 0
      exact hvec
  have hi' := selector_augmented_independent_erase hd hminimal
  exact (linearIndependent_iff'.mp hi') t w hzero i hi

/-- The deleted selector is the affine combination with all remaining coefficients one. -/
private theorem selector_affineSpan_erase {E : Finset V} {d : V} (hd : d ∈ E)
    (heven : Even E.card) (hsum : (∑ x ∈ E, x) = 0) :
    affineSpan (ZMod 2) ((E.erase d : Finset V) : Set V) = affineSpan (ZMod 2) (E : Set V) := by
  have hcoeff : (∑ _x ∈ E.erase d, (1 : ZMod 2)) = 1 := by
    have h := E.sum_erase_add (fun _ => (1 : ZMod 2)) hd
    rw [show (∑ _x ∈ E, (1 : ZMod 2)) = 0 by
      simpa only [Finset.sum_const, nsmul_one] using ZMod.natCast_eq_zero_iff_even.mpr heven] at h
    simpa only [ZModModule.neg_eq_self] using eq_neg_of_add_eq_zero_left h
  have hrest : (∑ x ∈ E.erase d, x) = d := by
    have h := E.sum_erase_add id hd
    rw [show (∑ x ∈ E, id x) = 0 from hsum] at h
    simpa only [id_eq, ZModModule.neg_eq_self] using eq_neg_of_add_eq_zero_left h
  have hcomb := affineCombination_mem_affineSpan_image hcoeff
    (s' := ((E.erase d : Finset V) : Set V)) (fun _ hi hnot => (hnot hi).elim) (id : V → V)
  rw [Set.image_id, Finset.affineCombination_eq_linear_combination _ _ _ hcoeff] at hcomb
  simp only [one_smul, id_eq, hrest] at hcomb
  refine le_antisymm (affineSpan_mono (ZMod 2) (Finset.erase_subset d E))
    (affineSpan_le_of_subset_coe ?_)
  intro x hx
  change x ∈ affineSpan (ZMod 2) ((E.erase d : Finset V) : Set V)
  rcases eq_or_ne x d with rfl | hxd
  · exact hcomb
  · exact mem_affineSpan _ (Finset.mem_erase.mpr ⟨hxd, hx⟩)

private theorem selector_affine_finrank {E : Finset V} (hcard : 4 ≤ E.card)
    (heven : Even E.card) (hsum : (∑ x ∈ E, x) = 0)
    (hminimal : ∀ I : Finset V, I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ x ∈ I, x) ≠ 0) :
    Module.finrank (ZMod 2) (affineSpan (ZMod 2) (E : Set V)).direction = E.card - 2 := by
  obtain ⟨d, hd⟩ := Finset.card_pos.mp (show 0 < E.card by omega)
  have hne : (E.erase d).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hd]
    omega)
  have hi : AffineIndepOn (ZMod 2) id ((E.erase d : Finset V) : Set V) :=
    selector_affineIndependent_erase hd hminimal
  rw [← selector_affineSpan_erase hd heven hsum, direction_affineSpan,
    hi.finrank_vectorSpan (E.erase d).finite_toSet hne.to_set,
    Set.ncard_coe_finset, Finset.card_erase_of_mem hd]
  omega

/-- A prescribed scalar on the selector set extends precisely when its sum vanishes. -/
private theorem selector_affine_interpolation {E : Finset V} (hne : E.Nonempty)
    (heven : Even E.card) (hsum : (∑ x ∈ E, x) = 0)
    (hminimal : ∀ I : Finset V, I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ x ∈ I, x) ≠ 0) (h : V → ZMod 2) :
    (∃ f : V →ᵃ[ZMod 2] ZMod 2, ∀ x ∈ E, f x = h x) ↔ (∑ x ∈ E, h x) = 0 := by
  constructor
  · rintro ⟨f, hf⟩
    have hform (x : V) : f x = f.linear x + f 0 := by
      simpa only [vadd_eq_add, add_zero] using f.map_vadd 0 x
    calc
      (∑ x ∈ E, h x) = ∑ x ∈ E, (f.linear x + f 0) :=
        Finset.sum_congr rfl fun x hx => (hf x hx).symm.trans (hform x)
      _ = 0 := by
        rw [Finset.sum_add_distrib, ← map_sum, hsum, map_zero, zero_add, Finset.sum_const,
          nsmul_eq_mul, ZMod.natCast_eq_zero_iff_even.mpr heven, zero_mul]
  · intro hh
    obtain ⟨d, hd⟩ := hne
    let b := Basis.span (selector_augmented_independent_erase hd hminimal)
    let g := b.constr (ZMod 2) (fun i => h i)
    obtain ⟨L, hL⟩ := g.exists_extend
    have hi (i : E.erase d) : L (1, (i : V)) = h i := by
      have hb := LinearMap.congr_fun hL (b i)
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply, b, Basis.coe_span_apply, g,
        Basis.constr_basis] using hb
    have hall : (∑ x ∈ E, L (1, x)) = 0 := by
      rw [← map_sum, selector_augmented_sum heven hsum, map_zero]
    have hrest : (∑ x ∈ E.erase d, L (1, x)) = ∑ x ∈ E.erase d, h x :=
      Finset.sum_congr rfl fun x hx => hi ⟨x, hx⟩
    have hdelL := E.sum_erase_add (fun x => L (1, x)) hd
    have hdelh := E.sum_erase_add h hd
    rw [hall, hrest] at hdelL
    rw [hh] at hdelh
    have hdel : L (1, d) = h d := add_left_cancel (hdelL.trans hdelh.symm)
    let f : V →ᵃ[ZMod 2] ZMod 2 :=
      { toFun := fun x => L (1, x)
        linear := L.comp (LinearMap.inr (ZMod 2) (ZMod 2) V)
        map_vadd' := fun p v => by
          change L (1, v + p) = L (0, v) + L (1, p)
          rw [← map_add]
          simp }
    refine ⟨f, fun x hx => ?_⟩
    change L (1, x) = h x
    by_cases hxd : x = d
    · simpa only [hxd] using hdel
    · exact hi ⟨x, Finset.mem_erase.mpr ⟨hxd, hx⟩⟩

private theorem selector_affine_indicator {E I : Finset V} (hne : E.Nonempty)
    (heven : Even E.card) (hsum : (∑ x ∈ E, x) = 0)
    (hminimal : ∀ J : Finset V, J ⊆ E → J.Nonempty → J ≠ E → Even J.card →
      (∑ x ∈ J, x) ≠ 0) (hI : I ⊆ E) :
    (∃ f : V →ᵃ[ZMod 2] ZMod 2, ∀ x ∈ E, f x = if x ∈ I then 1 else 0) ↔ Even I.card := by
  have hfilter : E.filter (· ∈ I) = I := by
    ext x
    exact ⟨fun hx => (Finset.mem_filter.mp hx).2, fun hx => Finset.mem_filter.mpr ⟨hI hx, hx⟩⟩
  rw [selector_affine_interpolation hne heven hsum hminimal,
    Finset.sum_boole, hfilter, ZMod.natCast_eq_zero_iff_even]

private theorem selector_affine_pair {E : Finset V} {s t : V} (hs : s ∈ E) (ht : t ∈ E)
    (hst : s ≠ t) (heven : Even E.card) (hsum : (∑ x ∈ E, x) = 0)
    (hminimal : ∀ I : Finset V, I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ x ∈ I, x) ≠ 0) :
    ∃ f : V →ᵃ[ZMod 2] ZMod 2, ∀ x ∈ E, f x = if x = s ∨ x = t then 1 else 0 := by
  have hpair : ({s, t} : Finset V) ⊆ E :=
    Finset.insert_subset_iff.mpr ⟨hs, Finset.singleton_subset_iff.mpr ht⟩
  have htwo : Even ({s, t} : Finset V).card := by simp [hst]
  obtain ⟨f, hf⟩ :=
    (selector_affine_indicator ⟨s, hs⟩ heven hsum hminimal hpair).mpr htwo
  exact ⟨f, by simpa only [Finset.mem_insert, Finset.mem_singleton] using hf⟩

private theorem selector_quadratic_singleton {E : Finset V} {s : V} (hs : s ∈ E)
    (hcard : 4 ≤ E.card) (heven : Even E.card) (hsum : (∑ x ∈ E, x) = 0)
    (hminimal : ∀ I : Finset V, I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ x ∈ I, x) ≠ 0) :
    ∃ f g : V →ᵃ[ZMod 2] ZMod 2, ∀ x ∈ E, f x * g x = if x = s then 1 else 0 := by
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (E.erase s).card by
    rw [Finset.card_erase_of_mem hs]; omega)
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < ((E.erase s).erase u).card by
    rw [Finset.card_erase_of_mem hu, Finset.card_erase_of_mem hs]; omega)
  rcases Finset.mem_erase.mp hu with ⟨hus, huE⟩
  rcases Finset.mem_erase.mp hv with ⟨hvu, hv⟩
  rcases Finset.mem_erase.mp hv with ⟨hvs, hvE⟩
  obtain ⟨f, hf⟩ := selector_affine_pair hs huE hus.symm heven hsum hminimal
  obtain ⟨g, hg⟩ := selector_affine_pair hs hvE hvs.symm heven hsum hminimal
  refine ⟨f, g, fun x hx => ?_⟩
  rw [hf x hx, hg x hx]
  by_cases hxs : x = s
  · simp [hxs]
  · by_cases hxu : x = u
    · simp [hxu, hvu.symm]
    · simp [hxs, hxu]

/-- Selector phases are a sum of products of affine scalars, with scalar coefficients. -/
private theorem selector_quadratic_interpolation {E : Finset V} (hcard : 4 ≤ E.card)
    (heven : Even E.card) (hsum : (∑ x ∈ E, x) = 0)
    (hminimal : ∀ I : Finset V, I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ x ∈ I, x) ≠ 0) (h : V → ZMod 2) :
    ∃ f g : E → (V →ᵃ[ZMod 2] ZMod 2),
      ∀ x ∈ E, (∑ s : E, h s * (f s x * g s x)) = h x := by
  choose f g hfg using fun s : E => selector_quadratic_singleton s.property hcard heven hsum hminimal
  refine ⟨f, g, fun x hx => ?_⟩
  rw [Finset.sum_eq_single (⟨x, hx⟩ : E)]
  · simp [hfg _ x hx]
  · intro s _ hs
    have hxs : x ≠ (s : V) := fun heq => hs (Subtype.ext heq.symm)
    simp [hfg s x hx, hxs]
  · simp

end SelectorTools


open scoped BigOperators

private abbrev RRField := ZMod 2
private abbrev RRVec (ι : Type*) := ι → RRField × RRField

private def rrCross (x y : RRField × RRField) : RRField :=
  x.1 * y.2 + x.2 * y.1

private def rrStandard (ι : Type*) [Fintype ι] :
    LinearMap.BilinForm RRField (RRVec ι) :=
  LinearMap.mk₂ RRField (fun x y => ∑ i, rrCross (x i) (y i))
    (by
      intro x x' y
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold rrCross
      change ((x i).1 + (x' i).1) * (y i).2 +
        ((x i).2 + (x' i).2) * (y i).1 = _
      ring)
    (by
      intro c x y
      simp only [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold rrCross
      change (c * (x i).1) * (y i).2 + (c * (x i).2) * (y i).1 = _
      ring)
    (by
      intro x y y'
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold rrCross
      change (x i).1 * ((y i).2 + (y' i).2) + (x i).2 * ((y i).1 + (y' i).1) = _
      ring)
    (by
      intro c x y
      simp only [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold rrCross
      change (x i).1 * (c * (y i).2) + (x i).2 * (c * (y i).1) = _
      ring)

private lemma rrVec_dim (ι : Type*) [Fintype ι] :
    Module.finrank RRField (RRVec ι) = 2 * Fintype.card ι := by
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_prod, Nat.mul_comm]

private lemma rrStandard_nondegenerate (ι : Type*) [Fintype ι] :
    (rrStandard ι).Nondegenerate := by
  classical
  have hleft : ∀ x : RRVec ι, (∀ y, rrStandard ι x y = 0) → x = 0 := by
    intro x hx
    funext i
    apply Prod.ext
    · let e : RRVec ι := Pi.single i (0, 1)
      have h := hx e
      change (∑ j, rrCross (x j) (e j)) = 0 at h
      rw [Finset.sum_eq_single i] at h
      · simpa [e, rrCross] using h
      · intro j _ hji
        have he : e j = 0 := Pi.single_eq_of_ne hji _
        simp [he, rrCross]
      · simp
    · let e : RRVec ι := Pi.single i (1, 0)
      have h := hx e
      change (∑ j, rrCross (x j) (e j)) = 0 at h
      rw [Finset.sum_eq_single i] at h
      · simpa [e, rrCross] using h
      · intro j _ hji
        have he : e j = 0 := Pi.single_eq_of_ne hji _
        simp [he, rrCross]
      · simp
  refine ⟨hleft, fun y hy => hleft y fun x => ?_⟩
  calc
    rrStandard ι y x = rrStandard ι x y := by
      change (∑ i, rrCross (y i) (x i)) = ∑ i, rrCross (x i) (y i)
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold rrCross
      ring
    _ = 0 := hy x

private lemma rrStandard_iso_dim {ι : Type*} [Fintype ι]
    (W : Submodule RRField (RRVec ι))
    (hW : ∀ x ∈ W, ∀ y ∈ W, rrStandard ι x y = 0) :
    Module.finrank RRField W ≤ Fintype.card ι := by
  have hle : W ≤ (rrStandard ι).orthogonal W := by
    intro y hy
    exact LinearMap.BilinForm.mem_orthogonal_iff.mpr fun x hx => hW x hx y hy
  have hdim := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal (rrStandard_nondegenerate ι) W,
    rrVec_dim] at hdim
  have htotal := W.finrank_le
  rw [rrVec_dim] at htotal
  omega

private def rrRestrict {ι : Type*} (J : Finset ι) :
    RRVec ι →ₗ[RRField] RRVec J where
  toFun := fun x i => x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma rrNonzero_one (x : RRField) (hx : x ≠ 0) : x = 1 := by
  have h : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact h.resolve_left hx

open Classical in
private lemma rrCommonIso_bound {ι σ : Type*} [Fintype ι]
    (W : Submodule RRField (RRVec ι)) (L : σ → ι → RRField)
    (hW : ∀ s, ∀ x ∈ W, ∀ y ∈ W,
      (∑ i, L s i * rrCross (x i) (y i)) = 0) :
    Module.finrank RRField W + (Finset.univ.filter (fun i => ∃ s, L s i ≠ 0)).card ≤
      2 * Fintype.card ι := by
  classical
  let active : ι → Prop := fun i => ∃ s, L s i ≠ 0
  have aux (J : Finset ι) (W : Submodule RRField (RRVec ι))
      (hs : ∀ x ∈ W, ∀ i ∉ J, x i = 0)
      (hi : ∀ s, ∀ x ∈ W, ∀ y ∈ W,
        (∑ i, L s i * rrCross (x i) (y i)) = 0) :
      Module.finrank RRField W + (J.filter active).card ≤ 2 * J.card := by
    induction J using Finset.strongInductionOn generalizing W with
    | _ J ih =>
      by_cases hn : (J.filter active).Nonempty
      · obtain ⟨i₀, hi₀⟩ := hn
        obtain ⟨hi₀J, hactive⟩ := Finset.mem_filter.mp hi₀
        obtain ⟨s, hs₀⟩ := hactive
        let T := J.filter (fun i => L s i ≠ 0)
        let J' := J \ T
        have hTmem (i : ι) : i ∈ T ↔ i ∈ J ∧ L s i ≠ 0 := Finset.mem_filter
        have hi₀T : i₀ ∈ T := (hTmem _).mpr ⟨hi₀J, hs₀⟩
        have hTJ : T ⊆ J := fun i hiT => ((hTmem i).mp hiT).1
        have hlt : J' ⊂ J := Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.sdiff_subset, fun he => (Finset.mem_sdiff.mp
            (show i₀ ∈ J' by rw [he]; exact hi₀J)).2 hi₀T⟩
        let π : RRVec ι →ₗ[RRField] RRVec T := rrRestrict T
        let f : W →ₗ[RRField] RRVec T := π.comp W.subtype
        let N : Submodule RRField (RRVec ι) := W ⊓ LinearMap.ker π
        have hNle : N ≤ W := inf_le_left
        have hNs : ∀ x ∈ N, ∀ i ∉ J', x i = 0 := by
          intro x hx i hi'
          by_cases hiJ : i ∈ J
          · have hiT : i ∈ T := by
              by_contra hnT
              exact hi' (Finset.mem_sdiff.mpr ⟨hiJ, hnT⟩)
            have hxker : x ∈ LinearMap.ker π := (show x ∈ W ⊓ LinearMap.ker π from hx).2
            exact congrFun (LinearMap.mem_ker.mp hxker) (⟨i, hiT⟩ : T)
          · exact hs x (hNle hx) i hiJ
        have hNdim := ih J' hlt N hNs (fun s x hx y hy => hi s x (hNle hx) y (hNle hy))
        have hImIso : ∀ x ∈ LinearMap.range f, ∀ y ∈ LinearMap.range f,
            rrStandard T x y = 0 := by
          intro x hx y hy
          obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx
          obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hy
          change (∑ i : T, rrCross (u.val i) (v.val i)) = 0
          rw [Finset.sum_coe_sort T (fun i => rrCross (u.val i) (v.val i))]
          calc
            (∑ i ∈ T, rrCross (u.val i) (v.val i)) =
                ∑ i ∈ T, L s i * rrCross (u.val i) (v.val i) := by
              refine Finset.sum_congr rfl fun i hiT => ?_
              rw [rrNonzero_one _ ((hTmem i).mp hiT).2, one_mul]
            _ = ∑ i, L s i * rrCross (u.val i) (v.val i) := by
              apply Finset.sum_subset (Finset.subset_univ _)
              intro i _ hiT
              by_cases hiJ : i ∈ J
              · have hz : L s i = 0 := by
                  by_contra hnz
                  exact hiT ((hTmem i).mpr ⟨hiJ, hnz⟩)
                rw [hz, zero_mul]
              · simp [hs u.val u.property i hiJ, rrCross]
            _ = 0 := hi s u.val u.property v.val v.property
        have hImdim := rrStandard_iso_dim (LinearMap.range f) hImIso
        rw [Fintype.card_coe] at hImdim
        have hker : LinearMap.ker f = N.comap W.subtype := by
          ext u
          change π u.val = 0 ↔ u.val ∈ W ⊓ LinearMap.ker π
          rw [Submodule.mem_inf, LinearMap.mem_ker]
          simp [u.property]
        have hkerdim : Module.finrank RRField (N.comap W.subtype) =
            Module.finrank RRField N := (Submodule.comapSubtypeEquivOfLe hNle).finrank_eq
        have hrank := f.finrank_range_add_finrank_ker
        rw [hker, hkerdim] at hrank
        have hJcard : J'.card + T.card = J.card := Finset.card_sdiff_add_card_eq_card hTJ
        have hActT : T ⊆ J.filter active := fun i hit =>
          Finset.mem_filter.mpr ⟨((hTmem i).mp hit).1, ⟨s, ((hTmem i).mp hit).2⟩⟩
        have hActEq : (J.filter active) \ T = J'.filter active := by
          ext i
          simp only [J', Finset.mem_sdiff, Finset.mem_filter]
          tauto
        have hActCard : (J'.filter active).card + T.card = (J.filter active).card := by
          rw [← hActEq]
          exact Finset.card_sdiff_add_card_eq_card hActT
        omega
      · have he : J.filter active = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
        let f : W →ₗ[RRField] RRVec J := (rrRestrict J).comp W.subtype
        have hf : Function.Injective f := by
          intro x y hxy
          apply Subtype.ext
          funext i
          by_cases h : i ∈ J
          · exact congrFun hxy (⟨i, h⟩ : J)
          · rw [hs x.val x.property i h, hs y.val y.property i h]
        have hrank := LinearMap.finrank_le_finrank_of_injective hf
        rw [rrVec_dim, Fintype.card_coe] at hrank
        simpa [he] using hrank
  simpa [active] using aux Finset.univ W (fun x _ i hi => (hi (Finset.mem_univ i)).elim) hW

open Classical in
private lemma rrCommonIso_codim {ι σ V : Type*} [Fintype ι]
    [AddCommGroup V] [Module RRField V] [FiniteDimensional RRField V]
    (coords : V →ₗ[RRField] RRVec ι) (hcoords : Function.Surjective coords)
    (W : Submodule RRField V) (L : σ → ι → RRField)
    (hW : ∀ s, ∀ x ∈ W, ∀ y ∈ W,
      (∑ i, L s i * rrCross (coords x i) (coords y i)) = 0) :
    Module.finrank RRField W + (Finset.univ.filter (fun i => ∃ s, L s i ≠ 0)).card ≤
      Module.finrank RRField V := by
  let f : W →ₗ[RRField] RRVec ι := coords.comp W.subtype
  have hIso : ∀ s, ∀ x ∈ LinearMap.range f, ∀ y ∈ LinearMap.range f,
      (∑ i, L s i * rrCross (x i) (y i)) = 0 := by
    intro s x hx y hy
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hy
    exact hW s u.val u.property v.val v.property
  have hbound := rrCommonIso_bound (LinearMap.range f) L hIso
  let N : Submodule RRField V := W ⊓ LinearMap.ker coords
  have hNle : N ≤ W := inf_le_left
  have hker : LinearMap.ker f = N.comap W.subtype := by
    ext u
    change coords u.val = 0 ↔ u.val ∈ W ⊓ LinearMap.ker coords
    rw [Submodule.mem_inf, LinearMap.mem_ker]
    simp [u.property]
  have hkerdim : Module.finrank RRField (N.comap W.subtype) = Module.finrank RRField N :=
    (Submodule.comapSubtypeEquivOfLe hNle).finrank_eq
  have hkerle : Module.finrank RRField N ≤ Module.finrank RRField (LinearMap.ker coords) :=
    Submodule.finrank_mono (show N ≤ LinearMap.ker coords from inf_le_right)
  have hf := f.finrank_range_add_finrank_ker
  rw [hker, hkerdim] at hf
  have hsize := coords.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hcoords, finrank_top, rrVec_dim] at hsize
  omega


open scoped BigOperators

private def daMass {α : Type*} (w : α → ℝ) (I : Finset α) : ℝ := ∑ v ∈ I, w v

private noncomputable def daNbr {α : Type*} [Fintype α] (adj : α → α → Prop)
    (I : Finset α) : Finset α := by
  classical
  exact Finset.univ.filter fun v => ∃ u ∈ I, adj u v

private def daStable {α : Type*} (adj : α → α → Prop) (I : Finset α) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬adj u v

private def daSaving {α : Type*} [Fintype α] [DecidableEq α] (adj : α → α → Prop)
    (w : α → ℝ) (b : ℝ) : Prop :=
  (∃ I : Finset α, daStable adj I ∧ b = (daMass w I - daMass w (daNbr adj I)) / 2) ∨
    ∃ v, b = w v - daMass w (daNbr adj {v})

private noncomputable def daMark {α : Type*} [Fintype α] (adj : α → α → Prop)
    (I : Finset α) (v : α) : ℝ := by
  classical
  exact (if v ∈ I then 1 else 0) - (if v ∈ daNbr adj I then 1 else 0)

private theorem da_mem_nbr {α : Type*} [Fintype α] {adj : α → α → Prop}
    {I : Finset α} {v : α} : v ∈ daNbr adj I ↔ ∃ u ∈ I, adj u v := by
  classical
  simp [daNbr]

private theorem da_mark_mem {α : Type*} [Fintype α] {adj : α → α → Prop}
    {I : Finset α} (hI : daStable adj I) {v : α} (hv : v ∈ I) : daMark adj I v = 1 := by
  classical
  have hn : v ∉ daNbr adj I := by
    intro h
    obtain ⟨u, hu, he⟩ := da_mem_nbr.mp h
    exact hI u hu v hv he
  simp [daMark, hv, hn]

private theorem da_mark_nbr {α : Type*} [Fintype α] {adj : α → α → Prop}
    {I : Finset α} (hI : daStable adj I) {v : α} (hv : v ∈ daNbr adj I) :
    daMark adj I v = -1 := by
  classical
  have hn : v ∉ I := by
    intro h
    obtain ⟨u, hu, he⟩ := da_mem_nbr.mp hv
    exact hI u hu v h he
  simp [daMark, hn, hv]

private theorem da_mark_nonpos {α : Type*} [Fintype α] {adj : α → α → Prop}
    {I : Finset α} {v : α} (hv : v ∉ I) : daMark adj I v ≤ 0 := by
  classical
  simp only [daMark, ite_eq_right hv]
  split_ifs <;> norm_num

private theorem da_mark_le {α : Type*} [Fintype α] {adj : α → α → Prop}
    {I : Finset α} {v : α} : daMark adj I v ≤ 1 := by
  classical
  unfold daMark
  split_ifs <;> norm_num

private theorem da_mark_edge_eq {α : Type*} [Fintype α] {adj : α → α → Prop}
    (hsym : ∀ ⦃u v⦄, adj u v → adj v u) {I : Finset α} (hI : daStable adj I) {u v : α}
    (he : adj u v) (hmem : u ∈ I ∨ v ∈ I) : daMark adj I u + daMark adj I v = 0 := by
  rcases hmem with hu | hv
  · rw [da_mark_mem hI hu, da_mark_nbr hI (da_mem_nbr.mpr ⟨u, hu, he⟩)]
    norm_num
  · rw [da_mark_nbr hI (da_mem_nbr.mpr ⟨v, hv, hsym he⟩), da_mark_mem hI hv]
    norm_num

private theorem da_mark_edge_le {α : Type*} [Fintype α] {adj : α → α → Prop}
    (hsym : ∀ ⦃u v⦄, adj u v → adj v u) {I : Finset α} (hI : daStable adj I) {u v : α}
    (he : adj u v) : daMark adj I u + daMark adj I v ≤ 0 := by
  classical
  by_cases hu : u ∈ I
  · exact le_of_eq (da_mark_edge_eq hsym hI he (Or.inl hu))
  by_cases hv : v ∈ I
  · exact le_of_eq (da_mark_edge_eq hsym hI he (Or.inr hv))
  exact add_nonpos (da_mark_nonpos hu) (da_mark_nonpos hv)

private theorem da_mark_weight {α : Type*} [Fintype α] (adj : α → α → Prop)
    (w : α → ℝ) (I : Finset α) :
    (∑ v, w v * daMark adj I v) = daMass w I - daMass w (daNbr adj I) := by
  classical
  have hf (J : Finset α) : daMass w J = ∑ v, if v ∈ J then w v else 0 := by
    have h : Finset.univ.filter (fun v => v ∈ J) = J := by ext v; simp
    calc
      daMass w J = ∑ v ∈ Finset.univ.filter (fun v => v ∈ J), w v := by rw [h, daMass]
      _ = _ := Finset.sum_filter _ _
  rw [hf I, hf (daNbr adj I), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  unfold daMark
  split_ifs <;> ring

private theorem da_weight_shift {α : Type*} [Fintype α] (adj : α → α → Prop)
    (w t : α → ℝ) (I : Finset α) (d : ℝ) :
    (∑ u, w u * t u) = (∑ u, w u * (t u - d * daMark adj I u)) +
      d * (daMass w I - daMass w (daNbr adj I)) := by
  rw [← da_mark_weight adj w I, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  ring

private noncomputable def daPositive {α : Type*} [Fintype α] (t : α → ℝ) : Finset α := by
  classical
  exact Finset.univ.filter fun v => 0 < t v

private theorem da_mem_positive {α : Type*} [Fintype α] (t : α → ℝ) (v : α) :
    v ∈ daPositive t ↔ 0 < t v := by
  classical
  simp [daPositive]

private theorem da_bounded_aux {α : Type*} [Fintype α] {adj : α → α → Prop}
    (hsym : ∀ ⦃u v⦄, adj u v → adj v u) {w : α → ℝ} (hw : ∀ v, 0 ≤ w v) {b : ℝ} (hb : 0 ≤ b)
    (hstable : ∀ I, daStable adj I → (daMass w I - daMass w (daNbr adj I)) / 2 ≤ b) :
    ∀ n : ℕ, ∀ (t : α → ℝ) (B : ℝ),
      (daPositive t).card = n →
      0 ≤ B → (∀ v, t v ≤ B) → (∀ u v, adj u v → t u + t v ≤ 0) →
        (∑ v, w v * t v) ≤ 2 * B * b := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro t B hn hB ht he
    let I : Finset α := daPositive t
    have hmem (v : α) : v ∈ I ↔ 0 < t v := da_mem_positive t v
    have hI : daStable adj I := by
      intro u hu v hv huv
      linarith [(hmem u).mp hu, (hmem v).mp hv, he u v huv]
    by_cases hne : I.Nonempty
    · obtain ⟨p, hp, hmin⟩ := Finset.exists_max_image I (fun v => -t v) hne
      have hp0 := (hmem p).mp hp
      have hmin' (u : α) (hu : u ∈ I) : t p ≤ t u := by
        linarith [hmin u hu]
      let t' : α → ℝ := fun u => t u - t p * daMark adj I u
      have hB' : 0 ≤ B - t p := sub_nonneg.mpr (ht p)
      have hout (u : α) (hu : u ∉ I) : t' u ≤ 0 := by
        have ht0 : t u ≤ 0 := le_of_not_gt fun h => hu ((hmem u).mpr h)
        by_cases hun : u ∈ daNbr adj I
        · obtain ⟨v, hv, hvu⟩ := da_mem_nbr.mp hun
          dsimp only [t']
          rw [da_mark_nbr hI hun]
          linarith [hmin' v hv, he v u hvu]
        · simpa [t', daMark, hu, hun] using ht0
      have ht' (u : α) : t' u ≤ B - t p := by
        by_cases hu : u ∈ I
        · dsimp only [t']
          rw [da_mark_mem hI hu, mul_one]
          exact sub_le_sub_right (ht u) _
        · exact (hout u hu).trans hB'
      have he' (u v : α) (huv : adj u v) : t' u + t' v ≤ 0 := by
        by_cases hz : u ∈ I ∨ v ∈ I
        · change t u - t p * daMark adj I u + (t v - t p * daMark adj I v) ≤ 0
          have hm := congrArg (fun x : ℝ => t p * x) (da_mark_edge_eq hsym hI huv hz)
          rw [mul_add, mul_zero] at hm
          linarith [he u v huv]
        · exact add_nonpos (hout u fun h => hz (Or.inl h)) (hout v fun h => hz (Or.inr h))
      have hsub : daPositive t' ⊂ I := by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · intro v hv
          have hv' := (da_mem_positive t' v).mp hv
          by_contra hvi
          exact (not_lt_of_ge (hout v hvi)) hv'
        · intro h
          have hp' : p ∈ daPositive t' := h.symm ▸ hp
          simpa [t', da_mark_mem hI hp] using (da_mem_positive t' p).mp hp'
      have hn' : (daPositive t').card < n := by
        change I.card = n at hn
        rw [← hn]
        exact Finset.card_lt_card hsub
      have hind := ih _ hn' t' (B - t p) rfl hB' ht' he'
      have hspent : t p * (daMass w I - daMass w (daNbr adj I)) ≤ t p * (2 * b) :=
        mul_le_mul_of_nonneg_left (by linarith [hstable I hI]) hp0.le
      rw [da_weight_shift adj w t I (t p)]
      change (∑ v, w v * t' v) + t p * (daMass w I - daMass w (daNbr adj I)) ≤ _
      nlinarith only [hind, hspent]
    · have hnonpos : (∑ v, w v * t v) ≤ 0 := by
        apply Finset.sum_nonpos
        intro v hv
        exact mul_nonpos_of_nonneg_of_nonpos (hw v) (le_of_not_gt fun h => hne ⟨v, (hmem v).mpr h⟩)
      exact hnonpos.trans (by positivity)

private theorem da_single_stable {α : Type*} [DecidableEq α] {adj : α → α → Prop}
    (hirr : ∀ v, ¬adj v v) (v : α) : daStable adj {v} := by
  intro u hu a ha
  simp only [Finset.mem_singleton] at hu ha
  subst u
  subst a
  exact hirr v

private theorem da_single_nbr {α : Type*} [Fintype α] [DecidableEq α]
    {adj : α → α → Prop} {v u : α} : u ∈ daNbr adj {v} ↔ adj v u := by
  rw [da_mem_nbr]
  simp

private theorem da_signed_max {α : Type*} [Fintype α] [DecidableEq α] {adj : α → α → Prop}
    (hsym : ∀ ⦃u v⦄, adj u v → adj v u) (hirr : ∀ v, ¬adj v v) {w : α → ℝ} (hw : ∀ v, 0 ≤ w v)
    {b : ℝ} (hb : ∀ z, daSaving adj w z → z ≤ b) (t : α → ℝ)
    (ht : ∀ v, t v ≤ 1) (hp : ∀ u v, u ≠ v → t u + t v ≤ 1)
    (he : ∀ u v, adj u v → t u + t v ≤ 0) : (∑ v, w v * t v) ≤ b := by
  classical
  have hb0 : 0 ≤ b := by
    have h0 : daSaving adj w 0 := by
      refine Or.inl ⟨∅, ?_, ?_⟩
      · simp [daStable]
      · simp [daMass, daNbr]
    exact hb 0 h0
  have hstable (I : Finset α) (hI : daStable adj I) :
      (daMass w I - daMass w (daNbr adj I)) / 2 ≤ b := hb _ (Or.inl ⟨I, hI, rfl⟩)
  have hbound (f : α → ℝ) (B : ℝ) := da_bounded_aux hsym hw hb0 hstable _ f B rfl
  by_cases hlow : ∀ v, t v ≤ 1 / 2
  · have h := hbound t (1 / 2) (by norm_num) hlow he
    norm_num at h
    exact h
  · push Not at hlow
    obtain ⟨v, hv⟩ := hlow
    let d : ℝ := 2 * t v - 1
    let R : ℝ := 1 - t v
    let T : α → ℝ := fun u => t u - d * daMark adj {v} u
    have hd : 0 ≤ d := by dsimp [d]; linarith
    have hR : 0 ≤ R := sub_nonneg.mpr (ht v)
    have hI := da_single_stable hirr v
    have hTv : T v = R := by
      dsimp only [T, d, R]
      rw [da_mark_mem hI (Finset.mem_singleton_self v)]
      ring
    have hTn (u : α) (hu : adj v u) : T u ≤ -R := by
      dsimp only [T, d, R]
      rw [da_mark_nbr hI (da_single_nbr.mpr hu)]
      linarith [he v u hu]
    have hTo (u : α) (hu : u ≠ v) (hn : ¬adj v u) : T u = t u := by
      have hn' : u ∉ daNbr adj {v} := fun h => hn (da_single_nbr.mp h)
      simp [T, daMark, hu, hn']
    have hTb (u : α) : T u ≤ R := by
      by_cases hu : u = v
      · simp [hu, hTv]
      by_cases hn : adj v u
      · linarith [hTn u hn]
      · rw [hTo u hu hn]
        dsimp [R]
        linarith [hp u v hu]
    have hTe (u a : α) (hua : adj u a) : T u + T a ≤ 0 := by
      by_cases hu : adj v u
      · linarith [hTn u hu, hTb a]
      by_cases ha : adj v a
      · linarith [hTn a ha, hTb u]
      have huv : u ≠ v := fun h => ha (h ▸ hua)
      have hav : a ≠ v := fun h => hu (h ▸ hsym hua)
      rw [hTo u huv hu, hTo a hav ha]
      exact he u a hua
    have hpart := hbound T R hR hTb hTe
    have hsingle : w v - daMass w (daNbr adj {v}) ≤ b := hb _ (Or.inr ⟨v, rfl⟩)
    have hs : d * (w v - daMass w (daNbr adj {v})) ≤ d * b :=
      mul_le_mul_of_nonneg_left hsingle hd
    rw [da_weight_shift adj w t {v} d, show daMass w {v} = w v by simp [daMass]]
    change (∑ u, w u * T u) + d * (w v - daMass w (daNbr adj {v})) ≤ _
    dsimp only [d, R] at hpart hs
    nlinarith only [hpart, hs]

private def daCover {α : Type*} (adj : α → α → Prop) (cover : α → ℝ) : Prop :=
  (∀ v, 0 ≤ cover v) ∧ (∀ u v, u ≠ v → 1 ≤ cover u + cover v) ∧
    (∀ u v, adj u v → 2 ≤ cover u + cover v)

private theorem da_weight_complement {α : Type*} [Fintype α] (w t : α → ℝ) :
    (∑ v, w v * (1 - t v)) = daMass w Finset.univ - (∑ v, w v * t v) := by
  simp [daMass, mul_sub, Finset.sum_sub_distrib]

private theorem da_cover_minimum {α : Type*} [Fintype α] [DecidableEq α]
    {adj : α → α → Prop} (hsym : ∀ ⦃u v⦄, adj u v → adj v u) (hirr : ∀ v, ¬adj v v)
    {w : α → ℝ} (hw : ∀ v, 0 < w v) {b : ℝ} (hbs : daSaving adj w b)
    (hb : ∀ z, daSaving adj w z → z ≤ b) :
    (∀ cover, daCover adj cover → daMass w Finset.univ - b ≤ ∑ v, w v * cover v) ∧
    ∃ cover, daCover adj cover ∧ (∑ v, w v * cover v) = daMass w Finset.univ - b := by
  classical
  constructor
  · intro cover hcover
    let t : α → ℝ := fun v => 1 - cover v
    have ht (v : α) : t v ≤ 1 := by dsimp [t]; linarith [hcover.1 v]
    have hp (u v : α) (huv : u ≠ v) : t u + t v ≤ 1 := by
      dsimp [t]
      linarith [hcover.2.1 u v huv]
    have he (u v : α) (huv : adj u v) : t u + t v ≤ 0 := by
      dsimp [t]
      linarith [hcover.2.2 u v huv]
    have hs := da_signed_max hsym hirr (fun v => (hw v).le) hb t ht hp he
    have hc := da_weight_complement w t
    simp only [t, sub_sub_cancel] at hc
    rw [hc]
    linarith
  · have mk (t : α → ℝ) (ht : ∀ v, t v ≤ 1)
        (hp : ∀ u v, u ≠ v → t u + t v ≤ 1)
        (he : ∀ u v, adj u v → t u + t v ≤ 0) (hs : (∑ v, w v * t v) = b) :
        ∃ cover, daCover adj cover ∧ (∑ v, w v * cover v) = daMass w Finset.univ - b := by
      refine ⟨fun v => 1 - t v, ⟨?_, ?_, ?_⟩, ?_⟩
      · intro v
        linarith [ht v]
      · intro u v huv
        linarith [hp u v huv]
      · intro u v huv
        linarith [he u v huv]
      · rw [da_weight_complement, hs]
    rcases hbs with ⟨I, hI, hval⟩ | ⟨v, hval⟩
    · apply mk (fun u => daMark adj I u / 2)
      · intro u
        linarith [da_mark_le (adj := adj) (I := I) (v := u)]
      · intro u v huv
        linarith [da_mark_le (adj := adj) (I := I) (v := u),
          da_mark_le (adj := adj) (I := I) (v := v)]
      · intro u v huv
        linarith [da_mark_edge_le hsym hI huv]
      · simp_rw [← mul_div_assoc]
        rw [← Finset.sum_div, da_mark_weight, hval]
    · apply mk (daMark adj {v})
      · intro u
        exact da_mark_le
      · intro u a hua
        by_cases hu : u ∈ ({v} : Finset α)
        · have ha : a ∉ ({v} : Finset α) := by
            simp only [Finset.mem_singleton] at hu ⊢
            exact fun h => hua (hu.trans h.symm)
          linarith [da_mark_le (adj := adj) (I := {v}) (v := u),
            da_mark_nonpos (adj := adj) ha]
        · linarith [da_mark_nonpos (adj := adj) hu,
            da_mark_le (adj := adj) (I := {v}) (v := a)]
      · exact fun u a => da_mark_edge_le hsym (da_single_stable hirr v)
      · rw [da_mark_weight, hval]
        simp [daMass]

private theorem da_saving_maximum {α : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) (w : α → ℝ) (hw : ∀ v, 0 < w v)
    (hother : ∀ v : α, ∃ u, u ≠ v) (hne : Nonempty α) :
    ∃ b, daSaving adj w b ∧ (∀ z, daSaving adj w z → z ≤ b) ∧ b < daMass w Finset.univ := by
  classical
  let Iset : Finset (Finset α) := Finset.univ.powerset.filter (daStable adj)
  let f : Finset α → ℝ := fun I => (daMass w I - daMass w (daNbr adj I)) / 2
  let g : α → ℝ := fun v => w v - daMass w (daNbr adj {v})
  let vals : Finset ℝ := Iset.image f ∪ Finset.univ.image g
  have hvals (z : ℝ) : daSaving adj w z ↔ z ∈ vals := by
    change _ ↔ z ∈ Iset.image f ∪ Finset.univ.image g
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro (⟨I, hI, rfl⟩ | ⟨v, rfl⟩)
      · exact Or.inl ⟨I, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ I), hI⟩, rfl⟩
      · exact Or.inr ⟨v, Finset.mem_univ v, rfl⟩
    · rintro (⟨I, hI, rfl⟩ | ⟨v, hv, rfl⟩)
      · exact Or.inl ⟨I, (Finset.mem_filter.mp hI).2, rfl⟩
      · exact Or.inr ⟨v, rfl⟩
  obtain ⟨v⟩ := hne
  have huv : vals.Nonempty := ⟨g v, (hvals _).mp (Or.inr ⟨v, rfl⟩)⟩
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image vals id huv
  have hbs := (hvals _).mpr hb
  refine ⟨b, hbs, fun z hz => hmax z ((hvals _).mp hz), ?_⟩
  have hnonneg (I : Finset α) : 0 ≤ daMass w I := Finset.sum_nonneg fun u _ => (hw u).le
  have hmono (I : Finset α) : daMass w I ≤ daMass w Finset.univ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun u hu hI => (hw u).le
  have ht : 0 < daMass w (Finset.univ : Finset α) := by
    have h := hmono {v}
    simp only [daMass, Finset.sum_singleton] at h
    exact (hw v).trans_le h
  rcases hbs with ⟨I, hI, hval⟩ | ⟨u, hval⟩
  · rw [hval]
    linarith [hmono I, hnonneg (daNbr adj I)]
  · obtain ⟨a, hau⟩ := hother u
    have h := hmono {u, a}
    have hp : daMass w {u, a} = w u + w a := by
      simp [daMass, Finset.sum_insert, Ne.symm hau]
    rw [hp] at h
    rw [hval]
    linarith [hw a, hnonneg (daNbr adj {u})]


open scoped BigOperators

-- The cover bound already rules out an empty atom type and handles atoms equal to zero.
private theorem finite_atom_packing {S A : Type*} [Fintype S] [Fintype A]
    (d : A → S → ℝ) (w : S → ℝ) (hw : ∀ s, 0 ≤ w s) {M q : ℝ}
    (hcover : ∀ l : S → ℝ, (∀ s, 0 ≤ l s) →
      (∀ a, 1 ≤ ∑ s, l s * d a s) → M ≤ ∑ s, l s * w s)
    (hq : 0 < q) (hMq : 1 ≤ q * M) :
    ∃ p : A → ℝ, (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1 ∧
      ∀ s, (∑ a, p a * d a s) ≤ q * w s := by
  classical
  let H := convexHull ℝ (Set.range d)
  let P : Set (S → ℝ) := {x | ∃ p : A → ℝ, (∀ a, 0 ≤ p a) ∧
    (∑ a, p a) = 1 ∧ ∀ s, x s = ∑ a, p a * d a s}
  have hHP : H ⊆ P := by
    apply convexHull_min
    · rintro _ ⟨a, rfl⟩
      refine ⟨fun i => if i = a then 1 else 0, ?_, by simp, ?_⟩
      · intro i
        by_cases hi : i = a <;> simp [hi]
      · intro s
        simp [ite_mul]
    · rintro x ⟨p, hp, hp₁, hxp⟩ y ⟨r, hr, hr₁, hyr⟩ α β hα hβ hαβ
      refine ⟨fun a => α * p a + β * r a,
        fun a => add_nonneg (mul_nonneg hα (hp a)) (mul_nonneg hβ (hr a)), ?_, ?_⟩
      · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp₁, hr₁]
        simpa using hαβ
      · intro s
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hxp s, hyr s]
        simp_rw [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  let b : S → ℝ := q • w
  by_contra hn
  have hdisj : Disjoint (Set.Iic b) H := by
    refine Set.disjoint_left.mpr fun x hxb hxH => ?_
    obtain ⟨p, hp, hp₁, hxp⟩ := hHP hxH
    exact hn ⟨p, hp, hp₁, fun s => (hxp s).symm.trans_le (hxb s)⟩
  obtain ⟨f, u, v, hB, huv, hH⟩ := geometric_hahn_banach_closed_compact
    (convex_Iic (𝕜 := ℝ) b) isClosed_Iic (convex_convexHull ℝ (Set.range d))
    ((Set.finite_range d).isCompact_convexHull ℝ) hdisj
  have hb₀ : (0 : S → ℝ) ∈ Set.Iic b := by
    intro s
    exact mul_nonneg hq.le (hw s)
  have hu : 0 < u := by simpa using hB 0 hb₀
  let L : S → ℝ := fun s => f (Pi.single s 1)
  have hL : ∀ s, 0 ≤ L s := by
    intro s
    by_contra! hs
    let t := u / L s
    have ht : t ≤ 0 := div_nonpos_of_nonneg_of_nonpos hu.le hs.le
    have hy₀ : t • (Pi.single s (1 : ℝ) : S → ℝ) ≤ 0 := by
      intro j
      change t * (Pi.single s (1 : ℝ) : S → ℝ) j ≤ 0
      by_cases hj : j = s
      · subst j
        simpa using ht
      · simp [Pi.single_eq_of_ne hj]
    have hy : t • (Pi.single s (1 : ℝ) : S → ℝ) ∈ Set.Iic b := hy₀.trans hb₀
    have hfy : f (t • (Pi.single s (1 : ℝ) : S → ℝ)) = u := by
      rw [map_smul]
      change (u / L s) * L s = u
      exact div_mul_cancel₀ _ hs.ne
    exact (hfy ▸ hB _ hy).false
  have hf (x : S → ℝ) : f x = ∑ s, L s * x s := by
    conv_lhs => rw [pi_eq_sum_univ' x, map_sum]
    simp only [map_smul, smul_eq_mul, L, mul_comm]
  have hnorm (x : S → ℝ) : (∑ s, (L s / u) * x s) = f x / u := by
    rw [hf, Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have hc : ∀ a, 1 ≤ ∑ s, (L s / u) * d a s := by
    intro a
    rw [hnorm, le_div_iff₀ hu, one_mul]
    exact (huv.trans (hH _ (subset_convexHull ℝ (Set.range d) (Set.mem_range_self a)))).le
  have hmass := hcover (fun s => L s / u) (fun s => div_nonneg (hL s) hu.le) hc
  have hbudget : q * (∑ s, (L s / u) * w s) < 1 := by
    rw [hnorm, ← mul_div_assoc]
    have hfb : f b = q * f w := f.map_smul q w
    rw [← hfb]
    exact (div_lt_one hu).mpr (hB b (Set.mem_Iic.mpr le_rfl))
  exact (not_lt_of_ge (hMq.trans (mul_le_mul_of_nonneg_left hmass hq.le))) hbudget


private def words {k m : ℕ} (A : Fin m → Vec k) (s : Vec k) (i : Fin m) : F2 :=
  dotProduct (A i) s

open Classical in
private noncomputable def varyingOn {k m : ℕ} (A : Fin m → Vec k)
    (E : Finset (Vec k)) (a : Vec k) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∃ s ∈ E, words A s i ≠ words A a i)

private def columnSide {k m : ℕ} (A : Fin m → Vec k) (E : Finset (Vec k))
    (i : Fin m) (b : F2) : Finset (Vec k) :=
  E.filter (fun v => words A v i ≠ b)

private def adjacent {k m : ℕ} (A : Fin m → Vec k) (E : Finset (Vec k))
    (s u : Vec k) : Prop :=
  s ≠ u ∧ ∃ (i : Fin m) (b : F2), columnSide A E i b = ({s,u} : Finset (Vec k))

private def liftSel {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r) :
    Vec k →ₗ[F2] Vec n :=
  e.symm.toLinearMap.comp (LinearMap.inl F2 (Vec k) (Data m r))

private noncomputable def liftData {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r) :
    Vec (2*m+r) →ₗ[F2] Vec n :=
  e.symm.toLinearMap.comp ((LinearMap.inr F2 (Vec k) (Data m r)).comp
    (pack m r).symm.toLinearMap)

private noncomputable def point {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r)
    (s : Vec k) (d : Vec (2*m+r)) : Vec n :=
  e.symm (s, (pack m r).symm d)

private lemma point_eq {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r)
    (s : Vec k) (d : Vec (2*m+r)) : point e s d = liftSel e s + liftData e d := by
  change e.symm (s, (pack m r).symm d) = e.symm (s, 0) + e.symm (0, (pack m r).symm d)
  rw [← e.symm.map_add]
  simp

private noncomputable def phase {k m r : ℕ} (A : Fin m → Vec k) (h : Vec k → F2)
    (s : Vec k) (d : Vec (2*m+r)) : F2 :=
  h s + ∑ i, words A s i * ((pack m r).symm d).1 i * ((pack m r).symm d).2.1 i

private noncomputable def score {k m r n : ℕ}
    (e : Vec n ≃ₗ[F2] Vec k × Data m r) (A : Fin m → Vec k) (h : Vec k → F2)
    (C : Circuit) (s : Vec k) : ℝ :=
  avg (fun d => avg (fun x : Vec n =>
    if C.eval (bitsOf n x ++ bitsOf n (point e s d)) =
      decide (dotProduct x (point e s d) + phase (r := r) A h s d = 1)
    then (1 : ℝ) else -1))

private lemma avgSum {α ι : Type*} [Fintype α] [Fintype ι] (cov : ι → ℝ)
    (f : ι → α → ℝ) :
    avg (fun x => ∑ i, cov i * f i x) = ∑ i, cov i * avg (f i) := by
  unfold avg
  rw [Finset.sum_comm, Finset.sum_div]
  simp_rw [← Finset.mul_sum, mul_div_assoc]

private lemma avgShift {n : ℕ} (f : Vec n → ℝ) (a : Vec n) :
    avg (fun x => f (x + a)) = avg f := by
  unfold avg
  exact congrArg (fun t : ℝ => t / Fintype.card (Vec n)) (Equiv.sum_comp (Equiv.addRight a) f)

private lemma avg_half_of_pair {n : ℕ} (f : Vec n → ℝ) (a : Vec n)
    (ha : ∀ x, f x + f (x + a) ≤ 1) : avg f ≤ 1/2 := by
  have hu := avg_le _ 1 ha
  have he : avg (fun x => f x + f (x + a)) = avg f + avg (fun x => f (x + a)) := by
    simp only [avg, Finset.sum_add_distrib, add_div]
  rw [he, avgShift] at hu
  linarith

open Classical in
private noncomputable def leafScore {k m r n : ℕ}
    (e : Vec n ≃ₗ[F2] Vec k × Data m r) (A : Fin m → Vec k) (h : Vec k → F2)
    (W : Submodule F2 (Vec n)) (a : Vec n) (D : Circuit) (pos : Vec n → Vec n)
    (s : Vec k) : ℝ :=
  avg (fun d => let y := point e s d
    if y - a ∈ W then
      chi (bitValue (D.eval (bitsOf n y)) + dotProduct (pos y) y + phase (r := r) A h s d)
    else 0)

private lemma leaf_le_one {k m r n : ℕ}
    (e : Vec n ≃ₗ[F2] Vec k × Data m r) (A : Fin m → Vec k) (h : Vec k → F2)
    (W : Submodule F2 (Vec n)) (a : Vec n) (D : Circuit) (pos : Vec n → Vec n)
    (s : Vec k) : leafScore e A h W a D pos s ≤ 1 := by
  apply avg_le
  intro d
  dsimp only
  split
  · exact chi_le_one _
  · norm_num

private lemma leaf_sparse_le_half {k m r n : ℕ}
    (e : Vec n ≃ₗ[F2] Vec k × Data m r) (A : Fin m → Vec k) (h : Vec k → F2)
    (W : Submodule F2 (Vec n)) (a : Vec n) (D : Circuit) (pos : Vec n → Vec n)
    (v : Vec (2*m+r)) (hv : liftData e v ∉ W) (s : Vec k) :
    leafScore e A h W a D pos s ≤ 1/2 := by
  classical
  unfold leafScore
  apply avg_half_of_pair _ v
  intro d
  have hnot : ¬ (point e s d - a ∈ W ∧ point e s (d + v) - a ∈ W) := by
    rintro ⟨h₁, h₂⟩
    apply hv
    have hdelta := W.sub_mem h₂ h₁
    rw [point_eq, point_eq e s d, map_add] at hdelta
    have he : liftSel e s + (liftData e d + liftData e v) - a -
        (liftSel e s + liftData e d - a) = liftData e v := by abel
    rwa [he] at hdelta
  dsimp only
  split_ifs with h₁ h₂ h₂
  · exact (hnot ⟨h₁, h₂⟩).elim
  · simpa using chi_le_one _
  · simpa using chi_le_one _
  · norm_num

private lemma point_mem_iff {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r)
    (W : Submodule F2 (Vec n)) (a : Vec n) (hf : ∀ d, liftData e d ∈ W)
    (s : Vec k) (d : Vec (2*m+r)) :
    point e s d - a ∈ W ↔ liftSel e s - a ∈ W := by
  rw [point_eq, show liftSel e s + liftData e d - a = (liftSel e s - a) + liftData e d by abel]
  constructor
  · intro h
    simpa using W.sub_mem h (hf d)
  · intro h
    exact W.add_mem h (hf d)

open scoped Affine in
private lemma selectorSupport {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r)
    (W : Submodule F2 (Vec n)) (a : Vec n) (s₀ : Vec k) (h₀ : liftSel e s₀ - a ∈ W) :
    ∀ s : Vec k, liftSel e s - a ∈ W ↔
      s ∈ AffineSubspace.mk' s₀ (W.comap (liftSel e)) := by
  intro s
  rw [AffineSubspace.mem_mk']
  change liftSel e s - a ∈ W ↔ (liftSel e) (s - s₀) ∈ W
  rw [map_sub]
  constructor
  · intro hs
    simpa [sub_sub_sub_cancel_right] using W.sub_mem hs h₀
  · intro hs
    convert W.add_mem hs h₀ using 1 <;> abel

private lemma fullLeafRank {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r)
    (W : Submodule F2 (Vec n)) (a : Vec n) (E : Finset (Vec k)) (s₀ : Vec k)
    (h₀ : s₀ ∈ E) (hs : ∀ s ∈ E, liftSel e s - a ∈ W) (hf : ∀ d, liftData e d ∈ W) :
    (2*m+r) + Module.finrank F2 (affineSpan F2 (E : Set (Vec k))).direction ≤
      Module.finrank F2 W := by
  let H := (affineSpan F2 (E : Set (Vec k))).direction
  have hU : H ≤ W.comap (liftSel e) := by
    have hh : affineSpan F2 (E : Set (Vec k)) ≤ AffineSubspace.mk' s₀ (W.comap (liftSel e)) :=
      affineSpan_le_of_subset_coe (fun s hmem =>
        (selectorSupport e W a s₀ (hs s₀ h₀) s).mp (hs s hmem))
    simpa only [AffineSubspace.direction_mk'] using AffineSubspace.direction_le hh
  let f : H × Vec (2*m+r) →ₗ[F2] Vec n :=
    e.symm.toLinearMap.comp (H.subtype.prodMap (pack m r).symm.toLinearMap)
  have hfmem (x : H × Vec (2*m+r)) : f x ∈ W := by
    change point e x.1.val x.2 ∈ W
    rw [point_eq]
    exact W.add_mem (hU x.1.property) (hf x.2)
  let g := f.codRestrict W hfmem
  have hg : Function.Injective g := by
    intro x y hy
    have hy' := e.symm.injective (congrArg Subtype.val hy)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hy'))
      ((pack m r).symm.injective (congrArg Prod.snd hy'))
  have hdim := LinearMap.finrank_le_finrank_of_injective hg
  simpa only [Module.finrank_prod, Module.finrank_fin_fun, Nat.add_comm] using hdim

private lemma missingPair {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r)
    (W : Submodule F2 (Vec n)) (a : Vec n) (E : Finset (Vec k))
    (hc : 4 ≤ E.card) (heven : Even E.card) (hsum : (∑ s ∈ E, s) = 0)
    (s : E) (hs : liftSel e s.val - a ∉ W) :
    ∃ u : E, s ≠ u ∧ liftSel e u.val - a ∉ W := by
  classical
  by_contra! hno
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (E.erase s.val).card by
    rw [Finset.card_erase_of_mem s.property]; omega)
  have huE := (Finset.mem_erase.mp hu).2
  have hsu : s ≠ (⟨u, huE⟩ : E) := fun h => (Finset.mem_erase.mp hu).1 (congrArg Subtype.val h).symm
  have huW := hno ⟨u,huE⟩ hsu
  let H := AffineSubspace.mk' u (W.comap (liftSel e))
  have hH : affineSpan F2 ((E.erase s.val : Finset (Vec k)) : Set (Vec k)) ≤ H :=
    affineSpan_le_of_subset_coe fun v hv =>
      (selectorSupport e W a u huW v).mp (hno ⟨v, (Finset.mem_erase.mp hv).2⟩
        (fun h => (Finset.mem_erase.mp hv).1 (congrArg Subtype.val h).symm))
  rw [selector_affineSpan_erase s.property heven hsum] at hH
  exact hs ((selectorSupport e W a u huW s.val).mpr
    (hH (subset_affineSpan F2 _ s.property)))

private lemma deficit_at_pair {α : Type*} [Fintype α] [DecidableEq α]
    (σ cov : α → ℝ) (hσ : ∀ v, σ v ≤ 1) (hcov : ∀ v, 0 ≤ cov v)
    {s t : α} (hne : s ≠ t) (a : ℝ) (hsa : σ s ≤ 1-a) (hta : σ t ≤ 1-a)
    (hm : 1 ≤ a * (cov s + cov t)) : 1 ≤ ∑ v, cov v * (1-σ v) := by
  calc
    1 ≤ a * (cov s + cov t) := hm
    _ ≤ cov s * (1-σ s) + cov t * (1-σ t) := by
      rw [mul_add, mul_comm a, mul_comm a]
      exact add_le_add (mul_le_mul_of_nonneg_left (by linarith) (hcov s))
        (mul_le_mul_of_nonneg_left (by linarith) (hcov t))
    _ = ∑ v ∈ ({s,t} : Finset α), cov v * (1-σ v) := by simp [hne]
    _ ≤ ∑ v, cov v * (1-σ v) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun v _ _ =>
        mul_nonneg (hcov v) (sub_nonneg.mpr (hσ v))

private lemma deficit_at_four {α : Type*} [Fintype α] [DecidableEq α]
    {adj : α → α → Prop} (σ cov : α → ℝ) (hσ : ∀ v, σ v ≤ 1)
    (hcov : daCover adj cov) (I : Finset α) (hI : 4 ≤ I.card)
    (hhalf : ∀ v ∈ I, σ v ≤ 1/2) :
    1 ≤ ∑ v, cov v * (1-σ v) := by
  obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq hI
  obtain ⟨s,t,u,v,hst,hsu,hsv,htu,htv,huv,rfl⟩ := Finset.card_eq_four.mp hJ
  have hp := hcov.2.1 s t hst
  have hq := hcov.2.1 u v huv
  have hle (j : α) (hj : j ∈ ({s,t,u,v} : Finset α)) :
      cov j / 2 ≤ cov j * (1-σ j) := by
    have h := hhalf j (hJI hj)
    nlinarith [mul_le_mul_of_nonneg_left h (hcov.1 j)]
  have hsum := Finset.sum_le_sum (fun j hj => hle j hj)
  simp [hst,hsu,hsv,htu,htv,huv] at hsum
  calc
    1 ≤ ∑ j ∈ ({s,t,u,v} : Finset α), cov j * (1-σ j) := by
      simp [hst,hsu,hsv,htu,htv,huv]
      linarith
    _ ≤ ∑ j, cov j * (1-σ j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ =>
        mul_nonneg (hcov.1 j) (sub_nonneg.mpr (hσ j))

private def payloadSecond {U : Type*} [Add U] (f : U → ZMod 2) (x u v : U) : ZMod 2 :=
  f (x + u + v) - f (x + u) - f (x + v) + f x

private lemma payloadSecond_add {U : Type*} [Add U] (f g : U → ZMod 2) (x u v : U) :
    payloadSecond (fun y => f y + g y) x u v =
      payloadSecond f x u v + payloadSecond g x u v := by
  unfold payloadSecond
  ring

private lemma payloadSecond_const {U : Type*} [Add U] (a : ZMod 2) (x u v : U) :
    payloadSecond (fun _ => a) x u v = 0 := by
  unfold payloadSecond
  ring

private lemma payloadSecond_weight {U : Type*} [Add U] (a : ZMod 2) (f : U → ZMod 2)
    (x u v : U) : payloadSecond (fun y => a * f y) x u v = a * payloadSecond f x u v := by
  unfold payloadSecond
  ring

private lemma payloadSecond_sum {U I : Type*} [Add U] (t : Finset I) (f : I → U → ZMod 2)
    (x u v : U) : payloadSecond (fun y => ∑ i ∈ t, f i y) x u v =
      ∑ i ∈ t, payloadSecond (f i) x u v := by
  simp only [payloadSecond, Finset.sum_add_distrib, Finset.sum_sub_distrib]

private lemma payloadSecond_linear {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (L : U →ₗ[ZMod 2] ZMod 2) (x u v : U) : payloadSecond L x u v = 0 := by
  simp only [payloadSecond, map_add]
  ring

private lemma payloadSecond_coordinateMul {U I : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (L R : U →ₗ[ZMod 2] (I → ZMod 2)) (a b : I → ZMod 2) (i : I) (x u v : U) :
    payloadSecond (fun y => (a i + L y i) * (b i + R y i)) x u v =
      L u i * R v i + L v i * R u i := by
  simp only [payloadSecond, map_add, Pi.add_apply]
  ring

-- Offsets may vary arbitrarily with the selector; the linear slopes do not vary.
private structure PayloadPolynomial (S U J I : Type*) [AddCommGroup U] [Module (ZMod 2) U] where
  left : U →ₗ[ZMod 2] (J → ZMod 2)
  right : U →ₗ[ZMod 2] (J → ZMod 2)
  output : U →ₗ[ZMod 2] ZMod 2
  dataLeft : U →ₗ[ZMod 2] (I → ZMod 2)
  dataRight : U →ₗ[ZMod 2] (I → ZMod 2)
  left₀ : S → J → ZMod 2
  right₀ : S → J → ZMod 2
  output₀ : S → ZMod 2
  dataLeft₀ : S → I → ZMod 2
  dataRight₀ : S → I → ZMod 2
  target : S → ZMod 2
  word : S → I → ZMod 2

private def PayloadPolynomial.error {S U J I : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Fintype J] [Fintype I] (P : PayloadPolynomial S U J I) (s : S) (x : U) : ZMod 2 :=
  dotProduct (P.left₀ s + P.left x) (P.right₀ s + P.right x) +
    (P.output₀ s + P.output x) + P.target s +
    ∑ i, P.word s i * ((P.dataLeft₀ s i + P.dataLeft x i) *
      (P.dataRight₀ s i + P.dataRight x i))

private def PayloadPolynomial.polar {S U J I : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Fintype J] [Fintype I] (P : PayloadPolynomial S U J I) (s : S) (u v : U) : ZMod 2 :=
  (dotProduct (P.left u) (P.right v) + dotProduct (P.left v) (P.right u)) +
    ∑ i, P.word s i * (P.dataLeft u i * P.dataRight v i + P.dataLeft v i * P.dataRight u i)

private lemma PayloadPolynomial.second_error {S U J I : Type*} [AddCommGroup U]
    [Module (ZMod 2) U] [Fintype J] [Fintype I] (P : PayloadPolynomial S U J I)
    (s : S) (x u v : U) : payloadSecond (P.error s) x u v = P.polar s u v := by
  unfold PayloadPolynomial.error PayloadPolynomial.polar
  simp only [dotProduct, Pi.add_apply,
    payloadSecond_add, payloadSecond_sum, payloadSecond_weight, payloadSecond_const,
    payloadSecond_linear, payloadSecond_coordinateMul, Finset.sum_add_distrib, add_zero]

private noncomputable def payloadSign (a : ZMod 2) : ℝ := if a = 1 then -1 else 1

private lemma payloadBinary (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma payloadOddFour (a b c d : ZMod 2) (h : a - b - c + d = 1) :
    payloadSign a + payloadSign b + payloadSign c + payloadSign d ≤ 2 := by
  rcases payloadBinary a with rfl | rfl <;> rcases payloadBinary b with rfl | rfl <;>
    rcases payloadBinary c with rfl | rfl <;> rcases payloadBinary d with rfl | rfl <;>
    first | (exfalso; revert h; decide)
          | norm_num [payloadSign, zero_ne_one]

-- A nonzero constant second difference forces a disagreement on every translated square.
private lemma payloadSecond_eq_zero_of_bias {U : Type*} [AddCommGroup U] [Fintype U]
    (f : U → ZMod 2) (u v : U) (c : ZMod 2)
    (hc : ∀ x, payloadSecond f x u v = c)
    (hb : (1 / 2 : ℝ) < (∑ x, payloadSign (f x)) / Fintype.card U) : c = 0 := by
  by_contra hn
  have h1 : c = 1 := (payloadBinary c).resolve_left hn
  let A : ℝ := ∑ x, payloadSign (f x)
  have hshift (w : U) : (∑ x, payloadSign (f (x + w))) = A :=
    Equiv.sum_comp (Equiv.addRight w) (fun x => payloadSign (f x))
  have hshift₂ : (∑ x, payloadSign (f (x + u + v))) = A := by
    simpa only [← add_assoc] using hshift (u + v)
  have htotal : A + A + A + A ≤ 2 * (Fintype.card U : ℝ) := by
    have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset U)) =>
      payloadOddFour _ _ _ _ ((hc x).trans h1))
    simpa [Finset.sum_add_distrib, hshift₂, hshift u, hshift v, A, mul_comm] using h
  have hcard : 0 < (Fintype.card U : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : U)⟩)
  have hlarge : (1 / 2 : ℝ) * Fintype.card U < A := (lt_div_iff₀ hcard).mp hb
  linarith

private lemma PayloadPolynomial.polar_eq_zero_of_bias {S U J I : Type*} [AddCommGroup U]
    [Module (ZMod 2) U] [Fintype U] [Fintype J] [Fintype I]
    (P : PayloadPolynomial S U J I) (s : S)
    (hb : (1 / 2 : ℝ) < (∑ x, payloadSign (P.error s x)) / Fintype.card U) (u v : U) :
    P.polar s u v = 0 :=
  payloadSecond_eq_zero_of_bias (P.error s) u v (P.polar s u v)
    (fun x => P.second_error s x u v) hb


private lemma chi_eq_payloadSign (u : F2) : chi u = payloadSign u := by
  simp only [chi, signBool, payloadSign, decide_eq_true_eq]
  split <;> norm_num

private def wordLinear {k m : ℕ} (A : Fin m → Vec k) (i : Fin m) : Vec k →ₗ[F2] F2 where
  toFun := fun v => words A v i
  map_add' x y := dotProduct_add (A i) x y
  map_smul' z x := dotProduct_smul z (A i) x

open scoped Affine in
private lemma columnSide_even {k m : ℕ} (A : Fin m → Vec k) (E : Finset (Vec k))
    (hne : E.Nonempty) (heven : Even E.card) (hsum : (∑ s ∈ E, s) = 0)
    (hmin : ∀ I : Finset (Vec k), I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ s ∈ I, s) ≠ 0) (i : Fin m) (b : F2) :
    Even (columnSide A E i b).card := by
  classical
  let f : Vec k →ᵃ[F2] F2 := (wordLinear A i).toAffineMap - AffineMap.const F2 (Vec k) b
  apply (selector_affine_indicator hne heven hsum hmin (Finset.filter_subset _ _)).mp
  refine ⟨f, ?_⟩
  intro s hs
  change words A s i - b = if s ∈ columnSide A E i b then 1 else 0
  simp only [columnSide, Finset.mem_filter, hs, true_and]
  rcases zmod2_cases (words A s i) with h | h <;> rcases zmod2_cases b with hb | hb <;>
    rw [h, hb] <;> decide

private lemma deficit_column {k m : ℕ} (A : Fin m → Vec k) (E : Finset (Vec k))
    (σ cov : E → ℝ) (hσ : ∀ v, σ v ≤ 1)
    (hcov : daCover (fun u v : E => adjacent A E u.val v.val) cov)
    {i : Fin m} {b : F2} (hne : (columnSide A E i b).Nonempty)
    (heven : Even (columnSide A E i b).card)
    (hhalf : ∀ v : E, words A v.val i ≠ b → σ v ≤ 1/2) :
    1 ≤ ∑ v, cov v * (1-σ v) := by
  classical
  let I : Finset E := Finset.univ.filter (fun v => words A v.val i ≠ b)
  let vv : E ↪ Vec k := Function.Embedding.subtype _
  have hmap : I.map vv = columnSide A E i b := by
    ext x
    simp only [Finset.mem_map, I, Finset.mem_filter, Finset.mem_univ, true_and, columnSide]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.property, hv⟩
    · rintro ⟨hx, hv⟩
      exact ⟨⟨x,hx⟩, hv, rfl⟩
  have hcard : I.card = (columnSide A E i b).card := by rw [← hmap, Finset.card_map]
  have hp : 0 < I.card := by rw [hcard]; exact Finset.card_pos.mpr hne
  have hEven : Even I.card := hcard ▸ heven
  have hh (v : E) (hv : v ∈ I) : σ v ≤ 1/2 := hhalf v (Finset.mem_filter.mp hv).2
  by_cases h4 : 4 ≤ I.card
  · exact deficit_at_four σ cov hσ hcov I h4 hh
  have h2 : I.card = 2 := by
    obtain ⟨t, ht⟩ := hEven
    omega
  obtain ⟨u,v,huv,huvI⟩ := Finset.card_eq_two.mp h2
  have hadj : adjacent A E u.val v.val := by
    refine ⟨fun he => huv (Subtype.ext he), i, b, ?_⟩
    rw [← hmap, huvI]
    simp [vv]
  apply deficit_at_pair σ cov hσ hcov.1 huv (1/2)
  · have := hh u (by simp [huvI])
    linarith
  · have := hh v (by simp [huvI])
    linarith
  · linarith [hcov.2.2 u v hadj]

private noncomputable def payloadPairs (m r : ℕ) : Vec (2*m+r) →ₗ[F2] (Fin m → F2 × F2) where
  toFun d i := (((pack m r).symm d).1 i, ((pack m r).symm d).2.1 i)
  map_add' x y := by funext i; simp
  map_smul' z x := by funext i; simp

private lemma payloadPairs_surjective (m r : ℕ) : Function.Surjective (payloadPairs m r) := by
  intro x
  refine ⟨pack m r (fun i => (x i).1, fun i => (x i).2, 0), ?_⟩
  funext i
  simp [payloadPairs]

private lemma residualSliceDeficit {k m r n : ℕ}
    (A : Fin m → Vec k) (E : Finset (Vec k)) (a : E)
    (heven : Even E.card) (hsum : (∑ s ∈ E, s) = 0)
    (hmin : ∀ I : Finset (Vec k), I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ s ∈ I, s) ≠ 0)
    (U : Submodule F2 (Vec (2*m+r)))
    (P : PayloadPolynomial E U (Fin n) (Fin m))
    (hword : P.word = fun s => words A s.val)
    (hcoords : ∀ (u : U) i, (P.dataLeft u i, P.dataRight u i) = payloadPairs m r u.val i)
    (ht : Module.finrank F2 U + (varyingOn A E a.val).card > 2*m+r)
    (cov : E → ℝ) (hcov : daCover (fun u v : E => adjacent A E u.val v.val) cov) :
    1 ≤ ∑ v, cov v * (1 - avg (fun d => chi (P.error v d))) := by
  classical
  let σ (v : E) := avg fun d => chi (P.error v d)
  let G : Set E := {v | 1/2 < σ v}
  have hs : ∀ v, σ v ≤ 1 := fun v => avg_le _ _ fun _ => chi_le_one _
  have hcol (i : Fin m) (hi : i ∈ varyingOn A E a.val) (b : F2)
      (hb : ∀ v ∈ G, words A v.val i = b) : 1 ≤ ∑ v, cov v * (1-σ v) := by
    apply deficit_column A E σ cov hs hcov (i := i) (b := b)
    · by_contra hn
      obtain ⟨s, hse, hsw⟩ := (Finset.mem_filter.mp hi).2
      have hsame (v : Vec k) (hv : v ∈ E) : words A v i = b := by
        by_contra hne
        exact hn ⟨v, Finset.mem_filter.mpr ⟨hv,hne⟩⟩
      exact hsw ((hsame s hse).trans (hsame a.val a.property).symm)
    · exact columnSide_even A E ⟨a.val,a.property⟩ heven hsum hmin i b
    · intro v hv
      exact le_of_not_gt (fun hg => hv (hb v hg))
  by_cases hG : G.Nonempty
  · obtain ⟨u, hu⟩ := hG
    let L : G → Fin m → F2 := fun v i => words A v.val.val i - words A u.val i
    have hpolar (v : G) (x y : U) :
        ∑ i, L v i * rrCross (payloadPairs m r x.val i) (payloadPairs m r y.val i) = 0 := by
      have hzero (s : E) (hs₀ : s ∈ G) : P.polar s x y = 0 := by
        apply P.polar_eq_zero_of_bias
        change (1/2 : ℝ) < σ s at hs₀
        simpa only [σ, avg, chi_eq_payloadSign] using hs₀
      have h₁ := hzero v.val v.property
      have h₂ := hzero u hu
      unfold PayloadPolynomial.polar at h₁ h₂
      rw [hword] at h₁ h₂
      have hc (i : Fin m) :
          rrCross (payloadPairs m r x.val i) (payloadPairs m r y.val i) =
            P.dataLeft x i * P.dataRight y i + P.dataLeft y i * P.dataRight x i := by
        rw [← hcoords x i, ← hcoords y i]
        simp only [rrCross]
        ring
      simp only [L, hc, sub_mul, Finset.sum_sub_distrib]
      linear_combination h₁ - h₂
    have hIso := rrCommonIso_codim (payloadPairs m r) (payloadPairs_surjective m r) U L
      (fun s x hx y hy => hpolar s ⟨x,hx⟩ ⟨y,hy⟩)
    rw [Module.finrank_fin_fun] at hIso
    let J := @Finset.filter (Fin m) (fun i => ∃ s : G, L s i ≠ 0)
      (fun _ => Classical.propDecidable _) Finset.univ
    change Module.finrank F2 U + J.card ≤ 2*m+r at hIso
    have hnot : ¬ varyingOn A E a.val ⊆ J := fun h => by
      have := Finset.card_le_card h
      omega
    obtain ⟨i, hi, hiJ⟩ := Finset.not_subset.mp hnot
    apply hcol i hi (words A u.val i)
    intro s hsG
    apply sub_eq_zero.mp
    by_contra hne
    apply hiJ
    exact (@Finset.mem_filter (Fin m) (fun j => ∃ z : G, L z j ≠ 0)
      (fun _ => Classical.propDecidable _) Finset.univ i).mpr
      ⟨Finset.mem_univ _, ⟨⟨s,hsG⟩, hne⟩⟩
  · obtain ⟨i, hi⟩ := Finset.card_pos.mp
      (show 0 < (varyingOn A E a.val).card by
        have := U.finrank_le
        rw [Module.finrank_fin_fun] at this
        omega)
    exact hcol i hi 0 (fun v hv => (hG ⟨v,hv⟩).elim)

private lemma convex_deficit {ι α : Type*} [Fintype ι] [Fintype α]
    (cov : α → ℝ) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hsum : (∑ i, μ i) = 1)
    (f : ι → α → ℝ) (hf : ∀ i, 1 ≤ ∑ s, cov s * (1 - f i s)) :
    1 ≤ ∑ s, cov s * (1 - ∑ i, μ i * f i s) := by
  have hc (s : α) : 1 - (∑ i, μ i * f i s) = ∑ i, μ i * (1-f i s) := by
    simp [mul_sub, Finset.sum_sub_distrib, hsum]
  calc
    1 = ∑ i, μ i * 1 := by simp [hsum]
    _ ≤ ∑ i, μ i * ∑ s, cov s * (1-f i s) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (hμ i))
    _ = ∑ s, cov s * (1 - ∑ i, μ i * f i s) := by
      simp_rw [hc, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

private def dotLinear {n : ℕ} (w : Vec n) : Vec n →ₗ[F2] F2 where
  toFun x := dotProduct w x
  map_add' := dotProduct_add w
  map_smul' z x := dotProduct_smul z w x

private lemma residualDeficit {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r)
    (A : Fin m → Vec k) (h : Vec k → F2) (E : Finset (Vec k)) (a : E)
    (heven : Even E.card) (hsum : (∑ s ∈ E, s) = 0)
    (hmin : ∀ I : Finset (Vec k), I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ s ∈ I, s) ≠ 0)
    (W : Submodule F2 (Vec n)) (z : Vec n) (D : Circuit)
    (tap : Fin n → ℕ) (hD : legalGates n D.gates)
    (hout : D.output < n + D.gates.length) (htap : ∀ j, tap j < n+D.gates.length)
    (ha : ∀ (s : E) d, point e s.val d - z ∈ W)
    (hcost : costGates D.gates < (varyingOn A E a.val).card)
    (cov : E → ℝ) (hcov : daCover (fun u v : E => adjacent A E u.val v.val) cov) :
    let pos (y : Vec n) (j : Fin n) := bitValue ((D.wires (bitsOf n y)).getD (tap j) false)
    1 ≤ ∑ s, cov s * (1 - leafScore e A h W z D pos s.val) := by
  classical
  intro pos
  obtain ⟨N, U, off, out, slope, hbudget, hpart, hwire⟩ := payloadSplit e D hD
  let d := 2*m+r
  let P (i : Fin N) : PayloadPolynomial E (U i) (Fin n) (Fin m) :=
    { left := LinearMap.pi fun j => (dotLinear (slope i (tap j))).comp (U i).subtype
      right := (liftData e).comp (U i).subtype
      output := (dotLinear (slope i D.output)).comp (U i).subtype
      dataLeft := LinearMap.pi fun j => (LinearMap.fst F2 F2 F2).comp
        ((LinearMap.proj j).comp ((payloadPairs m r).comp (U i).subtype))
      dataRight := LinearMap.pi fun j => (LinearMap.snd F2 F2 F2).comp
        ((LinearMap.proj j).comp ((payloadPairs m r).comp (U i).subtype))
      left₀ := fun s j => out i (tap j) s.val
      right₀ := fun s => point e s.val (off i s.val)
      output₀ := fun s => out i D.output s.val
      dataLeft₀ := fun s j => (payloadPairs m r (off i s.val) j).1
      dataRight₀ := fun s j => (payloadPairs m r (off i s.val) j).2
      target := fun s => h s.val
      word := fun s => words A s.val }
  have herr (i : Fin N) (s : E) (v : U i) :
      let dd := off i s.val + v.val
      let y := point e s.val dd
      bitValue (D.eval (bitsOf n y)) + dotProduct (pos y) y + phase (r := r) A h s.val dd =
        (P i).error s v := by
    intro dd y
    have hy : y = point e s.val (off i s.val) + liftData e v.val := by
      dsimp only [y, dd]
      simp only [point_eq,map_add]
      abel
    have ht (j : Fin n) :
        pos y j = out i (tap j) s.val + dotProduct (slope i (tap j)) v.val :=
      hwire i s.val v (tap j) (htap j)
    have ho : bitValue (D.eval (bitsOf n y)) =
        out i D.output s.val + dotProduct (slope i D.output) v.val :=
      hwire i s.val v D.output hout
    have hpos : pos y =
        (fun j => out i (tap j) s.val + dotProduct (slope i (tap j)) v.val) := funext ht
    have hph : phase (r := r) A h s.val dd =
        h s.val + ∑ j, words A s.val j *
          (((payloadPairs m r (off i s.val) j).1 + (payloadPairs m r v.val j).1) *
           ((payloadPairs m r (off i s.val) j).2 + (payloadPairs m r v.val j).2)) := by
      unfold phase
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [dd, map_add, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_assoc]
      rfl
    rw [ho, hpos, hy, hph]
    unfold PayloadPolynomial.error
    have hl : (P i).left₀ s + (P i).left v =
        (fun j => out i (tap j) s.val + dotProduct (slope i (tap j)) v.val) := by
      funext j
      rfl
    rw [hl]
    dsimp only [P, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Submodule.subtype_apply, LinearMap.proj_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      dotLinear]
    abel
  let μ (i : Fin N) := (Fintype.card (U i) : ℝ) / 2^d
  have hμ (i : Fin N) : 0 ≤ μ i := by dsimp [μ]; positivity
  have htot : ∑ i, μ i = 1 := sliceWeights U (fun i => off i 0) (hpart 0)
  have leaf (s : E) : leafScore e A h W z D pos s.val =
      ∑ i, μ i * avg (fun v => chi ((P i).error s v)) := by
    unfold leafScore
    simp_rw [if_pos (ha s _)]
    rw [avgSplit U (fun i => off i s.val) (hpart s.val)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact congrArg avg (funext fun v => congrArg chi (herr i s v))
  simp_rw [leaf]
  apply convex_deficit cov μ hμ htot
  intro i
  apply residualSliceDeficit A E a heven hsum hmin (U i) (P i) rfl (fun _ _ => rfl) _ cov hcov
  have hh := hbudget i
  omega

private lemma circuitDeficit {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r)
    (A : Fin m → Vec k) (h : Vec k → F2) (E : Finset (Vec k)) (a : E)
    (hc : 4 ≤ E.card) (heven : Even E.card) (hsum : (∑ s ∈ E, s) = 0)
    (hmin : ∀ I : Finset (Vec k), I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ s ∈ I, s) ≠ 0)
    (C : Circuit) (hC : legalGates (2*n) C.gates)
    (ht : costGates C.gates < (2*m+r)+(E.card-2)+(varyingOn A E a.val).card)
    (cov : E → ℝ) (hcov : daCover (fun u v : E => adjacent A E u.val v.val) cov) :
    1 ≤ ∑ s, cov s * (1 - score e A h C s.val) := by
  classical
  obtain ⟨N, rank, U, z, D, tap, _, hh, hp, heval⟩ :=
    decomp_835 n n C (show legalGates (n+n) C.gates by simpa only [two_mul] using hC)
  let pos (i : Fin N) (y : Vec n) (j : Fin n) :=
    bitValue ((D i).wires (bitsOf n y) |>.getD (tap i j) false)
  let μ (i : Fin N) := (Fintype.card (U i) : ℝ) / 2^n
  let W (i : Fin N) := orthoComp (U i)
  have hw (i : Fin N) : Module.finrank F2 (W i) = rank i := by
    have hdim := finrank_orthoComp (U i)
    have hm : Module.finrank F2 (U i) + rank i = n := (hh i).1
    dsimp [W]
    omega
  have hμ (i : Fin N) : 0 ≤ μ i := by dsimp [μ]; positivity
  have htot : ∑ i, μ i = 1 := sliceWeights U (fun i => pos i 0) (hp 0)
  have he (s : Vec k) : score e A h C s =
      ∑ i, μ i * leafScore e A h (W i) (z i) (D i) (pos i) s := by
    unfold score
    simp_rw [splitProfile C U z D pos hp heval]
    exact avgSum μ _
  simp_rw [he]
  apply convex_deficit cov μ hμ htot
  intro i
  let σ (s : E) := leafScore e A h (W i) (z i) (D i) (pos i) s.val
  have hσ (s : E) : σ s ≤ 1 := leaf_le_one e A h (W i) (z i) (D i) (pos i) s.val
  by_cases hfull : ∀ d, liftData e d ∈ W i
  · by_cases hsel : ∀ s : E, liftSel e s.val - z i ∈ W i
    · have hrank := fullLeafRank e (W i) (z i) E a.val a.property
        (fun s hs => hsel ⟨s,hs⟩) hfull
      rw [selector_affine_finrank hc heven hsum hmin, hw] at hrank
      have hbudget : costGates (D i).gates + rank i ≤ costGates C.gates := (hh i).2.2.1
      apply residualDeficit e A h E a heven hsum hmin (W i) (z i) (D i) (tap i)
        (hh i).2.1 ((hh i).2.2.2.1) ((hh i).2.2.2.2) _ _ cov hcov
      · intro s v
        exact (point_mem_iff e (W i) (z i) hfull s.val v).mpr (hsel s)
      · omega
    · push Not at hsel
      obtain ⟨s, hs⟩ := hsel
      obtain ⟨t, hst, ht'⟩ := missingPair e (W i) (z i) E hc heven hsum s hs
      have hz (v : E) (hv : liftSel e v.val - z i ∉ W i) : σ v = 0 := by
        unfold σ leafScore
        simp_rw [point_mem_iff e (W i) (z i) hfull, if_neg hv]
        simp [avg]
      apply deficit_at_pair σ cov hσ hcov.1 hst 1
      · simp [hz s hs]
      · simp [hz t ht']
      · simpa only [one_mul] using hcov.2.1 s t hst
  · push Not at hfull
    obtain ⟨v, hv⟩ := hfull
    exact deficit_at_four σ cov hσ hcov Finset.univ (by simpa using hc)
      (fun s _ => leaf_sparse_le_half e A h (W i) (z i) (D i) (pos i) v hv s.val)

private def isQuad {s : ℕ} (q : (Fin s → F2) → F2) : Prop :=
  ∃ (b : F2) (a : Fin s → F2) (M : Fin s → Fin s → F2), ∀ v,
    q v = b + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j

private lemma isQuad_const {s : ℕ} (b : F2) : isQuad (s := s) (fun _ => b) :=
  ⟨b, 0, fun _ _ => 0, fun _ => by simp⟩

private lemma isQuad_affine {s : ℕ} (a : Fin s → F2) (b : F2) :
    isQuad (s := s) (fun v => dotProduct a v + b) :=
  ⟨b, a, fun _ _ => 0, fun v => by simp [add_comm]⟩

private lemma isQuad_add {s : ℕ} {q1 q2 : (Fin s → F2) → F2} (h1 : isQuad q1) (h2 : isQuad q2) :
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

private lemma isQuad_mul_affine {s : ℕ} (u1 u2 : Fin s → F2) (c1 c2 : F2) :
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

private lemma isQuad_finset_sum {s : ℕ} {ι : Type*} (S : Finset ι) (f : ι → (Fin s → F2) → F2)
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


private lemma dot_appendVec {l m : ℕ} (u x : Vec l) (v y : Vec m) :
    dotProduct (appendVec u v) (appendVec x y) = dotProduct u x + dotProduct v y :=
  cubicDotProduct u x v y

private lemma linear_eval_sum {l : ℕ} (T : Vec l →ₗ[F2] F2) (u : Vec l) :
    T u = ∑ i, u i * T (Pi.single i 1) := by
  conv_lhs => rw [vec_eq_sum_single u, map_sum]
  simp only [map_smul, smul_eq_mul]

private lemma synthesizeFlat {n l t : ℕ} (a : Vec n) (B : Vec l →ₗ[F2] Vec n)
    (L : Vec n →ₗ[F2] Vec l) (q : Vec l → F2) (hq : isQuad q)
    (K : Fin t → Vec n →ₗ[F2] F2) (cU cV : Fin t → Vec n) (bU bV : Fin t → F2) :
    ∃ C : Circuit, legalGates (2*n) C.gates ∧ costGates C.gates ≤ l+t ∧
      ∀ x y : Vec n,
        let u := L (y + a)
        let y' := a + B u
        C.eval (bitsOf n x ++ bitsOf n y) =
          decide (dotProduct x y' + q u + ∑ j, K j y' *
            ((dotProduct (cU j) y + bU j) * (dotProduct (cV j) y + bV j)) = 1) := by
  obtain ⟨b, c, M, hq⟩ := hq
  have hcoord (i : Fin l) : ∃ w : Vec n, ∀ v, L v i = dotProduct w v :=
    linear_coord_dot ((LinearMap.proj i).comp L)
  choose row hrow using hcoord
  let v (i : Fin l) := B (Pi.single i (1 : F2))
  let vR (i : Fin l) := ∑ j : Fin l, M i j • row j
  let cR (i : Fin l) := c i + ∑ j, M i j * dotProduct (row j) a
  let wR (i : Fin l) (j : Fin t) := K j (v i)
  obtain ⟨C, hl, hc, he⟩ :=
    build_cubic_circuit (n+n) l t (appendVec a 0) (fun j => K j a) b
      (fun i => appendVec 0 (row i)) (fun i => appendVec (v i) (vR i))
      wR (fun i => dotProduct (row i) a) cR
      (fun j => appendVec 0 (cU j)) (fun j => appendVec 0 (cV j)) bU bV
  refine ⟨C, by simpa only [two_mul] using hl, hc, fun x y => ?_⟩
  intro u y'
  rw [bitsOf_appendVec]
  refine (he (appendVec x y)).trans ?_
  apply congrArg (fun z : F2 => decide (z = 1))
  simp only [dot_appendVec, zero_dotProduct, zero_add, add_zero]
  let aux (j : Fin t) := (dotProduct (cU j) y + bU j) * (dotProduct (cV j) y + bV j)
  have hL (i : Fin l) : dotProduct (row i) y + dotProduct (row i) a = u i := by
    rw [← dotProduct_add, ← hrow]
  have hR (i : Fin l) : dotProduct (vR i) y + (∑ j, M i j * dotProduct (row j) a) =
      ∑ j, M i j * u j := by
    simp only [vR, sum_dotProduct, smul_dotProduct, smul_eq_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hL, mul_add]
  have hz (i : Fin l) :
      dotProduct (v i) x + dotProduct (vR i) y + dotProduct (wR i) aux + cR i =
      dotProduct (v i) x + c i + (∑ j, M i j * u j) + dotProduct (wR i) aux := by
    dsimp only [cR]
    linear_combination hR i
  have hb : dotProduct x (B u) = ∑ i, u i * dotProduct (v i) x := by
    change ((dotLinear x).comp B) u = _
    rw [linear_eval_sum ((dotLinear x).comp B) u]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dotProduct_comm]
    rfl
  have hK (j : Fin t) : K j (B u) = ∑ i, u i * K j (v i) :=
    linear_eval_sum ((K j).comp B) u
  have haux : (∑ i : Fin l, u i * dotProduct (wR i) aux) =
      ∑ j, K j (B u) * aux j := by
    simp only [dotProduct, Finset.mul_sum, hK, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [wR]
    ring
  change dotProduct a x + dotProduct (fun j => K j a) aux + b +
      (∑ i, (dotProduct (row i) y + dotProduct (row i) a) *
        (dotProduct (v i) x + dotProduct (vR i) y + dotProduct (wR i) aux + cR i)) =
    dotProduct x y' + q u + ∑ j, K j y' * aux j
  simp_rw [hL, hz, mul_add, Finset.sum_add_distrib]
  have hl : (∑ i, u i * c i) = dotProduct c u :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hquad : (∑ i, u i * ∑ j, M i j * u j) =
      ∑ i, ∑ j, M i j * u i * u j := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hka : (∑ j, K j y' * aux j) =
      dotProduct (fun j => K j a) aux + ∑ j, K j (B u) * aux j := by
    simp only [y', map_add, add_mul, Finset.sum_add_distrib, dotProduct]
  rw [hl, hquad, haux, hka, hq u]
  unfold y'
  rw [dotProduct_add, hb, dotProduct_comm a x]
  ring

private lemma conditionalXScore {n : ℕ} (C : Circuit) (y y' : Vec n) (f v : F2)
    (hC : ∀ x : Vec n, C.eval (bitsOf n x ++ bitsOf n y) = decide (dotProduct x y' + f = 1)) :
    avg (fun x : Vec n =>
      if C.eval (bitsOf n x ++ bitsOf n y) = decide (dotProduct x y + v = 1)
      then (1:ℝ) else -1) = if y'=y then chi (f+v) else 0 := by
  have hterm (x : Vec n) :
      (if C.eval (bitsOf n x ++ bitsOf n y) = decide (dotProduct x y + v = 1)
      then (1:ℝ) else -1) = chi ((f+v) + dotProduct (y'+y) x) := by
    rw [agree_chi, hC x]
    change chi ((if decide (dotProduct x y' + f = 1) then (1 : F2) else 0) +
      (dotProduct x y+v)) = _
    rw [zmod2_decide_bool, add_dotProduct, dotProduct_comm y' x, dotProduct_comm y x]
    congr 1
    ring
  simp_rw [hterm, avgChiShift]
  by_cases h : y' = y
  · simp only [h, ↓reduceIte, zmod2_vec_add_self, zero_dotProduct]
    have hchi : chi 0 = 1 := by norm_num [chi, signBool, show (0:F2) ≠ 1 by decide]
    have hconst : avg (fun _ : Vec n => (1:ℝ)) = 1 := by
      have hcard : (Fintype.card (Vec n) : ℝ) ≠ 0 := by positivity
      simp [avg, hcard]
    rw [hchi, hconst, mul_one]
  · have hn : y'+y ≠ 0 := by
      intro hz
      apply h
      apply add_right_cancel (b := y)
      rw [hz, zmod2_vec_add_self]
    have hz := congrArg (Int.cast : ℤ → ℝ) (sum_sign_dot_univ (y'+y) hn)
    unfold avg chi at *
    rw [if_neg h, ← Int.cast_sum, hz, Int.cast_zero, zero_div, mul_zero]

private lemma quad_product {l : ℕ} (L R : Vec l →ₗ[F2] F2) (b c a : F2) :
    isQuad (fun x => a * ((L x + b) * (R x + c))) := by
  obtain ⟨p, hp⟩ := linear_coord_dot L
  obtain ⟨q, hq⟩ := linear_coord_dot R
  have he : (fun x => a * ((L x + b) * (R x + c))) =
      (fun x => (dotProduct (a • p) x + a*b) * (dotProduct q x+c)) := by
    funext x
    rw [hp, hq, smul_dotProduct, smul_eq_mul]
    ring
  rw [he]
  exact isQuad_mul_affine _ _ _ _

private def SelectorQuad {k : ℕ} (f : Vec k → F2) : Prop :=
  ∀ (l : ℕ) (a : Vec k) (B : Vec l →ₗ[F2] Vec k), isQuad (fun x => f (a+B x))

open scoped Affine in
private lemma affine_as_linear_add {k : ℕ} (f : Vec k →ᵃ[F2] F2) (v : Vec k) :
    f v = f.linear v + f 0 := by
  simpa using f.map_vadd (0 : Vec k) v

open scoped Affine in
private lemma selectorQuad_affine {k : ℕ} (f : Vec k →ᵃ[F2] F2) : SelectorQuad f := by
  intro l a B
  obtain ⟨c, hc⟩ := linear_coord_dot (f.linear.comp B)
  have he : (fun x => f (a+B x)) = fun x => dotProduct c x + (f.linear a + f 0) := by
    funext x
    rw [affine_as_linear_add, map_add, ← hc]
    change f.linear a + f.linear (B x) + f 0 = f.linear (B x) + (f.linear a + f 0)
    ring
  rw [he]
  exact isQuad_affine _ _

open scoped Affine in
private lemma selectorQuad_sum {k : ℕ} {I : Type*} [Fintype I]
    (a : I → F2) (F G : I → (Vec k →ᵃ[F2] F2)) :
    SelectorQuad (fun s => ∑ i, a i * (F i s * G i s)) := by
  intro l z B
  apply isQuad_finset_sum
  intro i _
  convert quad_product ((F i).linear.comp B) ((G i).linear.comp B)
    ((F i).linear z + F i 0) ((G i).linear z + G i 0) (a i) using 1
  funext x
  rw [affine_as_linear_add (F i), affine_as_linear_add (G i), map_add, map_add]
  simp only [LinearMap.comp_apply]
  ring

private def selProjection {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r) :
    Vec n →ₗ[F2] Vec k := (LinearMap.fst F2 (Vec k) (Data m r)).comp e.toLinearMap

private def pairLeft {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r) (i : Fin m) :
    Vec n →ₗ[F2] F2 where
  toFun y := (e y).2.1 i
  map_add' x y := by simp
  map_smul' c y := by simp

private def pairRight {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r) (i : Fin m) :
    Vec n →ₗ[F2] F2 where
  toFun y := (e y).2.2.1 i
  map_add' x y := by simp
  map_smul' c y := by simp

open Classical in
private lemma upperOnSelector {k m r n l : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r)
    (A : Fin m → Vec k) (h : Vec k → F2) (E : Finset (Vec k))
    (s₀ : Vec k) (B : Vec l →ₗ[F2] Vec k) (hB : Function.Injective B)
    (h' : Vec k → F2) (hq : SelectorQuad h')
    (hh : ∀ s ∈ E, (∃ u, s = s₀ + B u) → h' s = h s)
    (I : Finset (Fin m)) (β : Fin m → F2) :
    ∃ C : Circuit, legalGates (2*n) C.gates ∧ costGates C.gates ≤ (2*m+r)+l+I.card ∧
    ∀ s ∈ E,
      score e A h C s = if ∃ u, s = s₀+B u then
        avg (fun d => chi (∑ j, if j ∈ I then 0 else
          (words A s j + β j) * ((payloadPairs m r d j).1 * (payloadPairs m r d j).2)))
      else 0 := by
  let d := 2*m+r
  let a := liftSel e s₀
  let T : Vec (l+d) →ₗ[F2] Vec n := e.symm.toLinearMap.comp
    ((B.comp (headLinear l d)).prod ((pack m r).symm.toLinearMap.comp (tailLinear l d)))
  have ht (u : Vec l) (v : Vec d) : T (appendVec u v) = point e (B u) v := by
    change e.symm (B (fun j => Fin.addCases u v (j.castAdd d)),
      (pack m r).symm (fun j => Fin.addCases u v (j.natAdd l))) = _
    simp [point]
  have hinj : Function.Injective T := by
    intro v w hvw
    have he := e.symm.injective hvw
    have hL := hB (congrArg Prod.fst he)
    have hR := (pack m r).symm.injective (congrArg Prod.snd he)
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact congrFun hL j
    · exact congrFun hR j
  obtain ⟨L, hLT⟩ := linear_map_left_inv T hinj
  let q (u : Vec (l+d)) := h' (selProjection e (a+T u)) +
    ∑ j, β j * (pairLeft e j (a+T u) * pairRight e j (a+T u))
  have hquad : isQuad q := by
    apply isQuad_add
    · simpa only [map_add, LinearMap.comp_apply] using
        hq (l+d) (selProjection e a) ((selProjection e).comp T)
    · apply isQuad_finset_sum
      intro j _
      simpa only [map_add, LinearMap.comp_apply, add_comm] using
        quad_product ((pairLeft e j).comp T) ((pairRight e j).comp T)
          (pairLeft e j a) (pairRight e j a) (β j)
  let idx : Fin I.card ≃ I := (Fintype.equivFinOfCardEq (Fintype.card_coe I)).symm
  let A₁ (j : Fin I.card) := (wordLinear A (idx j).val).comp (selProjection e)
  let A₂ (j : Fin I.card) := pairRight e (idx j).val
  have hU (j : Fin I.card) := linear_coord_dot (A₁ j)
  have hV (j : Fin I.card) := linear_coord_dot (A₂ j)
  choose cU hU using hU
  choose cV hV using hV
  obtain ⟨C, hC, hc, he⟩ := synthesizeFlat a T L q hquad
    (fun j => pairLeft e (idx j).val) cU cV (fun j => β (idx j).val) (fun _ => 0)
  refine ⟨C, hC, by omega, fun s hs => ?_⟩
  let y (v : Vec d) := point e s v
  let proj (v : Vec d) := a+T (L (y v+a))
  have hfix (v : Vec d) : proj v = y v ↔ ∃ u, s = s₀+B u := by
    constructor
    · intro hp
      refine ⟨headLinear l d (L (y v+a)), ?_⟩
      have h₁ : selProjection e (y v) = s := by simp [y, point, selProjection]
      have h₂ : selProjection e (proj v) = s₀ + B (headLinear l d (L (y v+a))) := by
        unfold proj
        rw [map_add]
        change (e (e.symm (s₀,0))).1 + (e (e.symm
          (B (headLinear l d (L (y v+a))), (pack m r).symm (tailLinear l d (L (y v+a)))))).1 = _
        simp
      rw [← h₁, ← h₂, hp]
    · rintro ⟨u, hu⟩
      have hy : y v = a+T (appendVec u v) := by
        rw [ht]
        simp only [a, y, point_eq, map_add, hu]
        abel
      unfold proj
      rw [hy]
      have heq : a + T (appendVec u v) + a = T (appendVec u v) := by
        calc _ = (a+a)+T (appendVec u v) := by abel
             _ = _ := by rw [zmod2_vec_add_self, zero_add]
      rw [heq,hLT]
  have hf (v : Vec d) :
      avg (fun x : Vec n => if C.eval (bitsOf n x ++ bitsOf n (y v)) =
        decide (dotProduct x (y v)+phase (r := r) A h s v = 1) then (1:ℝ) else -1) =
      if ∃ u, s = s₀+B u then chi (∑ j, if j∈I then 0 else
        (words A s j+β j)*((payloadPairs m r v j).1*(payloadPairs m r v j).2)) else 0 := by
    let f := q (L (y v+a)) + ∑ j, pairLeft e (idx j).val (proj v) *
      ((dotProduct (cU j) (y v)+β (idx j).val)*(dotProduct (cV j) (y v)+0))
    have hEval (x : Vec n) : C.eval (bitsOf n x ++ bitsOf n (y v)) =
        decide (dotProduct x (proj v)+f = 1) := by
      refine (he x (y v)).trans (congrArg (fun t : F2 => decide (t = 1)) ?_)
      dsimp only [proj, f]
      ring
    rw [conditionalXScore C (y v) (proj v) f _ hEval]
    by_cases hp : ∃ u, s = s₀+B u
    · rw [if_pos ((hfix v).mpr hp), if_pos hp]
      have hy := (hfix v).mpr hp
      have hq' : q (L (y v+a)) = h' s + ∑ j, β j *
          (pairLeft e j (y v) * pairRight e j (y v)) := by
        change h' (selProjection e (proj v)) +
          ∑ j, β j * (pairLeft e j (proj v) * pairRight e j (proj v)) = _
        rw [hy]
        simp [selProjection,y,point]
      have hpair (j : Fin m) :
          (pairLeft e j (y v), pairRight e j (y v)) = payloadPairs m r v j := by
        simp [pairLeft,pairRight,y,point,payloadPairs]
      have hw (j : Fin I.card) : dotProduct (cU j) (y v) = words A s (idx j).val := by
        rw [← hU]
        simp [A₁,selProjection,y,point]
        rfl
      have hb (j : Fin I.card) : dotProduct (cV j) (y v) = pairRight e (idx j).val (y v) :=
        (hV j (y v)).symm
      unfold f
      simp_rw [hq', hh s hs hp, hy, hw, hb, add_zero]
      congr 1
      have hinner :
          (∑ j, pairLeft e (idx j).val (y v) *
            ((words A s (idx j).val+β (idx j).val)*pairRight e (idx j).val (y v))) =
          ∑ j ∈ I, (words A s j+β j) * (pairLeft e j (y v)*pairRight e j (y v)) := by
        rw [← Equiv.sum_comp idx.symm]
        simp only [idx.apply_symm_apply]
        rw [Finset.sum_coe_sort I (fun j => pairLeft e j (y v) *
          ((words A s j+β j)*pairRight e j (y v)))]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hinner, phase]
      have hfilter : (∑ j ∈ I, (words A s j+β j)*(pairLeft e j (y v)*pairRight e j (y v))) =
          (∑ j, if j∈I then (words A s j+β j)*(pairLeft e j (y v)*pairRight e j (y v)) else 0) := by
        rw [← Finset.sum_filter]
        simp
      rw [hfilter]
      have hz : h s + h s = 0 := by rcases zmod2_cases (h s) with h₀|h₀ <;> rw [h₀] <;> decide
      let f₁ := ∑ j, β j * (pairLeft e j (y v)*pairRight e j (y v))
      let f₂ := ∑ j, if j∈I then (words A s j+β j)*(pairLeft e j (y v)*pairRight e j (y v)) else 0
      let f₃ := ∑ j, words A s j * ((pack m r).symm v).1 j * ((pack m r).symm v).2.1 j
      change (h s + f₁ + f₂) + (h s + f₃) = _
      rw [show (h s + f₁ + f₂) + (h s + f₃) = (h s+h s)+(f₁+f₂+f₃) by abel, hz, zero_add]
      dsimp only [f₁,f₂,f₃]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hleft := congrArg Prod.fst (hpair j)
      have hright := congrArg Prod.snd (hpair j)
      change pairLeft e j (y v) = _ at hleft
      change pairRight e j (y v) = _ at hright
      rw [hleft,hright]
      change _ + _ + words A s j * (payloadPairs m r v j).1 * (payloadPairs m r v j).2 = _
      by_cases hi : j∈I
      · simp only [hi, ↓reduceIte]
        have htwo (z : F2) : z+z=0 := by rcases zmod2_cases z with h|h <;> rw [h] <;> decide
        linear_combination htwo (words A s j * (payloadPairs m r v j).1 * (payloadPairs m r v j).2) +
          htwo (β j * (payloadPairs m r v j).1 * (payloadPairs m r v j).2)
      · simp only [hi, ↓reduceIte]
        ring
    · rw [if_neg (fun h => hp ((hfix v).mp h)), if_neg hp]
  change avg (fun v : Vec d => avg (fun x : Vec n =>
    if C.eval (bitsOf n x ++ bitsOf n (y v)) =
      decide (dotProduct x (y v)+phase (r := r) A h s v = 1) then (1:ℝ) else -1)) = _
  simp_rw [hf]
  split_ifs
  · rfl
  · simp [avg]

section UpperSelectorCharts

open scoped Affine

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq V]

omit [DecidableEq V] in
/-- Coordinates on an affine subspace whose anchor is already chosen. -/
private theorem selector_chart [Module.Finite (ZMod 2) V]
    (H : AffineSubspace (ZMod 2) V) {a : V} (ha : a ∈ H) {d : ℕ}
    (hdim : Module.finrank (ZMod 2) H.direction = d) :
    ∃ B : (Fin d → ZMod 2) →ₗ[ZMod 2] V, Function.Injective B ∧
      ∀ v : V, (∃ u, v = a + B u) ↔ v ∈ H := by
  let e := (Module.finBasisOfFinrankEq (R := ZMod 2) (M := H.direction) hdim).equivFun.symm
  let B : (Fin d → ZMod 2) →ₗ[ZMod 2] V := H.direction.subtype.comp e.toLinearMap
  refine ⟨B, fun x y h => e.injective (Subtype.ext h), fun v => ?_⟩
  change (∃ u, v = a + (e u : V)) ↔ v ∈ H
  constructor
  · rintro ⟨u, rfl⟩
    rw [add_comm]
    exact AffineSubspace.vadd_mem_of_mem_direction (e u).property ha
  · intro hv
    let w : H.direction := ⟨v - a, AffineSubspace.vsub_mem_direction hv ha⟩
    refine ⟨e.symm w, ?_⟩
    rw [e.apply_symm_apply]
    change v = a + (v - a)
    abel

/-- The full selector set has an injective affine chart of dimension `E.card - 2`. -/
private theorem selector_full_chart [Module.Finite (ZMod 2) V] {E : Finset V}
    (hcard : 4 ≤ E.card) (heven : Even E.card) (hsum : (∑ v ∈ E, v) = 0)
    (hminimal : ∀ I : Finset V, I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ v ∈ I, v) ≠ 0) :
    ∃ a ∈ E, ∃ B : (Fin (E.card - 2) → ZMod 2) →ₗ[ZMod 2] V,
      Function.Injective B ∧ ∀ v ∈ E, ∃ u, v = a + B u := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < E.card by omega)
  obtain ⟨B, hB, hchart⟩ := selector_chart (affineSpan (ZMod 2) (E : Set V))
    (mem_affineSpan _ ha) (selector_affine_finrank hcard heven hsum hminimal)
  exact ⟨a, ha, B, hB, fun v hv => (hchart v).mpr (mem_affineSpan _ hv)⟩

/-- The affine span of the pair complement has dimension `E.card - 3` and misses
both removed selectors, as witnessed by the affine pair indicator. -/
private theorem selector_pair_complement_chart [Module.Finite (ZMod 2) V] {E : Finset V}
    {s t : V} (hs : s ∈ E) (ht : t ∈ E) (hst : s ≠ t)
    (hcard : 4 ≤ E.card) (heven : Even E.card) (hsum : (∑ v ∈ E, v) = 0)
    (hminimal : ∀ I : Finset V, I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ v ∈ I, v) ≠ 0) :
    ∃ a ∈ E, a ≠ s ∧ a ≠ t ∧
      ∃ B : (Fin (E.card - 3) → ZMod 2) →ₗ[ZMod 2] V,
        Function.Injective B ∧ ∀ v ∈ E, (∃ u, v = a + B u) ↔ v ≠ s ∧ v ≠ t := by
  let I := (E.erase s).erase t
  have hIts : t ∈ E.erase s := Finset.mem_erase.mpr ⟨hst.symm, ht⟩
  have hIcard : I.card = E.card - 2 := by
    dsimp only [I]
    rw [Finset.card_erase_of_mem hIts, Finset.card_erase_of_mem hs]
    omega
  have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
  have hind : AffineIndepOn (ZMod 2) id ((E.erase s : Finset V) : Set V) :=
    selector_affineIndependent_erase hs hminimal
  have hindI : AffineIndepOn (ZMod 2) id (I : Set V) :=
    hind.mono (Finset.erase_subset _ _)
  let H := affineSpan (ZMod 2) (I : Set V)
  have hdim : Module.finrank (ZMod 2) H.direction = E.card - 3 := by
    dsimp only [H]
    rw [direction_affineSpan, hindI.finrank_vectorSpan I.finite_toSet hIne.to_set,
      Set.ncard_coe_finset, hIcard]
    omega
  obtain ⟨a, ha⟩ := hIne
  have haH : a ∈ H := mem_affineSpan _ ha
  have has := Finset.mem_erase.mp (Finset.mem_erase.mp ha).2
  have hat := (Finset.mem_erase.mp ha).1
  obtain ⟨B, hB, hchart⟩ := selector_chart H haH hdim
  obtain ⟨ℓ, hℓ⟩ := selector_affine_pair hs ht hst heven hsum hminimal
  have hzero : H ≤ ({0} : AffineSubspace (ZMod 2) (ZMod 2)).comap ℓ := by
    apply affineSpan_le_of_subset_coe
    intro v hv
    rcases Finset.mem_erase.mp hv with ⟨hvt, hv⟩
    rcases Finset.mem_erase.mp hv with ⟨hvs, hvE⟩
    rw [SetLike.mem_coe, AffineSubspace.mem_comap, AffineSubspace.mem_singleton_iff]
    simp [hℓ v hvE, hvs, hvt]
  refine ⟨a, has.2, has.1, hat, B, hB, fun v hv => ?_⟩
  rw [hchart v]
  constructor
  · intro hvH
    have hz : ℓ v = 0 := (AffineSubspace.mem_singleton_iff _ _).mp
      (AffineSubspace.mem_comap.mp (hzero hvH))
    refine ⟨fun hvs => ?_, fun hvt => ?_⟩
    · rw [hℓ v hv, ite_eq_left (Or.inl hvs)] at hz
      exact one_ne_zero hz
    · rw [hℓ v hv, ite_eq_left (Or.inr hvt)] at hz
      exact one_ne_zero hz
  · rintro ⟨hvs, hvt⟩
    exact mem_affineSpan _ (Finset.mem_erase.mpr ⟨hvt, Finset.mem_erase.mpr ⟨hvs, hv⟩⟩)

/-- Changing the phase at one discarded selector makes its parity even, so the
original phase on all other selectors has an affine extension. -/
private theorem selector_phase_erase {E : Finset V} {s : V} (hs : s ∈ E)
    (heven : Even E.card) (hsum : (∑ v ∈ E, v) = 0)
    (hminimal : ∀ I : Finset V, I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ v ∈ I, v) ≠ 0) (h : V → ZMod 2) :
    ∃ f : V →ᵃ[ZMod 2] ZMod 2, ∀ v ∈ E, v ≠ s → f v = h v := by
  let h' : V → ZMod 2 := fun v => if v = s then -(∑ x ∈ E.erase s, h x) else h v
  have hrest : (∑ x ∈ E.erase s, h' x) = ∑ x ∈ E.erase s, h x := by
    apply Finset.sum_congr rfl
    intro v hv
    simp [h', (Finset.mem_erase.mp hv).1]
  have hphase : (∑ v ∈ E, h' v) = 0 := by
    rw [← E.sum_erase_add h' hs, hrest]
    simp only [h', ite_eq_left rfl, add_neg_cancel]
  obtain ⟨f, hf⟩ := (selector_affine_interpolation ⟨s, hs⟩ heven hsum hminimal h').mpr hphase
  exact ⟨f, fun v hv hvs => by simpa [h', hvs] using hf v hv⟩

end UpperSelectorCharts

private def daPairDeficit {α : Type*} [DecidableEq α] (u v : α) (a : ℝ) (s : α) : ℝ :=
  if s ∈ ({u, v} : Finset α) then a else 0

private theorem da_sum_pair_deficit {α : Type*} [Fintype α] [DecidableEq α]
    {u v : α} (huv : u ≠ v) (a : ℝ) (l : α → ℝ) :
    (∑ s, l s * daPairDeficit u v a s) = (l u + l v) * a := by
  simp only [daPairDeficit, mul_ite, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_insert]
  · rw [Finset.sum_singleton, add_mul]
  · simpa using huv

private theorem da_mix_deficit {A : Type*} [Fintype A] (p s : A → ℝ)
    (hp : (∑ i, p i) = 1) : (∑ i, p i * (1 - s i)) = 1 - ∑ i, p i * s i := by
  simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib, hp]

private theorem da_atom_mixture {α C : Type*} [Fintype α] [DecidableEq α]
    (adj : α → α → Prop) (hsym : ∀ ⦃u v⦄, adj u v → adj v u) (hirr : ∀ v, ¬adj v v)
    (w : α → ℝ) (hw : ∀ v, 0 < w v) (hother : ∀ v : α, ∃ u, u ≠ v) (hne : Nonempty α)
    (fits : C → Prop) (score : C → α → ℝ)
    (hlower : ∀ (c : C), fits c → ∀ l, daCover adj l → 1 ≤ ∑ s, l s * (1 - score c s))
    (hpair : ∀ u v, u ≠ v → ∃ c, fits c ∧ ∀ s, 1 - score c s = daPairDeficit u v 1 s)
    (hedge : ∀ u v, adj u v → ∃ c, fits c ∧ ∀ s, 1 - score c s = daPairDeficit u v (1 / 2) s) :
    ∃ b, daSaving adj w b ∧ (∀ z, daSaving adj w z → z ≤ b) ∧ b < daMass w Finset.univ ∧
      ∀ q : ℝ, (∃ (N : ℕ) (c : Fin N → C) (p : Fin N → ℝ),
        (∀ i, fits (c i) ∧ 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
        ∀ s, 1 - (∑ i, p i * score (c i) s) ≤ q * w s) ↔ 1 ≤ q * (daMass w Finset.univ - b) := by
  classical
  obtain ⟨b, hbs, hbmax, hb⟩ := da_saving_maximum adj w hw hother hne
  obtain ⟨hmin, l, hl, hlval⟩ := da_cover_minimum hsym hirr hw hbs hbmax
  refine ⟨b, hbs, hbmax, hb, fun q => ⟨?_, ?_⟩⟩
  · rintro ⟨N, c, p, hcp, hp, hbudget⟩
    have hswap : (∑ i, p i * ∑ s, l s * (1 - score (c i) s)) =
        ∑ s, l s * ∑ i, p i * (1 - score (c i) s) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
    calc
      1 = ∑ i, p i * 1 := by simpa using hp.symm
      _ ≤ ∑ i, p i * ∑ s, l s * (1 - score (c i) s) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlower _ (hcp i).1 l hl) (hcp i).2
      _ = ∑ s, l s * ∑ i, p i * (1 - score (c i) s) := hswap
      _ ≤ ∑ s, l s * (q * w s) := by
        apply Finset.sum_le_sum
        intro s _
        rw [da_mix_deficit p (fun i => score (c i) s) hp]
        exact mul_le_mul_of_nonneg_left (hbudget s) (hl.1 s)
      _ = q * (daMass w Finset.univ - b) := by
        rw [← hlval, Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
  · intro hqM
    have hq : 0 < q := by
      by_contra! h
      linarith [mul_nonpos_of_nonpos_of_nonneg h (sub_pos.mpr hb).le]
    let A := {a : α × α // a.1 ≠ a.2} ⊕ {a : α × α // adj a.1 a.2}
    let d : A → α → ℝ := Sum.elim
      (fun a => daPairDeficit a.1.1 a.1.2 1) (fun a => daPairDeficit a.1.1 a.1.2 (1 / 2))
    have hatoms (l' : α → ℝ) (hnn : ∀ s, 0 ≤ l' s)
        (hc : ∀ a, 1 ≤ ∑ s, l' s * d a s) : daMass w Finset.univ - b ≤ ∑ s, l' s * w s := by
      have hcov : daCover adj l' := by
        refine ⟨hnn, ?_, ?_⟩
        · intro u v huv
          have h := hc (Sum.inl ⟨(u,v), huv⟩)
          change 1 ≤ ∑ s, l' s * daPairDeficit u v 1 s at h
          rwa [da_sum_pair_deficit huv, mul_one] at h
        · intro u v huv
          have hneuv : u ≠ v := fun h => hirr v (h ▸ huv)
          have h := hc (Sum.inr ⟨(u,v), huv⟩)
          change 1 ≤ ∑ s, l' s * daPairDeficit u v (1 / 2) s at h
          rw [da_sum_pair_deficit hneuv] at h
          linarith
      simpa only [mul_comm] using hmin l' hcov
    obtain ⟨p, hp₀, hp₁, hpbound⟩ := finite_atom_packing d w (fun s => (hw s).le) hatoms hq hqM
    have hc : ∀ a : A, ∃ c, fits c ∧ ∀ s, 1 - score c s = d a s := by
      rintro (⟨⟨u,v⟩, huv⟩ | ⟨⟨u,v⟩, huv⟩)
      · exact hpair u v huv
      · exact hedge u v huv
    choose c hc using hc
    let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
    have hsum : (∑ i, p (e i)) = 1 := (e.sum_comp p).trans hp₁
    refine ⟨_, c ∘ e, p ∘ e, fun i => ⟨(hc (e i)).1, hp₀ (e i)⟩, hsum, fun s => ?_⟩
    change 1 - (∑ i, p (e i) * score (c (e i)) s) ≤ q * w s
    rw [← da_mix_deficit (fun i => p (e i)) (fun i => score (c (e i)) s) hsum]
    calc
      (∑ i, p (e i) * (1 - score (c (e i)) s)) = ∑ i, p (e i) * d (e i) s :=
        Finset.sum_congr rfl fun i _ => congrArg (p (e i) * ·) ((hc (e i)).2 s)
      _ = ∑ a, p a * d a s := e.sum_comp (fun a => p a * d a s)
      _ ≤ q * w s := hpbound s

private lemma avg_const_real {α : Type*} [Fintype α] [Nonempty α] (t : ℝ) :
    avg (fun _ : α => t) = t := by
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by positivity
  simp [avg, mul_comm, hcard]

private lemma chi_zero : chi 0 = 1 := by norm_num [chi, signBool, show (0:F2) ≠ 1 by decide]
private lemma chi_one : chi 1 = -1 := by norm_num [chi, signBool]

private lemma avg_chi_linear_zero {d : ℕ} (L : Vec d →ₗ[F2] F2) (v : Vec d) (hv : L v = 1) :
    avg (fun x => chi (L x)) = 0 := by
  have h := avgShift (fun x => chi (L x)) v
  simp_rw [map_add, hv, chi_add, chi_one, mul_neg_one, avg, Finset.sum_neg_distrib,
    neg_div] at h
  unfold avg
  linarith

private lemma avg_payload_pair {m r : ℕ} (i : Fin m) :
    avg (fun d : Vec (2*m+r) =>
      chi ((payloadPairs m r d i).1 * (payloadPairs m r d i).2)) = 1/2 := by
  classical
  let L : Vec (2*m+r) →ₗ[F2] F2 := (LinearMap.fst F2 F2 F2).comp
    ((LinearMap.proj i).comp (payloadPairs m r))
  let R : Vec (2*m+r) →ₗ[F2] F2 := (LinearMap.snd F2 F2 F2).comp
    ((LinearMap.proj i).comp (payloadPairs m r))
  obtain ⟨l, hl⟩ := payloadPairs_surjective m r (fun _ => (1,0))
  obtain ⟨r₀, hr⟩ := payloadPairs_surjective m r (fun _ => (0,1))
  have hL : L l = 1 := congrArg (fun f => (f i).1) hl
  have hR : R r₀ = 1 := congrArg (fun f => (f i).2) hr
  have hLR : (L+R) l = 1 := by
    change (payloadPairs m r l i).1+(payloadPairs m r l i).2 = 1
    simp [hl]
  have hl₀ := avg_chi_linear_zero L l hL
  have hr₀ := avg_chi_linear_zero R r₀ hR
  have hb₀ := avg_chi_linear_zero (L+R) l hLR
  have hFourier (x y : F2) :
      chi (x*y) = (1 + chi x + chi y - chi (x+y))/2 := by
    rcases zmod2_cases x with rfl|rfl <;> rcases zmod2_cases y with rfl|rfl <;>
      simp [chi_zero, chi_one, show (1:F2)+1=0 by decide] <;> norm_num
  change avg (fun d => chi (L d * R d)) = _
  simp_rw [hFourier]
  unfold avg at *
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  have hp : (Fintype.card (Vec (2*m+r)) : ℝ) ≠ 0 := by positivity
  have h₁ := (div_eq_zero_iff.mp hl₀).resolve_right hp
  have h₂ := (div_eq_zero_iff.mp hr₀).resolve_right hp
  have h₃ := (div_eq_zero_iff.mp hb₀).resolve_right hp
  change (∑ j, chi (L j)) = 0 at h₁
  change (∑ j, chi (R j)) = 0 at h₂
  change (∑ j, chi (L j + R j)) = 0 at h₃
  rw [h₁,h₂,h₃]
  field_simp <;> ring

private lemma word_constant_of_not_varying {k m : ℕ} {A : Fin m → Vec k}
    {E : Finset (Vec k)} {a s : Vec k} {i : Fin m} (hs : s ∈ E)
    (hi : i ∉ varyingOn A E a) : words A s i = words A a i := by
  classical
  by_contra hn
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,s,hs,hn⟩)

private lemma zmod2_self_cancel (v : F2) : v+v=0 := by
  rcases zmod2_cases v with rfl|rfl <;> decide

private lemma zmod2_add_eq_one_of_ne (a b : F2) (h : a ≠ b) : a+b=1 := by
  rcases zmod2_cases a with rfl|rfl <;> rcases zmod2_cases b with rfl|rfl <;>
    first | exact (h rfl).elim | decide

private lemma regularUpperError {k m r : ℕ} {A : Fin m → Vec k} {E : Finset (Vec k)}
    {a s : Vec k} (hs : s ∈ E) :
    avg (fun d : Vec (2*m+r) => chi (∑ j, if j ∈ varyingOn A E a then 0 else
      (words A s j + words A a j) * ((payloadPairs m r d j).1 * (payloadPairs m r d j).2))) = 1 := by
  have he (d : Vec (2*m+r)) :
      (∑ j, if j ∈ varyingOn A E a then 0 else
        (words A s j + words A a j) * ((payloadPairs m r d j).1 * (payloadPairs m r d j).2)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ varyingOn A E a
    · simp [hj]
    · simp [hj, word_constant_of_not_varying hs hj, zmod2_self_cancel]
  simp_rw [he, chi_zero]
  exact avg_const_real 1

private lemma phaseQuad {k : ℕ} (E : Finset (Vec k)) (h : Vec k → F2)
    (hc : 4 ≤ E.card) (heven : Even E.card) (hsum : (∑ s ∈ E, s) = 0)
    (hmin : ∀ I : Finset (Vec k), I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ s ∈ I, s) ≠ 0) :
    ∃ f : Vec k → F2, SelectorQuad f ∧ ∀ s ∈ E, f s = h s := by
  obtain ⟨f,g,hfg⟩ := selector_quadratic_interpolation hc heven hsum hmin h
  exact ⟨fun s => ∑ j : E, h j.val * (f j s * g j s), selectorQuad_sum (fun j : E => h j.val) f g,hfg⟩

private lemma fullWitness {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r)
    (A : Fin m → Vec k) (h : Vec k → F2) (E : Finset (Vec k)) (a : E)
    (hc : 4 ≤ E.card) (heven : Even E.card) (hsum : (∑ s ∈ E, s) = 0)
    (hmin : ∀ I : Finset (Vec k), I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ s ∈ I, s) ≠ 0) :
    ∃ C : Circuit, legalGates (2*n) C.gates ∧
      costGates C.gates ≤ (2*m+r)+(E.card-2)+(varyingOn A E a.val).card ∧
      ∀ s ∈ E, score e A h C s = 1 := by
  classical
  obtain ⟨s₀, _, B, hB, hfull⟩ := selector_full_chart hc heven hsum hmin
  obtain ⟨f,hq,hf⟩ := phaseQuad E h hc heven hsum hmin
  obtain ⟨C,hC,hcC,he⟩ := upperOnSelector e A h E s₀ B hB f hq
    (fun s hs _ => hf s hs) (varyingOn A E a.val) (words A a.val)
  refine ⟨C,hC,hcC,fun s hs => ?_⟩
  rw [he s hs, if_pos (hfull s hs)]
  exact regularUpperError (r := r) hs

private lemma pairWitness {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r)
    (A : Fin m → Vec k) (h : Vec k → F2) (E : Finset (Vec k)) (a : E)
    (hc : 4 ≤ E.card) (heven : Even E.card) (hsum : (∑ s ∈ E, s) = 0)
    (hmin : ∀ I : Finset (Vec k), I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ s ∈ I, s) ≠ 0) (u v : E) (huv : u ≠ v) :
    ∃ C : Circuit, legalGates (2*n) C.gates ∧
      costGates C.gates ≤ (2*m+r+(E.card-2)+(varyingOn A E a.val).card)-1 ∧
      ∀ s : E, 1-score e A h C s.val = daPairDeficit u v 1 s := by
  classical
  obtain ⟨s₀,_,_,_,B,hB,hcom⟩ :=
    selector_pair_complement_chart u.property v.property
      (fun ht => huv (Subtype.ext ht)) hc heven hsum hmin
  obtain ⟨f,hf⟩ := selector_phase_erase u.property heven hsum hmin h
  obtain ⟨C,hC,hcC,he⟩ := upperOnSelector e A h E s₀ B hB f (selectorQuad_affine f)
    (fun s hs hmem => hf s hs ((hcom s hs).mp hmem).1)
    (varyingOn A E a.val) (words A a.val)
  refine ⟨C,hC,by omega,fun s => ?_⟩
  rw [he s.val s.property]
  by_cases hm : s ∈ ({u,v}:Finset E)
  · have hn : ¬∃ z, s.val = s₀ + B z := by
      intro hmem
      obtain ⟨hu,hv⟩ := (hcom s.val s.property).mp hmem
      rcases Finset.mem_insert.mp hm with h | h
      · exact hu (congrArg Subtype.val h)
      · exact hv (congrArg Subtype.val (Finset.mem_singleton.mp h))
    simp [if_neg hn,daPairDeficit,hm]
  · have hu : s.val ≠ u.val := fun ht => hm
      (Finset.mem_insert.mpr (Or.inl (Subtype.ext ht)))
    have hv : s.val ≠ v.val := fun ht => hm (Finset.mem_insert_of_mem
      (Finset.mem_singleton.mpr (Subtype.ext ht)))
    rw [if_pos ((hcom s.val s.property).mpr ⟨hu,hv⟩), regularUpperError (r := r) s.property]
    simp [daPairDeficit,hm]

private lemma edgeWitness {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r)
    (A : Fin m → Vec k) (h : Vec k → F2) (E : Finset (Vec k)) (a : E)
    (hc : 4 ≤ E.card) (heven : Even E.card) (hsum : (∑ s ∈ E, s) = 0)
    (hmin : ∀ I : Finset (Vec k), I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ s ∈ I, s) ≠ 0) (u v : E) (huv : adjacent A E u.val v.val) :
    ∃ C : Circuit, legalGates (2*n) C.gates ∧
      costGates C.gates ≤ (2*m+r+(E.card-2)+(varyingOn A E a.val).card)-1 ∧
      ∀ s : E, 1-score e A h C s.val = daPairDeficit u v (1/2) s := by
  classical
  obtain ⟨hneq,i,b,hside⟩ := huv
  have hs (s : E) : words A s.val i ≠ b ↔ s ∈ ({u,v}:Finset E) := by
    have hi : s.val ∈ columnSide A E i b ↔ words A s.val i ≠ b := by simp [columnSide,s.property]
    rw [hside] at hi
    rw [← hi]
    constructor
    · intro hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext h))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
          (Subtype.ext (Finset.mem_singleton.mp h))))
    · intro hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val h))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
          (congrArg Subtype.val (Finset.mem_singleton.mp h))))
  obtain ⟨z,hz,hzu,hzv,_,_,_⟩ :=
    selector_pair_complement_chart u.property v.property hneq hc heven hsum hmin
  have hz' : words A z i = b := by
    by_contra hn
    have ht := (hs ⟨z,hz⟩).mp hn
    rcases Finset.mem_insert.mp ht with h | h
    · exact hzu (congrArg Subtype.val h)
    · exact hzv (congrArg Subtype.val (Finset.mem_singleton.mp h))
  have hi : i ∈ varyingOn A E a.val := by
    by_contra hn
    have h₁ := word_constant_of_not_varying u.property hn
    have h₂ := word_constant_of_not_varying hz hn
    exact (hs u).mpr (Finset.mem_insert_self _ _) (h₁.trans (h₂.symm.trans hz'))
  let I := (varyingOn A E a.val).erase i
  let β : Fin m → F2 := Function.update (words A a.val) i b
  have hI : I.card = (varyingOn A E a.val).card - 1 := Finset.card_erase_of_mem hi
  obtain ⟨s₀,_,B,hB,hfull⟩ := selector_full_chart hc heven hsum hmin
  obtain ⟨f,hq,hphase⟩ := phaseQuad E h hc heven hsum hmin
  obtain ⟨C,hC,hcC,he⟩ := upperOnSelector e A h E s₀ B hB f hq
    (fun s hs _ => hphase s hs) I β
  have hct : costGates C.gates ≤ (2*m+r+(E.card-2)+(varyingOn A E a.val).card)-1 := by
    rw [hI] at hcC
    have hp : 0 < (varyingOn A E a.val).card := Finset.card_pos.mpr ⟨i,hi⟩
    omega
  refine ⟨C,hC,hct,fun s => ?_⟩
  rw [he s.val s.property, if_pos (hfull s.val s.property)]
  have hsum' (d : Vec (2*m+r)) :
    (∑ j, if j ∈ I then 0 else (words A s.val j + β j) *
      ((payloadPairs m r d j).1 * (payloadPairs m r d j).2)) =
      (words A s.val i + b) * ((payloadPairs m r d i).1 * (payloadPairs m r d i).2) := by
    rw [Finset.sum_eq_single i]
    · simp [I,β]
    · intro j _ hji
      by_cases hj : j ∈ varyingOn A E a.val
      · simp [I,Finset.mem_erase,hji,hj]
      · simp [I,Finset.mem_erase,hji,hj,β,word_constant_of_not_varying s.property hj,zmod2_self_cancel]
    · simp
  simp_rw [hsum']
  by_cases hm : s ∈ ({u,v}:Finset E)
  · rw [zmod2_add_eq_one_of_ne _ _ ((hs s).mpr hm)]
    simp only [one_mul]
    rw [avg_payload_pair]
    norm_num [daPairDeficit,hm]
  · have hb : words A s.val i = b := by
      by_contra hn
      exact hm ((hs s).mp hn)
    simp only [hb,zmod2_self_cancel,zero_mul,chi_zero,avg_const_real]
    simp [daPairDeficit,hm]

private lemma score_canonical {k m r n : ℕ}
    (e : Vec n ≃ₗ[F2] Vec k × Data m r) (A : Fin m → Vec k) (h : Vec k → F2)
    (C : Circuit) (s : Vec k) :
    score e A h C s =
      (∑ x : Vec n, ∑ b : Vec m, ∑ c : Vec m, ∑ z : Vec r,
        let y := e.symm (s,(b,(c,z)))
        let v := dotProduct x y + h s + ∑ i, dotProduct (A i) s * b i * c i
        if C.eval (bitsOf n x ++ bitsOf n y) = decide (v = 1) then (1 : ℝ) else -1) /
        2^(n+(2*m+r)) := by
  unfold score avg
  rw [← Finset.sum_div, div_div]
  have hx : (Fintype.card (Vec n) : ℝ) = 2^n := by simp [Vec,ZMod.card]
  have hd : (Fintype.card (Vec (2*m+r)) : ℝ) = 2^(2*m+r) := by simp [Vec,ZMod.card]
  rw [hx,hd,← pow_add,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [← Equiv.sum_comp (pack m r).toEquiv]
  simp only [point, phase, LinearEquiv.coe_toEquiv, LinearEquiv.symm_apply_apply,
    Fintype.sum_prod_type, words, add_assoc]

private lemma mass_map_subtype {α : Type*} (E : Finset α) (w : α → ℝ) (I : Finset E) :
    daMass (fun v : E => w v.val) I = ∑ s ∈ I.map (Function.Embedding.subtype _), w s := by
  simp [daMass, Finset.sum_map]

private lemma all_map_subtype {α : Type*} (E : Finset α) :
    (Finset.univ : Finset E).map (Function.Embedding.subtype _) = E := by
  classical
  ext s
  simp [Finset.mem_map]

private lemma mass_subtype {α : Type*} (E : Finset α) (w : α → ℝ) :
    daMass (fun v : E => w v.val) Finset.univ = ∑ s ∈ E, w s := by
  rw [mass_map_subtype, all_map_subtype]

private noncomputable def postedNbr {α : Type*} (E : Finset α) (adj : α → α → Prop)
    (I : Finset α) : Finset α :=
  @Finset.filter α (fun v => ∃ u ∈ I, adj u v) (fun _ => Classical.propDecidable _) E

private lemma nbr_map_subtype {α : Type*} (E : Finset α) (adj : α → α → Prop) (I : Finset E) :
    (daNbr (fun u v : E => adj u.val v.val) I).map (Function.Embedding.subtype _) =
      postedNbr E adj (I.map (Function.Embedding.subtype _)) := by
  classical
  ext v
  rw [Finset.mem_map]
  change (∃ s : E, s ∈ _ ∧ s.val = v) ↔ v ∈ postedNbr E adj _
  have hmem : v ∈ postedNbr E adj (I.map (Function.Embedding.subtype _)) ↔
      v ∈ E ∧ ∃ u ∈ I.map (Function.Embedding.subtype _), adj u v :=
    @Finset.mem_filter α _ (fun _ => Classical.propDecidable _) E v
  rw [hmem]
  constructor
  · rintro ⟨s,hs,rfl⟩
    obtain ⟨u,hu,ha⟩ := da_mem_nbr.mp hs
    exact ⟨s.property, u.val, Finset.mem_map.mpr ⟨u,hu,rfl⟩, ha⟩
  · rintro ⟨hE,u,hu,ha⟩
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp hu
    exact ⟨⟨v,hE⟩,da_mem_nbr.mpr ⟨s,hs,ha⟩,rfl⟩

private def postedSaving {α : Type*} [DecidableEq α] (E : Finset α) (adj : α → α → Prop)
    (w : α → ℝ) (b : ℝ) : Prop :=
  (∃ I : Finset α, I ⊆ E ∧ (∀ u ∈ I, ∀ v ∈ I, ¬adj u v) ∧
    b = ((∑ s ∈ I, w s) - ∑ s ∈ postedNbr E adj I, w s)/2) ∨
  ∃ v ∈ E, b = w v - ∑ s ∈ postedNbr E adj {v}, w s

private lemma saving_subtype {α : Type*} [DecidableEq α] (E : Finset α)
    (adj : α → α → Prop) (w : α → ℝ) (b : ℝ) :
    daSaving (fun u v : E => adj u.val v.val) (fun v : E => w v.val) b ↔
      postedSaving E adj w b := by
  classical
  let emb : E ↪ α := Function.Embedding.subtype _
  have hm (I : Finset E) :
      daMass (fun v : E => w v.val) (daNbr (fun u v : E => adj u.val v.val) I) =
        ∑ s ∈ postedNbr E adj (I.map emb), w s := by
    rw [mass_map_subtype,nbr_map_subtype]
  constructor
  · rintro (⟨I,hI,heq⟩ | ⟨v,hv⟩)
    · left
      refine ⟨I.map emb, ?_, ?_, ?_⟩
      · intro s hs
        obtain ⟨v,_,rfl⟩ := Finset.mem_map.mp hs
        exact v.property
      · intro u hu v hv
        obtain ⟨u',hu',rfl⟩ := Finset.mem_map.mp hu
        obtain ⟨v',hv',rfl⟩ := Finset.mem_map.mp hv
        exact hI u' hu' v' hv'
      · rwa [← mass_map_subtype, ← hm]
    · right
      refine ⟨v.val,v.property,?_⟩
      rw [hv,hm,Finset.map_singleton]
      rfl
  · rintro (⟨I,hI,hs,heq⟩ | ⟨v,hv,heq⟩)
    · left
      let J : Finset E := Finset.univ.filter fun v => v.val ∈ I
      have hj : J.map emb = I := by
        ext s
        simp only [Finset.mem_map,J,Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · rintro ⟨v,hv,rfl⟩
          exact hv
        · intro hv
          exact ⟨⟨s,hI hv⟩,hv,rfl⟩
      refine ⟨J, ?_, ?_⟩
      · intro u hu v hv
        exact hs u.val (Finset.mem_filter.mp hu).2 v.val (Finset.mem_filter.mp hv).2
      · rwa [mass_map_subtype,hm,hj]
    · right
      refine ⟨⟨v,hv⟩,?_⟩
      rw [hm,Finset.map_singleton]
      exact heq

private def fit (n p : ℕ) (C : Circuit) : Prop :=
  legalGates (2*n) C.gates ∧ costGates C.gates ≤ p

private lemma assignmentCore {k m r n : ℕ} (e : Vec n ≃ₗ[F2] Vec k × Data m r)
    (A : Fin m → Vec k) (h : Vec k → F2) (E : Finset (Vec k)) (a : Vec k) (ha : a ∈ E)
    (hc : 4 ≤ E.card) (heven : Even E.card) (hsum : (∑ s ∈ E, s) = 0)
    (hmin : ∀ I : Finset (Vec k), I ⊆ E → I.Nonempty → I ≠ E → Even I.card →
      (∑ s ∈ I, s) ≠ 0)
    (w : Vec k → ℝ) (hw : ∀ s ∈ E, 0 < w s) :
    let price := (2*m+r)+(E.card-2)+(varyingOn A E a).card
    let adj := adjacent A E
    (∀ p, (∃ C, fit n p C ∧ ∀ s ∈ E, score e A h C s = 1) ↔ price ≤ p) ∧
    ∃ b : ℝ, postedSaving E adj w b ∧ (∀ z : ℝ, postedSaving E adj w z → z ≤ b) ∧
      b < (∑ s ∈ E, w s) ∧ ∀ q : ℝ,
      (∃ (N : ℕ) (C : Fin N → Circuit) (p : Fin N → ℝ),
        (∀ i, fit n (price-1) (C i) ∧ 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
        ∀ s ∈ E, 1 - (∑ i, p i * score e A h (C i) s) ≤ q*w s) ↔
      1 ≤ q*((∑ s ∈ E, w s)-b) := by
  classical
  intro price adj
  let aE : E := ⟨a,ha⟩
  have hp : 0 < price := by dsimp only [price]; omega
  constructor
  · intro p
    constructor
    · rintro ⟨C,⟨hC,hcost⟩,hex⟩
      by_contra! hn
      have hlt : costGates C.gates < price := hcost.trans_lt hn
      have hcov : daCover (fun u v : E => adj u.val v.val) (fun _ => 1) := by
        refine ⟨fun _ => by norm_num, fun _ _ _ => by norm_num, fun _ _ _ => by norm_num⟩
      have hd := circuitDeficit e A h E aE hc heven hsum hmin C hC hlt _ hcov
      simp [hex _ (Subtype.property _)] at hd
      norm_num at hd
    · intro hp'
      obtain ⟨C,hC,hcost,hex⟩ := fullWitness e A h E aE hc heven hsum hmin
      exact ⟨C,⟨hC,hcost.trans hp'⟩,hex⟩
  · let adjE (u v : E) := adj u.val v.val
    have hsym : ∀ ⦃u v : E⦄, adjE u v → adjE v u := by
      intro u v huv
      obtain ⟨hn,i,b,he⟩ := huv
      exact ⟨hn.symm,i,b,he.trans (by ext s; simp [or_comm])⟩
    have hirr (v : E) : ¬adjE v v := fun hh => hh.1 rfl
    have hother (v : E) : ∃ u : E, u ≠ v := by
      obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0 < (E.erase v.val).card by
        rw [Finset.card_erase_of_mem v.property]; omega)
      exact ⟨⟨u,(Finset.mem_erase.mp hu).2⟩,fun he =>
        (Finset.mem_erase.mp hu).1 (congrArg Subtype.val he)⟩
    obtain ⟨b,hb,hmax,hlt,hq⟩ :=
      da_atom_mixture adjE hsym hirr (fun v => w v.val) (fun v => hw _ v.property)
        hother ⟨aE⟩ (fit n (price-1)) (fun C v => score e A h C v.val)
        (fun C hC cov hcov => circuitDeficit e A h E aE hc heven hsum hmin C hC.1
          (hC.2.trans_lt (by omega : price-1 < price)) cov hcov)
        (fun u v huv => by
          obtain ⟨C,hC,hct,he⟩ := pairWitness e A h E aE hc heven hsum hmin u v huv
          exact ⟨C,⟨hC,hct⟩,he⟩)
        (fun u v huv => by
          obtain ⟨C,hC,hct,he⟩ := edgeWitness e A h E aE hc heven hsum hmin u v huv
          exact ⟨C,⟨hC,hct⟩,he⟩)
    refine ⟨b,(saving_subtype E adj w b).mp hb,
      fun z hz => hmax z ((saving_subtype E adj w z).mpr hz), ?_, ?_⟩
    · simpa only [mass_subtype] using hlt
    · intro q
      simpa only [mass_subtype, Subtype.forall] using hq q

private lemma filter_to_classical {α : Type*} (s : Finset α) (p : α → Prop)
    (d : DecidablePred p) :
    @Finset.filter α p d s = @Finset.filter α p (fun _ => Classical.propDecidable _) s :=
  congrArg (fun δ : DecidablePred p => @Finset.filter α p δ s) (Subsingleton.elim _ _)

private lemma filter_decision_eq {α : Type*} {p : α → Prop} (d e : DecidablePred p) :
    @Finset.filter α p d = @Finset.filter α p e :=
  congrArg (fun δ : DecidablePred p => @Finset.filter α p δ) (Subsingleton.elim d e)

private lemma filter_predicate_eq {α : Type*} {p q : α → Prop}
    (d : DecidablePred p) (e : DecidablePred q) (h : ∀ x, p x ↔ q x) :
    @Finset.filter α p d = @Finset.filter α q e := by
  have he : p = q := funext (fun x => propext (h x))
  subst q
  exact filter_decision_eq d e

end PEqualNP.Outside.L_meta_32589_aux

open PEqualNP.Outside.L_meta_32589_aux

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_meta_32589 :
  ∀ k m r : ℕ,
    let n := k+2*m+r
    let Circ := PEqualNP.CircuitLowerBounds.Circuit
    let F := ZMod 2
    let legal := fun (width : ℕ) (C : Circ) =>
      PEqualNP.MetaComplexity.NestedCover.ReadsBack width C ∧
        (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
          (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
    let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
      ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
    let bits := fun (width : ℕ) (u : Fin width → F) => List.ofFn (fun j : Fin width => decide (u j = 1))
    let V := Fin n → F
    let S := Fin k → F
    let D := Fin m → F
    let Z := Fin r → F
    let base := 2*m+r
    ∀ (e : V ≃ₗ[F] S × (D × (D × Z))) (A : Fin m → S) (h : S → F),
      let word := fun (s : S) (i : Fin m) => dotProduct (A i) s
      let score := fun (C : Circ) (s : S) =>
        (∑ x : V, ∑ b : D, ∑ c : D, ∑ z : Z,
          let y := e.symm (s,(b,(c,z)))
          let v := dotProduct x y + h s + ∑ i, word s i * b i * c i
          if C.eval (bits n x ++ bits n y) = decide (v = 1) then (1 : ℝ) else -1) / 2^(n+base)
      let fits := fun (p : ℕ) (C : Circ) => legal (2*n) C ∧ cost C ≤ p
      ∀ (E : Finset S) (a : S), a ∈ E →
        4 ≤ E.card → Even E.card → (∑ s ∈ E, s) = 0 →
        (∀ I : Finset S, I ⊆ E → I.Nonempty → I ≠ E → Even I.card → (∑ s ∈ I, s) ≠ 0) →
        let varying := ((Finset.univ : Finset (Fin m)).filter (fun i =>
          ∃ s ∈ E, word s i ≠ word a i)).card
        let price := base+(E.card-2)+varying
        let adj := fun (s u : S) => s ≠ u ∧ ∃ (i : Fin m) (b : F),
          E.filter (fun v => word v i ≠ b) = ({s,u} : Finset S)
        let nbr := fun (I : Finset S) => @Finset.filter S (fun v => ∃ u ∈ I, adj u v)
          (fun _ => Classical.propDecidable _) E
        ∀ w : S → ℝ, (∀ s ∈ E, 0 < w s) →
          let mass := fun (I : Finset S) => ∑ s ∈ I, w s
          let saving := fun (b : ℝ) =>
            (∃ I : Finset S, I ⊆ E ∧ (∀ u ∈ I, ∀ v ∈ I, ¬adj u v) ∧
              b = (mass I-mass (nbr I))/2) ∨
            ∃ v ∈ E, b = w v - mass (nbr {v})
          let feasible := fun (q : ℝ) =>
            ∃ (N : ℕ) (C : Fin N → Circ) (p : Fin N → ℝ),
              (∀ i, fits (price-1) (C i) ∧ 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
              ∀ s ∈ E, 1-(∑ i, p i * score (C i) s) ≤ q*w s
          (∀ p : ℕ, (∃ C : Circ, fits p C ∧ ∀ s ∈ E, score C s = 1) ↔ price ≤ p) ∧
          ∃ b : ℝ, saving b ∧ (∀ z : ℝ, saving z → z ≤ b) ∧ b < mass E ∧
            ∀ q : ℝ, feasible q ↔ 1 ≤ q*(mass E-b)
:= by
  dsimp only
  intro k m r e A h E a ha hc heven hsum hmin w hw
  have hcore := assignmentCore e A h E a ha hc heven hsum hmin w hw
  simp only [fit, legalGates, costGates, varyingOn, words, adjacent, columnSide,
    postedSaving, postedNbr, score_canonical, bitsOf, filter_to_classical,
    PEqualNP.MetaComplexity.NestedCover.ReadsBack,
    PEqualNP.MetaComplexity.NestedCover.gateAt] at hcore ⊢
  convert hcore using 1 <;> congr! <;>
    first
    | exact filter_decision_eq _ _
    | (apply filter_predicate_eq; intro x; congr! <;> exact filter_decision_eq _ _)
