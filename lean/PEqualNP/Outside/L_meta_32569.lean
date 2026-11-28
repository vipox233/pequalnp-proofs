import PEqualNP.Defs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace PEqualNP.Outside.L_meta_32569_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Matrix

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

lemma z2_add_self (a : F2) : a + a = 0 := by
  revert a; decide

lemma z2_eq_one_of_ne_zero {a : F2} (h : a ≠ 0) : a = 1 := by
  revert a h; decide

lemma z2_eq_of_add_eq_zero {a b : F2} (h : a + b = 0) : a = b := by
  revert a b h; decide

lemma zmod2_vec_add_self {k : ℕ} (x : Fin k → F2) : x + x = 0 := by
  funext j; exact z2_add_self (x j)

lemma z2_polar_prod (a b x1 x2 y1 y2 : F2) :
    (a + x1 + x2) * (b + y1 + y2) + (a + x1) * (b + y1) + (a + x2) * (b + y2) + a * b =
      x1 * y2 + x2 * y1 := by
  have h : (a + x1 + x2) * (b + y1 + y2) + (a + x1) * (b + y1) + (a + x2) * (b + y2) + a * b =
      (a * b + a * b) + (a * b + a * b) + (a * y1 + a * y1) + (a * y2 + a * y2) +
      (x1 * b + x1 * b) + (x1 * y1 + x1 * y1) + (x2 * b + x2 * b) + (x2 * y2 + x2 * y2) +
      (x1 * y2 + x2 * y1) := by ring
  rw [h]
  simp only [z2_add_self, zero_add]

lemma z2_polar_aff (a x1 x2 : F2) :
    (a + x1 + x2) + (a + x1) + (a + x2) + a = 0 := by
  have h : (a + x1 + x2) + (a + x1) + (a + x2) + a =
      (a + a) + (a + a) + (x1 + x1) + (x2 + x2) := by ring
  rw [h]
  simp only [z2_add_self, add_zero]

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
  · rcases hg : g.inputs with _ | ⟨w0, rest⟩
    · let gs' := B.gates ++ [⟨.and, []⟩]
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
      · have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        have hres := branch_eval_add_gate hleg hB B.gates [] (by simp) hB.2.1
          (by have := hB.2.2.1; omega) (B.off w0) (hB.2.2.2.2.1 w0 hw0) (B.slope w0)
          (fun z u hu => by
            rw [hop, hg]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
              List.all_nil, id_eq, Bool.and_true]
            exact hB.2.2.2.2.2 w0 hw0 z u hu)
        exact hwrap_one _ hres.1 rfl hres.2
      · rcases rest2 with _ | ⟨_, _⟩
        · have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
          have hw1 : w1 < k + t + gs.length := hback w1 (by rw [hg]; simp)
          have hcost1 : costGates (gs ++ [g]) = costGates gs + 1 :=
            costGates_snoc_one gs g ⟨Or.inl hop, by rw [hg]; rfl⟩
          by_cases hvan : (∀ u ∈ B.U, dotProduct (B.slope w0) u = 0) ∧
              (∀ u ∈ B.U, dotProduct (B.slope w1) u = 0)
          · let gs' := B.gates ++ [⟨.and, [B.off w0, B.off w1]⟩]
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
          · have hex : ∃ (wa wb : ℕ), wa < k + t + gs.length ∧ wb < k + t + gs.length ∧
                ((wa = w0 ∧ wb = w1) ∨ (wa = w1 ∧ wb = w0)) ∧
                ∃ v0 ∈ B.U, dotProduct (B.slope wa) v0 = 1 := by
              by_cases h0 : ∀ u ∈ B.U, dotProduct (B.slope w0) u = 0
              · have h1 : ¬ ∀ u ∈ B.U, dotProduct (B.slope w1) u = 0 := fun h => hvan ⟨h0, h⟩
                push Not at h1
                rcases h1 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.slope w1) v0 = 1 := z2_eq_one_of_ne_zero hne
                exact ⟨w1, w0, hw1, hw0, Or.inr ⟨rfl, rfl⟩, v0, hv0, hd1⟩
              · push Not at h0
                rcases h0 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.slope w0) v0 = 1 := z2_eq_one_of_ne_zero hne
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
  · rcases hg : g.inputs with _ | ⟨w0, rest⟩
    · let gs' := B.gates ++ [⟨.or, []⟩]
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
      · have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        have hres := branch_eval_add_gate hleg hB B.gates [] (by simp) hB.2.1
          (by have := hB.2.2.1; omega) (B.off w0) (hB.2.2.2.2.1 w0 hw0) (B.slope w0)
          (fun z u hu => by
            rw [hop, hg]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
              List.any_nil, id_eq, Bool.or_false]
            exact hB.2.2.2.2.2 w0 hw0 z u hu)
        exact hwrap_one _ hres.1 rfl hres.2
      · rcases rest2 with _ | ⟨_, _⟩
        · have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
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
                have hd1 : dotProduct (B.slope w1) v0 = 1 := z2_eq_one_of_ne_zero hne
                exact ⟨w1, w0, hw1, hw0, Or.inr ⟨rfl, rfl⟩, v0, hv0, hd1⟩
              · push Not at h0
                rcases h0 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.slope w0) v0 = 1 := z2_eq_one_of_ne_zero hne
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
  · rcases hg : g.inputs with _ | ⟨w0, rest⟩
    · let gs' := B.gates ++ [⟨.mod 2, []⟩]
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
      · rcases rest2 with _ | ⟨_, _⟩
        · have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
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
  · rcases hg : g.inputs with _ | ⟨w0, rest⟩
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

lemma signBool_le_one (b : Bool) : signBool b ≤ 1 := by
  cases b <;> decide

lemma signBool_sum_f2 {ι : Type*} (S : Finset ι) (f : ι → F2) :
    signBool (decide ((∑ i ∈ S, f i) = 1)) = ∏ i ∈ S, signBool (decide (f i = 1)) := by
  induction S using Finset.induction_on with
  | empty => simp [signBool]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, zmod2_add_decide, signBool_xor, ih]

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

lemma linear_coord_dot {k : ℕ} (ℓ : (Fin k → F2) →ₗ[F2] F2) :
    ∃ r : Fin k → F2, ∀ y : Fin k → F2, ℓ y = dotProduct r y := by
  refine ⟨fun j => ℓ (Pi.single j 1), fun y => ?_⟩
  conv_lhs => rw [vec_eq_sum_single y, map_sum]
  simp only [dotProduct, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

lemma isQuad_comp_linear {k s : ℕ} (B : (Fin s → F2) →ₗ[F2] (Fin k → F2))
    {f : (Fin k → F2) → F2} (hf : isQuad f) : isQuad (fun u => f (B u)) := by
  rcases hf with ⟨z, l, M, hfeq⟩
  have h1 : isQuad (fun _ : Fin s → F2 => z) := isQuad_const z
  have h2 : isQuad (fun u : Fin s → F2 => dotProduct l (B u)) := by
    obtain ⟨r, hr⟩ := linear_coord_dot ((dotLin l).comp B)
    have heq : (fun u => dotProduct l (B u)) = (fun u => dotProduct r u + 0) := by
      funext u; rw [add_zero]; exact hr u
    rw [heq]; exact isQuad_affine r 0
  have h3 : isQuad (fun u : Fin s → F2 => ∑ a : Fin k, ∑ b : Fin k, M a b * B u a * B u b) := by
    apply isQuad_finset_sum Finset.univ
    intro a _
    apply isQuad_finset_sum Finset.univ
    intro b _
    obtain ⟨ra, hra⟩ := linear_coord_dot ((LinearMap.proj a).comp B)
    obtain ⟨rb, hrb⟩ := linear_coord_dot ((LinearMap.proj b).comp B)
    have heq : (fun u : Fin s → F2 => M a b * B u a * B u b) =
        (fun u => (dotProduct (M a b • ra) u + 0) * (dotProduct rb u + 0)) := by
      funext u
      simp only [add_zero, smul_dotProduct, smul_eq_mul]
      have ha : B u a = dotProduct ra u := hra u
      have hb : B u b = dotProduct rb u := hrb u
      rw [ha, hb]
    rw [heq]; exact isQuad_mul_affine (M a b • ra) rb 0 0
  have heq : (fun u => f (B u)) =
      (fun u => (z + dotProduct l (B u)) + ∑ a : Fin k, ∑ b : Fin k, M a b * B u a * B u b) := by
    funext u; exact hfeq (B u)
  rw [heq]; exact isQuad_add (isQuad_add h1 h2) h3

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

def appendXorWiresLoop (n k : ℕ) (c : Fin k → F2) (ws : Fin k → ℕ) :
    (m : ℕ) → m ≤ k → List Gate → ℕ → List Gate × ℕ
  | 0, _, gs, acc => (gs, acc)
  | m + 1, hm, gs, acc =>
    let res := appendXorWiresLoop n k c ws m (by omega) gs acc
    let gs1 := res.1
    let acc1 := res.2
    if c ⟨m, hm⟩ = 1 then
      (gs1 ++ [⟨.mod 2, [acc1, ws ⟨m, hm⟩]⟩, ⟨.not, [n + gs1.length]⟩], n + gs1.length + 1)
    else (gs1, acc1)

lemma appendXorWiresLoop_spec (n k : ℕ) (c : Fin k → F2) (ws : Fin k → ℕ) :
    ∀ (m : ℕ) (hm : m ≤ k) (gs : List Gate) (acc : ℕ),
      legalGates n gs → acc < n + gs.length → (∀ i : Fin k, ws i < n + gs.length) →
      let res := appendXorWiresLoop n k c ws m hm gs acc
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates n res.1 ∧
        costGates res.1 = costGates gs ∧
        res.2 < n + res.1.length ∧
        ∀ u : Fin n → F2,
          (wiresOf res.1 (bitsOf n u)).getD res.2 false =
            Bool.xor ((wiresOf gs (bitsOf n u)).getD acc false)
              (decide ((∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val < m),
                c j * (if (wiresOf gs (bitsOf n u)).getD (ws j) false then (1 : F2) else 0)) = 1)) := by
  intro m
  induction m with
  | zero =>
    intro hm gs acc hleg hacc _
    refine ⟨[], by simp [appendXorWiresLoop], hleg, rfl, hacc, fun u => ?_⟩
    have hemp : Finset.univ.filter (fun j : Fin k => j.val < 0) = ∅ := by ext j; simp
    simp [appendXorWiresLoop, hemp]
  | succ m ih =>
    intro hm gs acc hleg hacc hws
    rcases ih (by omega) gs acc hleg hacc hws with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set gs1 := (appendXorWiresLoop n k c ws m (by omega) gs acc).1
    set acc1 := (appendXorWiresLoop n k c ws m (by omega) gs acc).2
    have hsplit : (Finset.univ.filter (fun j : Fin k => j.val < m + 1)) =
        insert ⟨m, hm⟩ (Finset.univ.filter (fun j : Fin k => j.val < m)) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hnotmem : (⟨m, hm⟩ : Fin k) ∉ Finset.univ.filter (fun j : Fin k => j.val < m) := by simp
    by_cases hcm : c ⟨m, hm⟩ = 1
    · have hws_lt1 : ws ⟨m, hm⟩ < n + gs1.length := by
        rw [h1eq, List.length_append]; have := hws ⟨m, hm⟩; omega
      have hstep := addXor_step n gs1 acc1 (ws ⟨m, hm⟩) h1leg h1lt hws_lt1
      refine ⟨ext1 ++ [⟨.mod 2, [acc1, ws ⟨m, hm⟩]⟩, ⟨.not, [n + gs1.length]⟩], ?_, ?_, ?_, ?_, ?_⟩
      · simp [appendXorWiresLoop, hcm, gs1, acc1, h1eq, List.append_assoc]
      · simpa [appendXorWiresLoop, hcm, gs1, acc1] using hstep.1
      · simpa [appendXorWiresLoop, hcm, gs1, acc1, h1cost] using hstep.2.1
      · simp only [appendXorWiresLoop, hcm, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]
        omega
      · intro u
        simp only [appendXorWiresLoop, hcm, ↓reduceIte]
        change (wiresOf (gs1 ++ [⟨.mod 2, [acc1, ws ⟨m, hm⟩]⟩, ⟨.not, [n + gs1.length]⟩]) (bitsOf n u)).getD (n + gs1.length + 1) false = _
        rw [hstep.2.2.2 (bitsOf n u) (bitsOf_len n u), h1sem u]
        have hm_wire : (wiresOf gs1 (bitsOf n u)).getD (ws ⟨m, hm⟩) false =
            (wiresOf gs (bitsOf n u)).getD (ws ⟨m, hm⟩) false := by
          rw [h1eq, wiresOf_append_getD_lt gs ext1 (bitsOf n u) (by rw [bitsOf_len]; exact hws ⟨m, hm⟩)]
        rw [hm_wire, hsplit, Finset.sum_insert hnotmem, hcm, one_mul, zmod2_add_decide, zmod2_bool_decide]
        cases (wiresOf gs (bitsOf n u)).getD acc false <;>
          cases (wiresOf gs (bitsOf n u)).getD (ws ⟨m, hm⟩) false <;>
          cases decide ((∑ x ∈ Finset.univ.filter (fun j : Fin k => j.val < m),
            c x * (if (wiresOf gs (bitsOf n u)).getD (ws x) false then (1 : F2) else 0)) = 1) <;> decide
    · have hcm0 : c ⟨m, hm⟩ = 0 := by
        rcases zmod2_cases (c ⟨m, hm⟩) with h0 | h1
        · exact h0
        · exact absurd h1 hcm
      refine ⟨ext1, ?_, ?_, ?_, ?_, ?_⟩
      · simp [appendXorWiresLoop, hcm, gs1, h1eq]
      · simpa [appendXorWiresLoop, hcm, gs1] using h1leg
      · simpa [appendXorWiresLoop, hcm, gs1] using h1cost
      · simpa [appendXorWiresLoop, hcm, gs1, acc1] using h1lt
      · intro u
        simp only [appendXorWiresLoop, hcm, ↓reduceIte]
        rw [h1sem u, hsplit, Finset.sum_insert hnotmem, hcm0, zero_mul, zero_add]

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

def concatVec2 {k t : ℕ} (x : Fin k → F2) (y : Fin t → F2) : Fin (k + t) → F2 :=
  fun idx => if h : idx.val < k then x ⟨idx.val, h⟩ else y ⟨idx.val - k, by omega⟩

lemma bitsOf_concatVec2 {k t : ℕ} (x : Fin k → F2) (y : Fin t → F2) :
    bitsOf k x ++ bitsOf t y = bitsOf (k + t) (concatVec2 x y) := by
  apply List.ext_getElem
  · simp [bitsOf_len]
  · intro i h1 h2
    simp only [bitsOf]
    by_cases hik : i < k
    · rw [List.getElem_append_left (by simp; exact hik)]
      simp [concatVec2, hik]
    · rw [List.getElem_append_right (by simp; omega)]
      simp [concatVec2, hik]

lemma dotProduct_concatVec2 {k t : ℕ} (u x : Fin k → F2) (v y : Fin t → F2) :
    dotProduct (concatVec2 u v) (concatVec2 x y) = dotProduct u x + dotProduct v y := by
  simp only [dotProduct]
  let e : Fin k ⊕ Fin t ≃ Fin (k + t) :=
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
    simp [e, concatVec2, i.isLt]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hnot : ¬ (k + i.val < k) := by omega
    simp [e, concatVec2, hnot]

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

lemma viaFlat_to_viaCircuit (k s : ℕ) (g : (Fin k → F2) → F2) (T : ℕ)
    (B : (Fin s → F2) →ₗ[F2] (Fin k → F2)) (a : Fin k → F2) (q : (Fin s → F2) → F2)
    (hB : Function.Injective B) (hq : isQuad q)
    (hT : T ≤ 2 ^ k * (∑ v : Fin s → F2, if g (a + B v) = q v then (1 : ℤ) else -1).natAbs) :
    ∃ C : Circuit, legalGates (2 * k) C.gates ∧ costGates C.gates ≤ s ∧
      T ≤ (∑ x : Fin k → F2, ∑ y : Fin k → F2,
        if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs := by
  rcases hq with ⟨b, c, M, hq_eq⟩
  rcases linear_map_left_inv B hB with ⟨L, hLB⟩
  have hcoord : ∀ i : Fin s, ∃ r : Fin k → F2, ∀ w : Fin k → F2, L w i = dotProduct r w := fun i =>
    linear_coord_dot ((LinearMap.proj i).comp L)
  choose rv hrv using hcoord
  let c0 : Fin (2 * k) → F2 := concatVec a 0
  let b0 : F2 := b
  let cA : Fin s → Fin (2 * k) → F2 := fun i => concatVec 0 (rv i)
  let bA : Fin s → F2 := fun i => dotProduct (rv i) a
  let cB : Fin s → Fin (2 * k) → F2 := fun i =>
    concatVec (B (Pi.single i 1)) (∑ j : Fin s, M i j • rv j)
  let bB : Fin s → F2 := fun i => c i + ∑ j : Fin s, M i j * dotProduct (rv j) a
  rcases build_sum_prods_circuit (2 * k) s c0 b0 cA cB bA bB with ⟨C, hleg, hcost, heval⟩
  refine ⟨C, hleg, by omega, ?_⟩
  have hCe : ∀ x y : Fin k → F2,
      C.eval (bitsOf k x ++ bitsOf k y) =
        decide (dotProduct x (a + B (L (y + a))) + q (L (y + a)) = 1) := by
    intro x y
    rw [bitsOf_concatVec, heval (concatVec x y)]
    congr 1
    have h0 : dotProduct c0 (concatVec x y) + b0 = dotProduct x a + b := by
      simp only [c0, b0, dotProduct_concatVec, zero_dotProduct, add_zero, dotProduct_comm a x]
    have hAi : ∀ i : Fin s, dotProduct (cA i) (concatVec x y) + bA i = L (y + a) i := by
      intro i
      simp only [cA, bA, dotProduct_concatVec, zero_dotProduct, zero_add, hrv i, dotProduct_add]
    have hBi : ∀ i : Fin s, dotProduct (cB i) (concatVec x y) + bB i =
        dotProduct x (B (Pi.single i 1)) + c i + ∑ j : Fin s, M i j * L (y + a) j := by
      intro i
      simp only [cB, bB, dotProduct_concatVec, dotProduct_comm (B (Pi.single i 1)) x]
      have hsum : dotProduct (∑ j : Fin s, M i j • rv j) y + ∑ j : Fin s, M i j * dotProduct (rv j) a =
          ∑ j : Fin s, M i j * L (y + a) j := by
        rw [sum_dotProduct, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_dotProduct, smul_eq_mul, hrv j, dotProduct_add]; ring
      linear_combination hsum
    have hPB : dotProduct x (B (L (y + a))) =
        ∑ i : Fin s, L (y + a) i * dotProduct x (B (Pi.single i 1)) := by
      conv_lhs => rw [vec_eq_sum_single (L (y + a)), map_sum, dotProduct_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, dotProduct_smul, smul_eq_mul]
    rw [h0, dotProduct_add, hPB, hq_eq (L (y + a))]
    have hterms : (∑ i : Fin s, (dotProduct (cA i) (concatVec x y) + bA i) * (dotProduct (cB i) (concatVec x y) + bB i)) =
        (∑ i : Fin s, L (y + a) i * dotProduct x (B (Pi.single i 1))) +
        dotProduct c (L (y + a)) +
        ∑ i : Fin s, ∑ j : Fin s, M i j * L (y + a) i * L (y + a) j := by
      simp_rw [hAi, hBi]
      calc (∑ i : Fin s, L (y + a) i * (dotProduct x (B (Pi.single i 1)) + c i + ∑ j : Fin s, M i j * L (y + a) j))
          = ∑ i : Fin s, ((L (y + a) i * dotProduct x (B (Pi.single i 1)) + c i * L (y + a) i) +
              ∑ j : Fin s, M i j * L (y + a) i * L (y + a) j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [mul_add, mul_add, Finset.mul_sum]
            have hinner : (∑ j : Fin s, L (y + a) i * (M i j * L (y + a) j)) =
                ∑ j : Fin s, M i j * L (y + a) i * L (y + a) j :=
              Finset.sum_congr rfl fun j _ => by ring
            rw [hinner]; ring
        _ = (∑ i : Fin s, L (y + a) i * dotProduct x (B (Pi.single i 1))) +
            dotProduct c (L (y + a)) +
            ∑ i : Fin s, ∑ j : Fin s, M i j * L (y + a) i * L (y + a) j := by
            simp only [Finset.sum_add_distrib, dotProduct]
    rw [hterms]; ring
  have htotal : (∑ x : Fin k → F2, ∑ y : Fin k → F2,
      if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1) =
      (2 : ℤ) ^ k * ∑ v : Fin s → F2, if g (a + B v) = q v then (1 : ℤ) else -1 := by
    rw [Finset.sum_comm]
    have hinner : ∀ y : Fin k → F2,
        (∑ x : Fin k → F2, if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
          then (1 : ℤ) else -1) =
        if y + a ∈ LinearMap.range B then
          (2 : ℤ) ^ k * (if g y = q (L (y + a)) then (1 : ℤ) else -1)
        else 0 := by
      intro y
      have hrw : ∀ x : Fin k → F2,
          (if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1) then (1 : ℤ) else -1) =
          signBool (decide (dotProduct (a + B (L (y + a)) + y) x = 1)) *
            (if g y = q (L (y + a)) then (1 : ℤ) else -1) := by
        intro x
        rw [hCe x y, zmod2_add_decide (dotProduct x y) (g y), agree_eq_sign, eq_f2_sign]
        have hxor : Bool.xor (decide (dotProduct x (a + B (L (y + a))) + q (L (y + a)) = 1)) (decide (dotProduct x y = 1)) =
            Bool.xor (decide (dotProduct (a + B (L (y + a)) + y) x = 1)) (decide (q (L (y + a)) = 1)) := by
          rw [← zmod2_add_decide, ← zmod2_add_decide, add_dotProduct, dotProduct_comm (a + B (L (y + a))) x,
              dotProduct_comm y x]
          congr 1; ring
        rw [hxor, signBool_xor]
        ring
      simp_rw [hrw, ← Finset.sum_mul]
      by_cases hmem : y + a ∈ LinearMap.range B
      · simp only [hmem, ↓reduceIte]
        rcases hmem with ⟨v, hv⟩
        have hzero : a + B (L (y + a)) + y = 0 := by
          rw [← hv, hLB v, hv]
          calc a + (y + a) + y = (a + a) + (y + y) := by abel
            _ = 0 := by rw [zmod2_vec_add_self, zmod2_vec_add_self, add_zero]
        simp only [hzero, zero_dotProduct]
        have hcard : (∑ _x : Fin k → F2, signBool (decide ((0 : F2) = 1))) = (2 : ℤ) ^ k := by
          change (∑ _x : Fin k → F2, (1 : ℤ)) = (2 : ℤ) ^ k
          simp [ZMod.card]
        rw [hcard]
      · simp only [hmem, ↓reduceIte]
        have hne : a + B (L (y + a)) + y ≠ 0 := by
          intro h0
          apply hmem
          refine ⟨L (y + a), ?_⟩
          have h1 : B (L (y + a)) + (a + B (L (y + a)) + y) = y + a := by
            calc B (L (y + a)) + (a + B (L (y + a)) + y)
                = (B (L (y + a)) + B (L (y + a))) + (y + a) := by abel
              _ = y + a := by rw [zmod2_vec_add_self, zero_add]
          rw [h0, add_zero] at h1
          exact h1
        rw [sum_sign_dot_univ _ hne, zero_mul]
    simp_rw [hinner]
    rw [← Finset.sum_filter]
    let f_inj : (Fin s → F2) → (Fin k → F2) := fun v => a + B v
    have hbij : Finset.univ.image f_inj = Finset.univ.filter (fun y : Fin k → F2 => y + a ∈ LinearMap.range B) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, f_inj]
      constructor
      · rintro ⟨v, rfl⟩
        refine ⟨v, ?_⟩
        calc B v = (a + a) + B v := by rw [zmod2_vec_add_self, zero_add]
          _ = a + B v + a := by abel
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        calc a + B v = a + (y + a) := by rw [hv]
          _ = (a + a) + y := by abel
          _ = y := by rw [zmod2_vec_add_self, zero_add]
    rw [← hbij, Finset.sum_image (fun v1 _ v2 _ h => hB (add_left_cancel h)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have harg : f_inj v + a = B v := by
      dsimp only [f_inj]
      calc a + B v + a = (a + a) + B v := by abel
        _ = B v := by rw [zmod2_vec_add_self, zero_add]
    rw [harg, hLB v]
  rw [htotal, Int.natAbs_mul]
  have h2k : ((2 : ℤ) ^ k).natAbs = 2 ^ k := by
    rw [show (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) by push_cast; rfl, Int.natAbs_natCast]
  rw [h2k]
  exact hT

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

lemma viaCircuit_le_bound (k s : ℕ) (g : (Fin k → F2) → F2) (T : ℕ)
    (C : Circuit) (hleg : legalGates (2 * k) C.gates) (hcost : costGates C.gates ≤ s)
    (hT : T ≤ (∑ x : Fin k → F2, ∑ y : Fin k → F2,
      if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1).natAbs) :
    T ≤ 2 ^ (k + s) := by
  rcases forward_decomp_bounds k s g C hleg hcost with ⟨N, r, W, a, D, tap, _, hmeta, hsum, hB, hraw⟩
  dsimp only at hB hraw
  have hbound : ∑ i : Fin N, 2 ^ (k - r i) *
      (∑ y : Fin k → F2, if y - a i ∈ W i then
        signBool (Bool.xor ((D i).eval (bitsOf k y))
          (decide (dotProduct (fun j : Fin k => if ((D i).wires (bitsOf k y)).getD (tap i j) false then (1 : F2) else 0) y = 1))) *
          signBool (decide (g y = 1))
      else 0).natAbs ≤ ∑ i : Fin N, 2 ^ (k - r i) * 2 ^ s := by
    refine Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ ?_
    have hri : r i ≤ s := by have := (hmeta i).2.2.2.1; omega
    exact le_trans (hB i) (Nat.pow_le_pow_right (by omega) hri)
  have hrhs : ∑ i : Fin N, 2 ^ (k - r i) * 2 ^ s = 2 ^ (k + s) := by
    rw [← Finset.sum_mul, hsum, ← pow_add]
  exact le_trans hT (le_trans hraw (le_trans hbound (le_of_eq hrhs)))

lemma pivots_917 {X ι : Type} [AddCommGroup X] [Module F2 X] [FiniteDimensional F2 X]
    [Fintype ι] (bX : Module.Basis ι F2 X) (U : Submodule F2 X) :
    ∃ N : Finset ι, N.card ≤ Module.finrank F2 (X ⧸ U) ∧
      ∀ x : X, ∃ u ∈ U, ∀ t, t ∉ N → bX.repr (x - u) t = 0 := by
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' F2 (U.mkQ ∘ bX)
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have htop : Submodule.span F2 (Set.range ((U.mkQ ∘ bX) ∘ a)) = ⊤ := by
    rw [hsp, Set.range_comp, Submodule.span_image, bX.span_eq, Submodule.map_top,
      Submodule.range_mkQ]
  refine ⟨Finset.univ.image a, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ha, Finset.card_univ]
    exact hli.fintype_card_le_finrank
  · intro x
    have hx : U.mkQ x ∈ Submodule.span F2 (Set.range ((U.mkQ ∘ bX) ∘ a)) := by
      rw [htop]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F2).mp hx
    refine ⟨x - ∑ i, c i • bX (a i), ?_, ?_⟩
    · have h0 : U.mkQ (x - ∑ i, c i • bX (a i)) = 0 := by
        rw [map_sub, map_sum, ← hc]
        simp
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    · intro t ht
      have h : ∀ i, a i ≠ t := fun i hi => ht (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
      rw [sub_sub_cancel, map_sum]
      simp [h]

lemma selector_917 (k m r j : ℕ) (A : Fin m → (Fin k → F2))
    (W : Submodule F2
      ((Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2)))))
    (hW : 2 * m + r + j ≤ Module.finrank F2 W) :
    ∃ B : (Fin j → F2) →ₗ[F2] (Fin k → F2), Function.Injective B ∧
      (∀ a, ∃ w ∈ W, w.1 = B a) ∧
      ∀ b c : Fin m → F2, ∃ w ∈ W, w.1 = 0 ∧
        ∀ i : Fin m, (∃ a, dotProduct (A i) (B a) ≠ 0) → w.2.1 i = b i ∧ w.2.2.1 i = c i := by
  let X := (Fin m → F2) × ((Fin m → F2) × (Fin r → F2))
  let g : W →ₗ[F2] (Fin k → F2) := (LinearMap.fst _ _ _).comp W.subtype
  let P := LinearMap.range g
  let W0 : Submodule F2 X := W.comap (LinearMap.inr F2 (Fin k → F2) X)
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  let ι : LinearMap.ker g →ₗ[F2] W0 :=
    { toFun := fun w => ⟨w.1.1.2, by
        have h1 : w.1.1.1 = 0 := LinearMap.mem_ker.mp w.2
        show ((0 : Fin k → F2), w.1.1.2) ∈ W
        have : ((0 : Fin k → F2), w.1.1.2) = w.1.1 := Prod.ext h1.symm rfl
        rw [this]; exact w.1.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ι := by
    intro x y h
    have h2 : x.1.1.2 = y.1.1.2 := congrArg Subtype.val h
    have hx : x.1.1.1 = 0 := LinearMap.mem_ker.mp x.2
    have hy : y.1.1.1 = 0 := LinearMap.mem_ker.mp y.2
    exact Subtype.ext (Subtype.ext (Prod.ext (hx.trans hy.symm) h2))
  have hW0 := LinearMap.finrank_le_finrank_of_injective hinj
  let bX : Module.Basis (Fin m ⊕ (Fin m ⊕ Fin r)) F2 X :=
    (Pi.basisFun _ _).prod ((Pi.basisFun _ _).prod (Pi.basisFun _ _))
  obtain ⟨N, hN, hNx⟩ := pivots_917 bX W0
  have hq := W0.finrank_quotient_add_finrank
  have hX : Module.finrank F2 X = m + (m + r) := by simp [X]
  let T : Finset (Fin m) :=
    Finset.univ.filter (fun i => Sum.inl i ∈ N ∨ Sum.inr (Sum.inl i) ∈ N)
  have hT : T.card ≤ N.card := by
    let f : Fin m → Fin m ⊕ (Fin m ⊕ Fin r) :=
      fun i => if Sum.inl i ∈ N then Sum.inl i else Sum.inr (Sum.inl i)
    apply Finset.card_le_card_of_injOn f
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      simp only [f]
      split_ifs with h
      · exact h
      · exact hx'.resolve_left h
    · intro x _ y _ hxy
      simp only [f] at hxy
      split_ifs at hxy <;> simp_all
  let φ : (Fin k → F2) →ₗ[F2] (T → F2) :=
    Matrix.mulVecLin (Matrix.of fun (i : T) (s : Fin k) => A i.1 s)
  have hKmem : ∀ s ∈ LinearMap.ker φ, ∀ i ∈ T, dotProduct (A i) s = 0 := by
    intro s hs i hi
    have := congrFun (LinearMap.mem_ker.mp hs) ⟨i, hi⟩
    simpa [φ, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using this
  have hK := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : Module.finrank F2 (LinearMap.range φ) ≤ T.card := by
    have := Submodule.finrank_le (LinearMap.range φ)
    simpa using this
  have hS : Module.finrank F2 (Fin k → F2) = k := Module.finrank_fin_fun _
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq P (LinearMap.ker φ)
  have hsupl := Submodule.finrank_le (P ⊔ LinearMap.ker φ)
  have a1 : Module.finrank F2 (LinearMap.ker g) ≤ Module.finrank F2 W0 := hW0
  have a2 : Module.finrank F2 (X ⧸ W0) + Module.finrank F2 W0 = m + (m + r) := hq.trans hX
  have a3 : Module.finrank F2 P + Module.finrank F2 (LinearMap.ker g) = Module.finrank F2 W := hrn
  have a4 : Module.finrank F2 (LinearMap.range φ) + Module.finrank F2 (LinearMap.ker φ) = k :=
    hK.trans hS
  have a5 : Module.finrank F2 ↥(P ⊔ LinearMap.ker φ) ≤ k := hsupl.trans hS.le
  have a6 : Module.finrank F2 ↥(P ⊔ LinearMap.ker φ) + Module.finrank F2 ↥(P ⊓ LinearMap.ker φ)
      = Module.finrank F2 P + Module.finrank F2 (LinearMap.ker φ) := hsup
  have a7 : N.card ≤ Module.finrank F2 (X ⧸ W0) := hN
  have hR : j ≤ Module.finrank F2 ↥(P ⊓ LinearMap.ker φ) := by omega
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hR
  have hf' : LinearIndependent F2 (fun t => (f t : Fin k → F2)) :=
    hf.map' (P ⊓ LinearMap.ker φ).subtype (Submodule.ker_subtype _)
  let B : (Fin j → F2) →ₗ[F2] (Fin k → F2) :=
    { toFun := fun a => ∑ t, a t • (f t : Fin k → F2)
      map_add' := by intro x y; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.smul_sum, smul_smul] }
  have hBR : ∀ a, B a ∈ P ⊓ LinearMap.ker φ := fun a => show ∑ t, a t • _ ∈ _ from
    Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (f t).2)
  refine ⟨B, ?_, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero B).mpr ?_
    intro a ha
    funext t
    exact Fintype.linearIndependent_iff.mp hf' a ha t
  · intro a
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (Submodule.mem_inf.mp (hBR a)).1
    exact ⟨w.1, w.2, hw⟩
  · intro b c
    obtain ⟨u, hu, hu'⟩ := hNx ((b, c, 0) : X)
    refine ⟨(0, u), hu, rfl, ?_⟩
    rintro i ⟨a, ha⟩
    have hiT : i ∉ T := fun hi => ha (hKmem (B a) (Submodule.mem_inf.mp (hBR a)).2 i hi)
    have h1 : (Sum.inl i : Fin m ⊕ (Fin m ⊕ Fin r)) ∉ N := fun h => hiT (by simp [T, h])
    have h2 : (Sum.inr (Sum.inl i) : Fin m ⊕ (Fin m ⊕ Fin r)) ∉ N :=
      fun h => hiT (by simp [T, h])
    have e1 := hu' _ h1
    have e2 := hu' _ h2
    simp only [bX] at e1 e2
    exact ⟨(sub_eq_zero.mp e1).symm, (sub_eq_zero.mp e2).symm⟩

lemma symm_zero_diag_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (M : ι → ι → F2) (hdiag : ∀ i, M i i = 0) (hsymm : ∀ i j, M i j = M j i) :
    ∑ i ∈ s, ∑ j ∈ s, M i j = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hinner : ∀ i ∈ s, ∑ j ∈ insert a s, M i j = M i a + ∑ j ∈ s, M i j := by
      intro i _
      rw [Finset.sum_insert ha]
    rw [Finset.sum_insert ha, Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ih, hdiag a,
      zero_add, add_zero]
    have hswap : ∑ i ∈ s, M i a = ∑ j ∈ s, M a j := by
      apply Finset.sum_congr rfl
      intro i _
      exact hsymm i a
    rw [hswap]
    exact z2_add_self _

def radSub {r : ℕ}
    (B : (Fin r → F2) →ₗ[F2] (Fin r → F2) →ₗ[F2] F2)
    (U : Submodule F2 (Fin r → F2)) : Submodule F2 (Fin r → F2) :=
  { carrier := {u | u ∈ U ∧ ∀ v ∈ U, B u v = 0}, add_mem' := by
      intro a b ha hb
      refine ⟨U.add_mem ha.1 hb.1, fun v hv => ?_⟩
      rw [map_add, LinearMap.add_apply, ha.2 v hv, hb.2 v hv, add_zero]
    zero_mem' := ⟨U.zero_mem, fun _ _ => by simp⟩
    smul_mem' := by
      intro s a ha
      refine ⟨U.smul_mem s ha.1, fun v hv => ?_⟩
      rw [map_smul, LinearMap.smul_apply, ha.2 v hv, smul_zero] }

lemma even_codim_rad {r : ℕ}
    (B : (Fin r → F2) →ₗ[F2] (Fin r → F2) →ₗ[F2] F2)
    (halt : ∀ v, B v v = 0)
    (hsymm : ∀ u v, B u v = B v u)
    (W : Submodule F2 (Fin r → F2)) :
    Even (Module.finrank F2 W - Module.finrank F2 (radSub B W)) := by
  let radOf := radSub B
  have hstrong : ∀ k : ℕ, ∀ U : Submodule F2 (Fin r → F2),
      Module.finrank F2 U = k →
      Even (Module.finrank F2 U - Module.finrank F2 (radOf U)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro U hk
      by_cases htriv : ∀ u ∈ U, ∀ v ∈ U, B u v = 0
      · have heq : radOf U = U := by
          ext u
          exact ⟨fun h => h.1, fun hu => ⟨hu, htriv u hu⟩⟩
        rw [heq, Nat.sub_self]
        exact ⟨0, rfl⟩
      · push Not at htriv
        obtain ⟨u, huU, v, hvU, huv_ne⟩ := htriv
        have huv : B u v = 1 := z2_eq_one_of_ne_zero huv_ne
        have hvu : B v u = 1 := by rw [hsymm, huv]
        let φ : U →ₗ[F2] (F2 × F2) :=
          { toFun := fun w => (B u w.1, B v w.1)
            map_add' := fun a b => by
              apply Prod.ext <;> simp only [Submodule.coe_add, map_add, Prod.fst_add, Prod.snd_add]
            map_smul' := fun s a => by
              apply Prod.ext <;> simp only [SetLike.val_smul, map_smul, Prod.smul_fst,
                Prod.smul_snd, RingHom.id_apply] }
        have hφ_surj : Function.Surjective φ := by
          intro ⟨a, b⟩
          refine ⟨a • ⟨v, hvU⟩ + b • ⟨u, huU⟩, ?_⟩
          apply Prod.ext
          · change B u (a • v + b • u) = a
            rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, huv, halt u,
              mul_one, mul_zero, add_zero]
          · change B v (a • v + b • u) = b
            rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hvu, halt v,
              mul_zero, mul_one, zero_add]
        have hrange_φ : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
        have hrank_φ : Module.finrank F2 (LinearMap.range φ) = 2 := by
          rw [hrange_φ, finrank_top, Module.finrank_prod, Module.finrank_self]
        have hrn := LinearMap.finrank_range_add_finrank_ker φ
        rw [hrank_φ] at hrn
        let U' : Submodule F2 (Fin r → F2) :=
          { carrier := {w | w ∈ U ∧ B u w = 0 ∧ B v w = 0}, add_mem' := by
              intro a b ha hb
              refine ⟨U.add_mem ha.1 hb.1, ?_, ?_⟩
              · rw [map_add, ha.2.1, hb.2.1, add_zero]
              · rw [map_add, ha.2.2, hb.2.2, add_zero]
            zero_mem' := ⟨U.zero_mem, by simp, by simp⟩
            smul_mem' := by
              intro s a ha
              refine ⟨U.smul_mem s ha.1, ?_, ?_⟩
              · rw [map_smul, ha.2.1, smul_zero]
              · rw [map_smul, ha.2.2, smul_zero] }
        let eker : LinearMap.ker φ ≃ₗ[F2] U' :=
          { toFun := fun w => ⟨w.1.1, w.1.2, by
              have hw : φ w.1 = 0 := w.2
              exact ⟨congrArg Prod.fst hw, congrArg Prod.snd hw⟩⟩
            invFun := fun w => ⟨⟨w.1, w.2.1⟩, by
              change φ ⟨w.1, w.2.1⟩ = 0
              exact Prod.ext w.2.2.1 w.2.2.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        have hdimU' : Module.finrank F2 U' = Module.finrank F2 (LinearMap.ker φ) :=
          eker.finrank_eq.symm
        have hrad_eq : radOf U' = radOf U := by
          ext x
          constructor
          · intro hx
            refine ⟨hx.1.1, fun w hw => ?_⟩
            let w' := w + B u w • v + B v w • u
            have hw'U : w' ∈ U :=
              U.add_mem (U.add_mem hw (U.smul_mem _ hvU)) (U.smul_mem _ huU)
            have hBuw' : B u w' = 0 := by
              dsimp only [w']
              rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
                huv, halt u, mul_one, mul_zero, add_zero]
              exact z2_add_self _
            have hBvw' : B v w' = 0 := by
              dsimp only [w']
              rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
                hvu, halt v, mul_one, mul_zero, add_zero]
              exact z2_add_self _
            have hBxw' : B x w' = 0 := hx.2 w' ⟨hw'U, hBuw', hBvw'⟩
            have hBxu : B x u = 0 := by rw [hsymm]; exact hx.1.2.1
            have hBxv : B x v = 0 := by rw [hsymm]; exact hx.1.2.2
            dsimp only [w'] at hBxw'
            rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
              hBxv, hBxu, mul_zero, mul_zero, add_zero, add_zero] at hBxw'
            exact hBxw'
          · intro hx
            refine ⟨⟨hx.1, ?_, ?_⟩, fun w hw => hx.2 w hw.1⟩
            · rw [hsymm]; exact hx.2 u huU
            · rw [hsymm]; exact hx.2 v hvU
        have hle_rad : Module.finrank F2 (radOf U') ≤ Module.finrank F2 U' :=
          Submodule.finrank_mono (fun _ hx => hx.1)
        have hU'_lt : Module.finrank F2 U' < k := by omega
        have hev' := ih (Module.finrank F2 U') hU'_lt U' rfl
        rw [hrad_eq] at hev' hle_rad
        rcases hev' with ⟨t, ht⟩
        refine ⟨t + 1, ?_⟩
        omega
  exact hstrong (Module.finrank F2 W) W rfl

lemma even_finrank_range_alt {r : ℕ}
    (A : (Fin r → F2) →ₗ[F2] (Fin r → F2))
    (halt : ∀ v, dotProduct v (A v) = 0) :
    Even (Module.finrank F2 (LinearMap.range A)) := by
  have hsymm : ∀ u v, dotProduct u (A v) = dotProduct v (A u) := by
    intro u v
    have h := halt (u + v)
    rw [map_add, add_dotProduct, dotProduct_add, dotProduct_add, halt u, halt v,
      zero_add, add_zero] at h
    exact z2_eq_of_add_eq_zero h
  let B : (Fin r → F2) →ₗ[F2] (Fin r → F2) →ₗ[F2] F2 :=
    { toFun := fun u =>
        { toFun := fun v => dotProduct u (A v)
          map_add' := fun v₁ v₂ => by rw [map_add, dotProduct_add]
          map_smul' := fun s v => by rw [map_smul, dotProduct_smul, RingHom.id_apply] }
      map_add' := fun u₁ u₂ => by
        apply LinearMap.ext; intro v; exact add_dotProduct u₁ u₂ (A v)
      map_smul' := fun s u => by
        apply LinearMap.ext; intro v; exact smul_dotProduct s u (A v) }
  have hrad : radSub B ⊤ = LinearMap.ker A := by
    ext u
    change (u ∈ (⊤ : Submodule F2 (Fin r → F2)) ∧
      ∀ v ∈ (⊤ : Submodule F2 (Fin r → F2)), dotProduct u (A v) = 0) ↔ A u = 0
    constructor
    · intro h
      funext a
      have ha := h.2 (Pi.single a 1) Submodule.mem_top
      rw [hsymm, single_dotProduct, one_mul] at ha
      exact ha
    · intro h
      refine ⟨Submodule.mem_top, fun v _ => ?_⟩
      rw [hsymm, h, dotProduct_zero]
  have hev := even_codim_rad B halt hsymm ⊤
  rw [hrad, finrank_top] at hev
  have hrn := LinearMap.finrank_range_add_finrank_ker A
  have hsub : Module.finrank F2 (Fin r → F2) - Module.finrank F2 (LinearMap.ker A) =
      Module.finrank F2 (LinearMap.range A) := by omega
  rwa [hsub] at hev

lemma even_rank {n : ℕ} (A : Matrix (Fin n) (Fin n) F2) (hd : ∀ i, A i i = 0)
    (hs : ∀ i j, A i j = A j i) : Even A.rank := by
  apply even_finrank_range_alt A.mulVecLin
  intro v
  rw [Matrix.mulVecLin_apply]
  have h := symm_zero_diag_sum Finset.univ (fun i j => v i * A i j * v j)
    (fun i => by show v i * A i i * v i = 0; rw [hd]; ring)
    (fun i j => by show v i * A i j * v j = v j * A j i * v i; rw [hs i j]; ring)
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [← h]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma rank_add_le' {n : ℕ} (A B : Matrix (Fin n) (Fin n) F2) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.add_mulVec]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

def pairIdx {m : ℕ} (t : Fin m) (b : Bool) : Fin (2 * m) :=
  if b then ⟨2 * t.val + 1, by omega⟩ else ⟨2 * t.val, by omega⟩

def pairEquiv (m : ℕ) : Fin m × Bool ≃ Fin (2 * m) :=
  { toFun := fun p => pairIdx p.1 p.2
    invFun := fun idx => (⟨idx.val / 2, by omega⟩, decide (idx.val % 2 = 1))
    left_inv := fun ⟨t, b⟩ => by
      cases b
      · apply Prod.ext
        · apply Fin.ext; simp [pairIdx]
        · simp [pairIdx]
      · apply Prod.ext
        · apply Fin.ext; simp [pairIdx]; omega
        · simp [pairIdx]
    right_inv := fun idx => by
      apply Fin.ext
      dsimp only [pairIdx]
      by_cases h : idx.val % 2 = 1
      · simp only [h, decide_true, ↓reduceIte]; omega
      · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; omega }

def diagPair {m : ℕ} (d : Fin m → F2) : Matrix (Fin (2 * m)) (Fin (2 * m)) F2 :=
  Matrix.of fun i j =>
    if i.val / 2 = j.val / 2 ∧ i ≠ j then d ⟨i.val / 2, by omega⟩ else 0

lemma diagPair_diag {m : ℕ} (d : Fin m → F2) (i : Fin (2 * m)) : diagPair d i i = 0 := by
  simp [diagPair]

lemma diagPair_symm {m : ℕ} (d : Fin m → F2) (i j : Fin (2 * m)) :
    diagPair d i j = diagPair d j i := by
  simp only [diagPair, Matrix.of_apply]
  by_cases h : i.val / 2 = j.val / 2 ∧ i ≠ j
  · have h' : j.val / 2 = i.val / 2 ∧ j ≠ i := ⟨h.1.symm, h.2.symm⟩
    rw [if_pos h, if_pos h']
    congr 1; exact Fin.ext h.1
  · have h' : ¬ (j.val / 2 = i.val / 2 ∧ j ≠ i) := fun ⟨a, b⟩ => h ⟨a.symm, b.symm⟩
    rw [if_neg h, if_neg h']

lemma diagPair_add {m : ℕ} (d1 d2 : Fin m → F2) :
    diagPair (d1 + d2) = diagPair d1 + diagPair d2 := by
  ext i j
  simp only [diagPair, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

def hamWt {m : ℕ} (v : Fin m → F2) : ℕ :=
  (Finset.univ.filter (fun t => v t ≠ 0)).card

def hamDist {m : ℕ} (u v : Fin m → F2) : ℕ :=
  hamWt (u + v)

lemma sum_fin_support1 {N : ℕ} (a : Fin N) (f : Fin N → F2) (hf : ∀ j, j ≠ a → f j = 0) :
    ∑ j : Fin N, f j = f a := by
  rw [← Finset.sum_subset (Finset.subset_univ {a})]
  · simp
  · intro j _ hj; exact hf j (by simpa using hj)

lemma sum_fin_support3 {N : ℕ} {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f : Fin N → F2) (hf : ∀ j, j ≠ a → j ≠ b → j ≠ c → f j = 0) :
    ∑ j : Fin N, f j = f a + f b + f c := by
  rw [← Finset.sum_subset (Finset.subset_univ {a, b, c})]
  · rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]), Finset.sum_singleton]
    ring
  · intro j _ hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    exact hf j hj.1 hj.2.1 hj.2.2

lemma rank_mul_invol_left {N : ℕ} (P A : Matrix (Fin N) (Fin N) F2) (hP : P * P = 1) :
    (P * A).rank = A.rank := by
  let eP : (Fin N → F2) ≃ₗ[F2] (Fin N → F2) :=
    { toLinearMap := P.mulVecLin
      invFun := P.mulVecLin
      left_inv := fun v => by
        show P *ᵥ (P *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
      right_inv := fun v => by
        show P *ᵥ (P *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec] }
  have hcomp : (P * A).mulVecLin = eP.toLinearMap.comp A.mulVecLin := by
    ext v i; simp [eP, Matrix.mulVec_mulVec]
  unfold Matrix.rank
  rw [hcomp, LinearMap.range_comp]
  exact LinearEquiv.finrank_map_eq eP (LinearMap.range A.mulVecLin)

lemma rank_mul_invol_right {N : ℕ} (A P : Matrix (Fin N) (Fin N) F2) (hP : P * P = 1) :
    (A * P).rank = A.rank := by
  let eP : (Fin N → F2) ≃ₗ[F2] (Fin N → F2) :=
    { toLinearMap := P.mulVecLin
      invFun := P.mulVecLin
      left_inv := fun v => by
        show P *ᵥ (P *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
      right_inv := fun v => by
        show P *ᵥ (P *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec] }
  have hcomp : (A * P).mulVecLin = A.mulVecLin.comp eP.toLinearMap := by
    ext v i; simp [eP, Matrix.mulVec_mulVec]
  unfold Matrix.rank
  rw [hcomp, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range eP)]

lemma schur_hamming_center : ∀ (m : ℕ) (K : Matrix (Fin (2 * m)) (Fin (2 * m)) F2),
    (∀ i, K i i = 0) → (∀ i j, K i j = K j i) →
    ∃ z0 : Fin m → F2, ∀ d : Fin m → F2, 2 * hamDist d z0 ≤ (K + diagPair d).rank := by
  intro m
  induction m with
  | zero =>
    intro K _ _
    refine ⟨Fin.elim0, fun d => ?_⟩
    have h0 : hamDist d Fin.elim0 = 0 := by simp [hamDist, hamWt]
    rw [h0]; simp
  | succ m' ih =>
    intro K hKd hKs
    let i0 : Fin (2 * (m' + 1)) := ⟨0, by omega⟩
    let i1 : Fin (2 * (m' + 1)) := ⟨1, by omega⟩
    let sh : Fin (2 * m') → Fin (2 * (m' + 1)) := fun i => ⟨i.val + 2, by omega⟩
    let a0 : F2 := K i0 i1
    let K' : Matrix (Fin (2 * m')) (Fin (2 * m')) F2 := Matrix.of fun i j =>
      K (sh i) (sh j) + K i0 (sh i) * K i1 (sh j) + K i1 (sh i) * K i0 (sh j)
    have hK'd : ∀ i, K' i i = 0 := by
      intro i
      simp only [K', Matrix.of_apply, hKd (sh i), zero_add]
      have hcomm : K i1 (sh i) * K i0 (sh i) = K i0 (sh i) * K i1 (sh i) := mul_comm _ _
      rw [hcomm]; exact z2_add_self _
    have hK's : ∀ i j, K' i j = K' j i := by
      intro i j
      simp only [K', Matrix.of_apply, hKs (sh i) (sh j)]
      ring
    rcases ih K' hK'd hK's with ⟨z', hz'⟩
    let z0 : Fin (m' + 1) → F2 := Fin.cons a0 z'
    refine ⟨z0, fun d => ?_⟩
    let d' : Fin m' → F2 := Fin.tail d
    let M1 : Matrix (Fin (2 * (m' + 1))) (Fin (2 * (m' + 1))) F2 :=
      K + diagPair (Fin.cons (a0 + 1) d')
    have hM1_00 : M1 i0 i0 = 0 := by simp [M1, hKd, diagPair]
    have hM1_11 : M1 i1 i1 = 0 := by simp [M1, hKd, diagPair]
    have hM1_01 : M1 i0 i1 = 1 := by
      have hne : i0 ≠ i1 := fun h => by have := congrArg Fin.val h; simp [i0, i1] at this
      have hdiv : i0.val / 2 = i1.val / 2 := by simp [i0, i1]
      have hcond : i0.val / 2 = i1.val / 2 ∧ i0 ≠ i1 := ⟨hdiv, hne⟩
      simp only [M1, Matrix.add_apply, diagPair, Matrix.of_apply]
      rw [ite_eq_left_iff.mpr (fun hn => absurd hcond hn)]
      have h0 : (⟨i0.val / 2, by omega⟩ : Fin (m' + 1)) = 0 := Fin.ext (by simp [i0])
      rw [h0, Fin.cons_zero]
      change a0 + (a0 + 1) = 1
      rw [← add_assoc, z2_add_self, zero_add]
    have hM1_10 : M1 i1 i0 = 1 := by
      have hne : i1 ≠ i0 := fun h => by have := congrArg Fin.val h; simp [i0, i1] at this
      have hdiv : i1.val / 2 = i0.val / 2 := by simp [i0, i1]
      have hcond : i1.val / 2 = i0.val / 2 ∧ i1 ≠ i0 := ⟨hdiv, hne⟩
      simp only [M1, Matrix.add_apply, diagPair, Matrix.of_apply]
      rw [ite_eq_left_iff.mpr (fun hn => absurd hcond hn)]
      have h0 : (⟨i1.val / 2, by omega⟩ : Fin (m' + 1)) = 0 := Fin.ext (by simp [i1])
      rw [h0, Fin.cons_zero, hKs i1 i0]
      change a0 + (a0 + 1) = 1
      rw [← add_assoc, z2_add_self, zero_add]
    have hM1_0s : ∀ j : Fin (2 * m'), M1 i0 (sh j) = K i0 (sh j) := by
      intro j
      simp only [M1, Matrix.add_apply, diagPair, Matrix.of_apply]
      have hnot : ¬ (i0.val / 2 = (sh j).val / 2 ∧ i0 ≠ sh j) := by
        intro h; have := h.1; simp [i0, sh] at this
      simp [hnot]
    have hM1_1s : ∀ j : Fin (2 * m'), M1 i1 (sh j) = K i1 (sh j) := by
      intro j
      simp only [M1, Matrix.add_apply, diagPair, Matrix.of_apply]
      have hnot : ¬ (i1.val / 2 = (sh j).val / 2 ∧ i1 ≠ sh j) := by
        intro h; have := h.1; simp [i1, sh] at this
      simp [hnot]
    have hM1_s0 : ∀ i : Fin (2 * m'), M1 (sh i) i0 = K i0 (sh i) := by
      intro i
      simp only [M1, Matrix.add_apply, diagPair, Matrix.of_apply, hKs (sh i) i0]
      have hnot : ¬ ((sh i).val / 2 = i0.val / 2 ∧ sh i ≠ i0) := by
        intro h; have := h.1; simp [i0, sh] at this
      simp [hnot]
    have hM1_s1 : ∀ i : Fin (2 * m'), M1 (sh i) i1 = K i1 (sh i) := by
      intro i
      simp only [M1, Matrix.add_apply, diagPair, Matrix.of_apply, hKs (sh i) i1]
      have hnot : ¬ ((sh i).val / 2 = i1.val / 2 ∧ sh i ≠ i1) := by
        intro h; have := h.1; simp [i1, sh] at this
      simp [hnot]
    have hM1_ss : ∀ i j : Fin (2 * m'), M1 (sh i) (sh j) = K (sh i) (sh j) + diagPair d' i j := by
      intro i j
      simp only [M1, Matrix.add_apply, diagPair, Matrix.of_apply]
      congr 1
      have hdiv : ((sh i).val / 2 = (sh j).val / 2) ↔ (i.val / 2 = j.val / 2) := by
        simp only [sh]; omega
      have hne : (sh i ≠ sh j) ↔ (i ≠ j) := by
        simp only [ne_eq, Fin.ext_iff, sh]; omega
      by_cases h : i.val / 2 = j.val / 2 ∧ i ≠ j
      · have hs : (sh i).val / 2 = (sh j).val / 2 ∧ sh i ≠ sh j := ⟨hdiv.mpr h.1, hne.mpr h.2⟩
        rw [ite_eq_left_iff.mpr (fun hn => absurd hs hn), ite_eq_left_iff.mpr (fun hn => absurd h hn)]
        have hidx : (⟨(sh i).val / 2, by omega⟩ : Fin (m' + 1)) = (⟨i.val / 2, by omega⟩ : Fin m').succ := by
          apply Fin.ext; simp [sh]
        rw [hidx, Fin.cons_succ]
      · have hs : ¬ ((sh i).val / 2 = (sh j).val / 2 ∧ sh i ≠ sh j) :=
          fun ⟨a, b⟩ => h ⟨hdiv.mp a, hne.mp b⟩
        rw [ite_eq_right_iff.mpr (fun hp => absurd hp hs), ite_eq_right_iff.mpr (fun hp => absurd hp h)]
    let L : Matrix (Fin (2 * (m' + 1))) (Fin (2 * (m' + 1))) F2 := Matrix.of fun i j =>
      if i = j then 1
      else if 2 ≤ i.val then
        if j = i0 then K i1 i
        else if j = i1 then K i0 i
        else 0
      else 0
    have hLL : L * L = 1 := by
      ext i k
      rw [Matrix.mul_apply, Matrix.one_apply]
      by_cases hi2 : 2 ≤ i.val
      · have hi0 : i ≠ i0 := fun h => by subst h; simp [i0] at hi2
        have hi1 : i ≠ i1 := fun h => by subst h; simp [i1] at hi2
        have h01 : i0 ≠ i1 := fun h => by have := congrArg Fin.val h; simp [i0, i1] at this
        rw [sum_fin_support3 hi0 hi1 h01 (fun j => L i j * L j k)]
        · have hLi : L i i = 1 := by simp [L]
          have hL0 : L i i0 = K i1 i := by simp [L, hi0, hi2]
          have hL1 : L i i1 = K i0 i := by simp [L, hi1, hi2, h01.symm]
          have h0k : L i0 k = if i0 = k then 1 else 0 := by
            dsimp only [L, Matrix.of_apply]
            have hn2 : ¬ (2 ≤ i0.val) := by simp [i0]
            by_cases h : i0 = k
            · simp [h]
            · rw [ite_eq_right_iff.mpr (fun hp => absurd hp h), ite_eq_right_iff.mpr (fun hp => absurd hp hn2),
                ite_eq_right_iff.mpr (fun hp => absurd hp h)]
          have h1k : L i1 k = if i1 = k then 1 else 0 := by
            dsimp only [L, Matrix.of_apply]
            have hn2 : ¬ (2 ≤ i1.val) := by simp [i1]
            by_cases h : i1 = k
            · simp [h]
            · rw [ite_eq_right_iff.mpr (fun hp => absurd hp h), ite_eq_right_iff.mpr (fun hp => absurd hp hn2),
                ite_eq_right_iff.mpr (fun hp => absurd hp h)]
          rw [hLi, hL0, hL1, h0k, h1k, one_mul]
          by_cases hik : i = k
          · subst hik
            simp [L, hi0.symm, hi1.symm]
          · by_cases hk0 : i0 = k
            · subst hk0
              simp only [hik, ↓reduceIte, h01, h01.symm, mul_one, mul_zero, add_zero]
              rw [hL0]; exact z2_add_self _
            · by_cases hk1 : i1 = k
              · subst hk1
                simp only [hik, ↓reduceIte, h01, h01.symm, mul_one, mul_zero, add_zero]
                rw [hL1]; exact z2_add_self _
              · simp [L, hik, hi2, hk0, hk1, Ne.symm hk0, Ne.symm hk1]
        · intro j hji hj0 hj1
          have hLij : L i j = 0 := by simp [L, Ne.symm hji, hi2, hj0, hj1]
          rw [hLij, zero_mul]
      · rw [sum_fin_support1 i (fun j => L i j * L j k)]
        · have hLii : L i i = 1 := by simp [L]
          have hLik : L i k = if i = k then 1 else 0 := by simp [L, hi2]
          rw [hLii, one_mul, hLik]
        · intro j hji
          have hLij : L i j = 0 := by simp [L, Ne.symm hji, hi2]
          rw [hLij, zero_mul]
    have hLtLt : Lᵀ * Lᵀ = 1 := by
      rw [← Matrix.transpose_mul, hLL, Matrix.transpose_one]
    let N : Matrix (Fin (2 * (m' + 1))) (Fin (2 * (m' + 1))) F2 := L * M1 * Lᵀ
    have hNrank : N.rank = M1.rank := by
      dsimp only [N]
      rw [rank_mul_invol_right (L * M1) Lᵀ hLtLt, rank_mul_invol_left L M1 hLL]
    let A' : Matrix (Fin (2 * m')) (Fin (2 * m')) F2 := K' + diagPair d'
    have hLM1 : ∀ i j : Fin (2 * (m' + 1)),
        (L * M1) i j =
          if 2 ≤ i.val then M1 i j + K i1 i * M1 i0 j + K i0 i * M1 i1 j
          else M1 i j := by
      intro i j
      rw [Matrix.mul_apply]
      by_cases hi2 : 2 ≤ i.val
      · simp only [hi2, ↓reduceIte]
        have hi0 : i ≠ i0 := fun h => by subst h; simp [i0] at hi2
        have hi1 : i ≠ i1 := fun h => by subst h; simp [i1] at hi2
        have h01 : i0 ≠ i1 := fun h => by have := congrArg Fin.val h; simp [i0, i1] at this
        rw [sum_fin_support3 hi0 hi1 h01 (fun r => L i r * M1 r j)]
        · have hLi : L i i = 1 := by simp [L]
          have hL0 : L i i0 = K i1 i := by simp [L, hi0, hi2]
          have hL1 : L i i1 = K i0 i := by simp [L, hi1, hi2, h01.symm]
          rw [hLi, hL0, hL1, one_mul]
        · intro r hri hr0 hr1
          have hLir : L i r = 0 := by simp [L, Ne.symm hri, hi2, hr0, hr1]
          rw [hLir, zero_mul]
      · simp only [hi2, ↓reduceIte]
        rw [sum_fin_support1 i (fun r => L i r * M1 r j)]
        · have hLii : L i i = 1 := by simp [L]
          rw [hLii, one_mul]
        · intro r hri
          have hLir : L i r = 0 := by simp [L, Ne.symm hri, hi2]
          rw [hLir, zero_mul]
    have hLM1_s0 : ∀ i : Fin (2 * m'), (L * M1) (sh i) i0 = 0 := by
      intro i
      rw [hLM1]
      have hi2 : 2 ≤ (sh i).val := by simp [sh]
      simp only [hi2, ↓reduceIte, hM1_s0, hM1_00, hM1_10, mul_zero, mul_one, add_zero]
      exact z2_add_self _
    have hLM1_s1 : ∀ i : Fin (2 * m'), (L * M1) (sh i) i1 = 0 := by
      intro i
      rw [hLM1]
      have hi2 : 2 ≤ (sh i).val := by simp [sh]
      simp only [hi2, ↓reduceIte, hM1_s1, hM1_01, hM1_11, mul_zero, mul_one, add_zero]
      exact z2_add_self _
    have hN_apply : ∀ i k : Fin (2 * (m' + 1)),
        N i k =
          if 2 ≤ k.val then (L * M1) i k + (L * M1) i i0 * K i1 k + (L * M1) i i1 * K i0 k
          else (L * M1) i k := by
      intro i k
      dsimp only [N]
      rw [Matrix.mul_apply]
      by_cases hk2 : 2 ≤ k.val
      · simp only [hk2, ↓reduceIte]
        have hk0 : k ≠ i0 := fun h => by subst h; simp [i0] at hk2
        have hk1 : k ≠ i1 := fun h => by subst h; simp [i1] at hk2
        have h01 : i0 ≠ i1 := fun h => by have := congrArg Fin.val h; simp [i0, i1] at this
        rw [sum_fin_support3 hk0 hk1 h01 (fun r => (L * M1) i r * Lᵀ r k)]
        · simp only [Matrix.transpose_apply]
          have hLk : L k k = 1 := by simp [L]
          have hL0 : L k i0 = K i1 k := by simp [L, hk0, hk2]
          have hL1 : L k i1 = K i0 k := by simp [L, hk1, hk2, h01.symm]
          rw [hLk, hL0, hL1, mul_one]
        · intro r hrk hr0 hr1
          simp only [Matrix.transpose_apply]
          have hLkr : L k r = 0 := by simp [L, Ne.symm hrk, hk2, hr0, hr1]
          rw [hLkr, mul_zero]
      · simp only [hk2, ↓reduceIte]
        rw [sum_fin_support1 k (fun r => (L * M1) i r * Lᵀ r k)]
        · simp only [Matrix.transpose_apply]
          have hLkk : L k k = 1 := by simp [L]
          rw [hLkk, mul_one]
        · intro r hrk
          simp only [Matrix.transpose_apply]
          have hLkr : L k r = 0 := by simp [L, Ne.symm hrk, hk2]
          rw [hLkr, mul_zero]
    have hi0_not2 : ¬ (2 ≤ i0.val) := by simp [i0]
    have hi1_not2 : ¬ (2 ≤ i1.val) := by simp [i1]
    have hN_00 : N i0 i0 = 0 := by
      rw [hN_apply]; simp only [hi0_not2, ↓reduceIte]; rw [hLM1]; simp only [hi0_not2, ↓reduceIte]; exact hM1_00
    have hN_01 : N i0 i1 = 1 := by
      rw [hN_apply]; simp only [hi1_not2, ↓reduceIte]; rw [hLM1]; simp only [hi0_not2, ↓reduceIte]; exact hM1_01
    have hN_10 : N i1 i0 = 1 := by
      rw [hN_apply]; simp only [hi0_not2, ↓reduceIte]; rw [hLM1]; simp only [hi1_not2, ↓reduceIte]; exact hM1_10
    have hN_11 : N i1 i1 = 0 := by
      rw [hN_apply]; simp only [hi1_not2, ↓reduceIte]; rw [hLM1]; simp only [hi1_not2, ↓reduceIte]; exact hM1_11
    have hN_0s : ∀ k : Fin (2 * m'), N i0 (sh k) = 0 := by
      intro k
      rw [hN_apply]
      have hk2 : 2 ≤ (sh k).val := by simp [sh]
      simp only [hk2, ↓reduceIte, hLM1, hi0_not2,
        hM1_0s, hM1_00, hM1_01, zero_mul, one_mul, add_zero]
      exact z2_add_self _
    have hN_1s : ∀ k : Fin (2 * m'), N i1 (sh k) = 0 := by
      intro k
      rw [hN_apply]
      have hk2 : 2 ≤ (sh k).val := by simp [sh]
      simp only [hk2, ↓reduceIte, hLM1, hi1_not2,
        hM1_1s, hM1_10, hM1_11, zero_mul, one_mul, add_zero]
      exact z2_add_self _
    have hN_s0 : ∀ i : Fin (2 * m'), N (sh i) i0 = 0 := by
      intro i; rw [hN_apply]; simp only [hi0_not2, ↓reduceIte]; exact hLM1_s0 i
    have hN_s1 : ∀ i : Fin (2 * m'), N (sh i) i1 = 0 := by
      intro i; rw [hN_apply]; simp only [hi1_not2, ↓reduceIte]; exact hLM1_s1 i
    have hN_ss : ∀ i k : Fin (2 * m'), N (sh i) (sh k) = A' i k := by
      intro i k
      rw [hN_apply]
      have hi2 : 2 ≤ (sh i).val := by simp [sh]
      have hk2 : 2 ≤ (sh k).val := by simp [sh]
      simp only [hk2, ↓reduceIte, hLM1_s0, hLM1_s1, zero_mul, add_zero]
      rw [hLM1]
      simp only [hi2, ↓reduceIte, hM1_ss, hM1_0s, hM1_1s, A', K', Matrix.add_apply, Matrix.of_apply]
      ring
    have hN_mv0 : ∀ v : Fin (2 * (m' + 1)) → F2, (N *ᵥ v) i0 = v i1 := by
      intro v
      simp only [Matrix.mulVec, dotProduct]
      rw [sum_fin_support1 i1 (fun j => N i0 j * v j)]
      · rw [hN_01, one_mul]
      · intro j hj1
        by_cases hj0 : j = i0
        · subst hj0; rw [hN_00, zero_mul]
        · have hj2 : 2 ≤ j.val := by
            have h0 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
            have h1 : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
            omega
          have hjeq : j = sh ⟨j.val - 2, by omega⟩ := Fin.ext (by simp [sh]; omega)
          rw [hjeq, hN_0s, zero_mul]
    have hN_mv1 : ∀ v : Fin (2 * (m' + 1)) → F2, (N *ᵥ v) i1 = v i0 := by
      intro v
      simp only [Matrix.mulVec, dotProduct]
      rw [sum_fin_support1 i0 (fun j => N i1 j * v j)]
      · rw [hN_10, one_mul]
      · intro j hj0
        by_cases hj1 : j = i1
        · subst hj1; rw [hN_11, zero_mul]
        · have hj2 : 2 ≤ j.val := by
            have h0 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
            have h1 : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
            omega
          have hjeq : j = sh ⟨j.val - 2, by omega⟩ := Fin.ext (by simp [sh]; omega)
          rw [hjeq, hN_1s, zero_mul]
    have hN_mvs : ∀ (v : Fin (2 * (m' + 1)) → F2) (i : Fin (2 * m')),
        (N *ᵥ v) (sh i) = (A' *ᵥ (fun k => v (sh k))) i := by
      intro v i
      simp only [Matrix.mulVec, dotProduct]
      let eSplit : Fin 2 ⊕ Fin (2 * m') ≃ Fin (2 * (m' + 1)) :=
        { toFun := Sum.elim (fun b => ⟨b.val, by omega⟩) sh
          invFun := fun j => if hj : j.val < 2 then Sum.inl ⟨j.val, hj⟩ else Sum.inr ⟨j.val - 2, by omega⟩
          left_inv := fun s => by
            cases s with
            | inl b => simp [b.isLt]
            | inr k =>
              have hnot : ¬ (k.val + 2 < 2) := by omega
              simp [sh, hnot]
          right_inv := fun j => by
            by_cases hj : j.val < 2
            · simp [hj]
            · simp only [hj, ↓reduceDIte, Sum.elim_inr]
              apply Fin.ext; simp [sh]; omega }
      rw [← Equiv.sum_comp eSplit, Fintype.sum_sum_type, Fin.sum_univ_two]
      have h0 : eSplit (Sum.inl 0) = i0 := rfl
      have h1 : eSplit (Sum.inl 1) = i1 := rfl
      rw [h0, h1, hN_s0, hN_s1, zero_mul, zero_mul, add_zero, zero_add]
      refine Finset.sum_congr rfl fun k _ => ?_
      change N (sh i) (sh k) * v (sh k) = A' i k * v (sh k)
      rw [hN_ss]
    let eR : ((Fin 2 → F2) × LinearMap.range A'.mulVecLin) ≃ₗ[F2] LinearMap.range N.mulVecLin :=
      { toFun := fun p =>
          ⟨fun idx => if h0 : idx.val = 0 then p.1 0 else if h1 : idx.val = 1 then p.1 1 else p.2.val ⟨idx.val - 2, by omega⟩, by
            rcases p.2.property with ⟨u, hu⟩
            let v : Fin (2 * (m' + 1)) → F2 := fun idx =>
              if h0 : idx.val = 0 then p.1 1 else if h1 : idx.val = 1 then p.1 0 else u ⟨idx.val - 2, by omega⟩
            refine ⟨v, ?_⟩
            funext idx
            rw [Matrix.mulVecLin_apply]
            by_cases h0 : idx.val = 0
            · have hid : idx = i0 := Fin.ext h0
              subst hid; simp only [h0, ↓reduceDIte, hN_mv0]; rfl
            · by_cases h1 : idx.val = 1
              · have hid : idx = i1 := Fin.ext h1
                subst hid; simp only [h0, h1, ↓reduceDIte, hN_mv1]; rfl
              · have hid : idx = sh ⟨idx.val - 2, by omega⟩ := Fin.ext (by simp [sh]; omega)
                simp only [h0, h1, ↓reduceDIte]
                conv_lhs => rw [hid, hN_mvs]
                have hvu : (fun k : Fin (2 * m') => v (sh k)) = u := by
                  funext k; simp [v, sh]
                rw [hvu]
                have := congrFun hu ⟨idx.val - 2, by omega⟩
                simpa [Matrix.mulVecLin_apply] using this⟩
        invFun := fun w =>
          (fun b => if b = 0 then w.val i0 else w.val i1,
           ⟨fun k => w.val (sh k), by
             rcases w.property with ⟨v, hv⟩
             refine ⟨fun k => v (sh k), ?_⟩
             funext k
             rw [Matrix.mulVecLin_apply, ← hN_mvs v k]
             exact congrFun hv (sh k)⟩)
        left_inv := fun ⟨p, ⟨y, hy⟩⟩ => by
          apply Prod.ext
          · funext b; fin_cases b <;> simp [i0, i1]
          · apply Subtype.ext; funext k; simp [sh]
        right_inv := fun ⟨w, hw⟩ => by
          apply Subtype.ext; funext idx
          by_cases h0 : idx.val = 0
          · have hid : idx = i0 := Fin.ext h0; subst hid; simp [i0]
          · by_cases h1 : idx.val = 1
            · have hid : idx = i1 := Fin.ext h1; subst hid; simp [i1]
            · have hid : idx = sh ⟨idx.val - 2, by omega⟩ := Fin.ext (by simp [sh]; omega)
              simp only [h0, h1, ↓reduceDIte]; rw [← hid]
        map_add' := fun p q => by
          apply Subtype.ext; funext idx
          simp only [Submodule.coe_add, Pi.add_apply, Prod.fst_add, Prod.snd_add]
          by_cases h0 : idx.val = 0
          · simp only [h0, ↓reduceDIte]
          · by_cases h1 : idx.val = 1
            · simp only [h0, h1, ↓reduceDIte, show ¬ ((1 : ℕ) = 0) by omega]
            · simp only [h0, h1, ↓reduceDIte]
        map_smul' := fun c p => by
          apply Subtype.ext; funext idx
          simp only [SetLike.val_smul, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
          by_cases h0 : idx.val = 0
          · simp only [h0, ↓reduceDIte]
          · by_cases h1 : idx.val = 1
            · simp only [h0, h1, ↓reduceDIte, show ¬ ((1 : ℕ) = 0) by omega]
            · simp only [h0, h1, ↓reduceDIte] }
    have hM1_rank : M1.rank = 2 + A'.rank := by
      have h1 := eR.finrank_eq
      rw [Module.finrank_prod, Module.finrank_fin_fun] at h1
      change 2 + A'.rank = N.rank at h1
      omega
    have hdeq : d = Fin.cons (d 0) d' := by
      funext i; refine Fin.cases (by simp) (fun j => by simp [d', Fin.tail]) i
    have hham_split : hamDist d z0 = (if d 0 + a0 ≠ 0 then 1 else 0) + hamDist d' z' := by
      simp only [hamDist, hamWt]
      let eF : Fin 1 ⊕ Fin m' ≃ Fin (m' + 1) :=
        { toFun := Sum.elim (fun _ => 0) Fin.succ
          invFun := fun i => if h : i = 0 then Sum.inl 0 else Sum.inr (i.pred h)
          left_inv := fun s => by
            cases s with
            | inl b => fin_cases b; simp
            | inr k => simp [Fin.succ_ne_zero]
          right_inv := fun i => by
            by_cases h : i = 0
            · subst h; simp
            · simp [h] }
      have hcard : (Finset.univ.filter (fun t : Fin (m' + 1) => (d + z0) t ≠ 0)).card =
          (Finset.univ.filter (fun s : Fin 1 ⊕ Fin m' => (d + z0) (eF s) ≠ 0)).card := by
        apply Finset.card_bij (fun t _ => eF.symm t)
        · intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
          rwa [Equiv.apply_symm_apply]
        · intro t1 _ t2 _ h; exact eF.symm.injective h
        · intro s hs
          refine ⟨eF s, ?_, eF.symm_apply_apply s⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          exact hs
      rw [hcard]
      have hsum : (Finset.univ.filter (fun s : Fin 1 ⊕ Fin m' => (d + z0) (eF s) ≠ 0)).card =
          ∑ s : Fin 1 ⊕ Fin m', if (d + z0) (eF s) ≠ 0 then 1 else 0 := by
        rw [Finset.card_filter]
      rw [hsum, Fintype.sum_sum_type, Fin.sum_univ_one]
      have h0 : (d + z0) (eF (Sum.inl 0)) = d 0 + a0 := by simp [eF, z0]
      rw [h0]
      congr 1
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [eF, Equiv.coe_fn_mk, Sum.elim_inr, Pi.add_apply, z0, Fin.cons_succ, d', Fin.tail]
      by_cases hc : d t.succ + z' t = 0 <;> simp [hc]
    rcases zmod2_cases (d 0 + a0) with hd0 | hd1
    · have hda : d 0 = a0 := z2_eq_of_add_eq_zero hd0
      have hM1_sum : M1 = (K + diagPair d) + diagPair (Fin.cons (1 : F2) (0 : Fin m' → F2)) := by
        dsimp only [M1]
        rw [add_assoc, ← diagPair_add]
        congr 2
        funext i
        refine Fin.cases ?_ ?_ i
        · simp only [Pi.add_apply, Fin.cons_zero, hda]
        · intro j; simp only [Pi.add_apply, Fin.cons_succ, Pi.zero_apply, add_zero, d', Fin.tail]
      let J2m : Matrix (Fin (2 * (m' + 1))) (Fin (2 * (m' + 1))) F2 :=
        diagPair (Fin.cons (1 : F2) (0 : Fin m' → F2))
      have hJ2_rank : J2m.rank ≤ 2 := by
        let proj2 : LinearMap.range J2m.mulVecLin →ₗ[F2] (Fin 2 → F2) :=
          { toFun := fun w b => w.val ⟨b.val, by omega⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        have hinj2 : Function.Injective proj2 := by
          intro w1 w2 h
          apply Subtype.ext; funext idx
          by_cases h0 : idx.val = 0
          · have hid : idx = ⟨0, by omega⟩ := Fin.ext h0
            rw [hid]; exact congrFun h 0
          · by_cases h1 : idx.val = 1
            · have hid : idx = ⟨1, by omega⟩ := Fin.ext h1
              rw [hid]; exact congrFun h 1
            · have hzero : ∀ w ∈ LinearMap.range J2m.mulVecLin, w idx = 0 := by
                rintro _ ⟨v, rfl⟩
                rw [Matrix.mulVecLin_apply]
                simp only [Matrix.mulVec, dotProduct]
                apply Finset.sum_eq_zero
                intro j _
                have hJ0 : J2m idx j = 0 := by
                  simp only [J2m, diagPair, Matrix.of_apply]
                  split_ifs with hcond
                  · have hpos : 0 < idx.val / 2 := by omega
                    have hne0 : (⟨idx.val / 2, by omega⟩ : Fin (m' + 1)) ≠ 0 := by
                      intro heq; have := congrArg Fin.val heq; simp at this; omega
                    have hsucc : (⟨idx.val / 2, by omega⟩ : Fin (m' + 1)) =
                        (⟨idx.val / 2 - 1, by omega⟩ : Fin m').succ := by
                      apply Fin.ext; simp; omega
                    rw [hsucc, Fin.cons_succ]; rfl
                  · rfl
                rw [hJ0, zero_mul]
              rw [hzero w1.val w1.property, hzero w2.val w2.property]
        have hle := LinearMap.finrank_le_finrank_of_injective hinj2
        simpa [Matrix.rank] using hle
      have hrle := rank_add_le' (K + diagPair d) J2m
      rw [← hM1_sum, hM1_rank] at hrle
      dsimp only [A'] at hrle
      have hih := hz' d'
      rw [hham_split, hd0]
      simp only [ne_eq, not_true_eq_false, ↓reduceIte, zero_add]
      omega
    · have hda : d 0 = a0 + 1 := by
        have : d 0 + a0 + a0 = 1 + a0 := congrArg (· + a0) hd1
        rw [add_assoc, z2_add_self, add_zero, add_comm (1 : F2) a0] at this
        exact this
      have hMeq : K + diagPair d = M1 := by
        dsimp only [M1]; congr 2; rw [hdeq, hda]
      rw [hMeq, hM1_rank, hham_split, hd1]
      have hne1 : (1 : F2) ≠ 0 := by decide
      rw [ite_eq_left_iff.mpr (fun h => absurd hne1 h)]
      dsimp only [A']
      have hih := hz' d'
      omega

lemma gauss_sum_sq_bound {m2 : ℕ} (M : Matrix (Fin (2 * m2)) (Fin (2 * m2)) F2)
    (hMd : ∀ i, M i i = 0) (hMs : ∀ i j, M i j = M j i)
    (E : (Fin (2 * m2) → F2) → F2)
    (hE : ∀ q h, E (q + h) + E q = E h + E 0 + dotProduct (M *ᵥ h) q) :
    (∑ q : Fin (2 * m2) → F2, signBool (decide (E q = 1))).natAbs ≤ 2 ^ (2 * m2 - M.rank / 2) := by
  set S : ℤ := ∑ q : Fin (2 * m2) → F2, signBool (decide (E q = 1))
  have hS2 : S * S = (2 : ℤ) ^ (2 * m2) *
      ∑ h : Fin (2 * m2) → F2,
        if M *ᵥ h = 0 then signBool (decide (E h + E 0 = 1)) else 0 := by
    calc S * S
        = ∑ q : Fin (2 * m2) → F2, ∑ q' : Fin (2 * m2) → F2,
            signBool (decide (E q = 1)) * signBool (decide (E q' = 1)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun q _ => by rw [Finset.mul_sum]
      _ = ∑ q : Fin (2 * m2) → F2, ∑ h : Fin (2 * m2) → F2,
            signBool (decide (E q = 1)) * signBool (decide (E (q + h) = 1)) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          exact (Equiv.sum_comp (Equiv.addLeft q) (fun q' => signBool (decide (E q = 1)) * signBool (decide (E q' = 1)))).symm
      _ = ∑ h : Fin (2 * m2) → F2, ∑ q : Fin (2 * m2) → F2,
            signBool (decide (E h + E 0 = 1)) * signBool (decide (dotProduct (M *ᵥ h) q = 1)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun q _ => ?_
          rw [← signBool_xor, ← zmod2_add_decide, add_comm (E q), hE q h, zmod2_add_decide, signBool_xor]
      _ = ∑ h : Fin (2 * m2) → F2,
            signBool (decide (E h + E 0 = 1)) *
              (∑ q : Fin (2 * m2) → F2, signBool (decide (dotProduct (M *ᵥ h) q = 1))) := by
          refine Finset.sum_congr rfl fun h _ => by rw [← Finset.mul_sum]
      _ = ∑ h : Fin (2 * m2) → F2,
            (2 : ℤ) ^ (2 * m2) * (if M *ᵥ h = 0 then signBool (decide (E h + E 0 = 1)) else 0) := by
          refine Finset.sum_congr rfl fun h _ => ?_
          by_cases h0 : M *ᵥ h = 0
          · simp only [h0, ↓reduceIte, zero_dotProduct]
            have hcard : (∑ _q : Fin (2 * m2) → F2, signBool (decide ((0 : F2) = 1))) = (2 : ℤ) ^ (2 * m2) := by
              change (∑ _q : Fin (2 * m2) → F2, (1 : ℤ)) = (2 : ℤ) ^ (2 * m2)
              simp [ZMod.card]
            rw [hcard, mul_comm]
          · simp only [h0, ↓reduceIte, sum_sign_dot_univ _ h0, mul_zero]
      _ = (2 : ℤ) ^ (2 * m2) *
            ∑ h : Fin (2 * m2) → F2,
              if M *ᵥ h = 0 then signBool (decide (E h + E 0 = 1)) else 0 := by
          rw [Finset.mul_sum]
  have hker_le : (∑ h : Fin (2 * m2) → F2,
      if M *ᵥ h = 0 then signBool (decide (E h + E 0 = 1)) else 0).natAbs ≤
      2 ^ (2 * m2 - M.rank) := by
    have htri := Finset.abs_sum_le_sum_abs
      (fun h : Fin (2 * m2) → F2 => if M *ᵥ h = 0 then signBool (decide (E h + E 0 = 1)) else 0)
      Finset.univ
    have habs : ∀ h : Fin (2 * m2) → F2,
        |(if M *ᵥ h = 0 then signBool (decide (E h + E 0 = 1)) else 0)| =
          if M *ᵥ h = 0 then (1 : ℤ) else 0 := by
      intro h; split_ifs
      · exact signBool_abs_one _
      · simp
    simp_rw [habs] at htri
    have hnat : (∑ h : Fin (2 * m2) → F2,
        if M *ᵥ h = 0 then signBool (decide (E h + E 0 = 1)) else 0).natAbs ≤
        ∑ h : Fin (2 * m2) → F2, if M *ᵥ h = 0 then (1 : ℕ) else 0 := by
      have hcast : ((∑ h : Fin (2 * m2) → F2,
          if M *ᵥ h = 0 then signBool (decide (E h + E 0 = 1)) else 0).natAbs : ℤ) ≤
          ∑ h : Fin (2 * m2) → F2, if M *ᵥ h = 0 then (1 : ℤ) else 0 := by
        simpa [Int.natCast_natAbs] using htri
      exact_mod_cast hcast
    have hcard_ker : (∑ h : Fin (2 * m2) → F2, if M *ᵥ h = 0 then (1 : ℕ) else 0) =
        2 ^ (2 * m2 - M.rank) := by
      rw [← Finset.card_filter]
      have h1 : (Finset.univ.filter (fun h : Fin (2 * m2) → F2 => M *ᵥ h = 0)).card =
          Fintype.card (LinearMap.ker M.mulVecLin) := by
        rw [← Fintype.card_subtype]
        exact Fintype.card_congr
          { toFun := fun x => ⟨x.1, x.2⟩
            invFun := fun x => ⟨x.1, x.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      rw [h1, card_submodule_zmod2]
      have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
      rw [Module.finrank_fin_fun] at hrn
      have hdim : Module.finrank F2 (LinearMap.ker M.mulVecLin) = 2 * m2 - M.rank := by
        unfold Matrix.rank; omega
      rw [hdim]
    exact le_trans hnat (le_of_eq hcard_ker)
  have hsq_le : S.natAbs * S.natAbs ≤ 2 ^ (2 * m2) * 2 ^ (2 * m2 - M.rank) := by
    have hmul : S.natAbs * S.natAbs = (S * S).natAbs := (Int.natAbs_mul S S).symm
    rw [hmul, hS2, Int.natAbs_mul]
    have h2 : ((2 : ℤ) ^ (2 * m2)).natAbs = 2 ^ (2 * m2) := by
      rw [show (2 : ℤ) ^ (2 * m2) = ((2 ^ (2 * m2) : ℕ) : ℤ) by push_cast; rfl, Int.natAbs_natCast]
    rw [h2]
    exact Nat.mul_le_mul_left _ hker_le
  have hev : Even M.rank := even_rank M hMd hMs
  have hrk_le : M.rank ≤ 2 * m2 := by
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fin_fun] at this
    unfold Matrix.rank; omega
  have hrk_eq : 2 * (M.rank / 2) = M.rank := by
    rcases hev with ⟨t, ht⟩; omega
  have hpow_eq : 2 ^ (2 * m2) * 2 ^ (2 * m2 - M.rank) =
      2 ^ (2 * m2 - M.rank / 2) * 2 ^ (2 * m2 - M.rank / 2) := by
    rw [← pow_add, ← pow_add]
    congr 1; omega
  rw [hpow_eq] at hsq_le
  by_contra hgt
  push Not at hgt
  have := Nat.mul_lt_mul'' hgt hgt
  omega

lemma walsh_coset_bound {j0 m2 : ℕ} (c : (Fin j0 → F2) →ₗ[F2] (Fin m2 → F2)) (z0 : Fin m2 → F2) :
    ∑ w : Fin j0 → F2, 2 ^ (m2 - hamWt (c w + z0)) ≤ ∑ w : Fin j0 → F2, 2 ^ (m2 - hamWt (c w)) := by
  have hident : ∀ v : Fin m2 → F2,
      (2 : ℤ) ^ m2 * (2 : ℤ) ^ (m2 - hamWt v) =
        ∑ S ∈ (Finset.univ : Finset (Fin m2)).powerset,
          (3 : ℤ) ^ (m2 - S.card) * signBool (decide ((∑ t ∈ S, v t) = 1)) := by
    intro v
    have hprod : ∏ t : Fin m2, ((3 : ℤ) + signBool (decide (v t = 1))) =
        (2 : ℤ) ^ m2 * (2 : ℤ) ^ (m2 - hamWt v) := by
      have hterm : ∀ t : Fin m2, (3 : ℤ) + signBool (decide (v t = 1)) =
          (2 : ℤ) * (if v t = 0 then (2 : ℤ) else 1) := by
        intro t
        rcases zmod2_cases (v t) with h | h <;> rw [h] <;> decide
      simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
      congr 1
      have hcomp : (Finset.univ.filter (fun t : Fin m2 => v t = 0)).card +
          (Finset.univ.filter (fun t : Fin m2 => v t ≠ 0)).card = m2 := by
        have h1 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin m2)) (fun t => v t = 0) (fun _ => (1 : ℕ))
        simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at h1
        exact h1
      dsimp only [hamWt]; omega
    rw [← hprod]
    have hcomm : (∏ t : Fin m2, ((3 : ℤ) + signBool (decide (v t = 1)))) =
        ∏ t : Fin m2, (signBool (decide (v t = 1)) + (3 : ℤ)) :=
      Finset.prod_congr rfl fun t _ => add_comm _ _
    rw [hcomm, Finset.prod_add (fun t : Fin m2 => signBool (decide (v t = 1))) (fun _ => (3 : ℤ)) Finset.univ]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [Finset.prod_const, ← signBool_sum_f2 S v, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, mul_comm]
  have hsum_ident : ∀ z : Fin m2 → F2,
      (2 : ℤ) ^ m2 * (∑ w : Fin j0 → F2, (2 : ℤ) ^ (m2 - hamWt (c w + z))) =
        ∑ S ∈ (Finset.univ : Finset (Fin m2)).powerset,
          (3 : ℤ) ^ (m2 - S.card) * signBool (decide ((∑ t ∈ S, z t) = 1)) *
            (∑ w : Fin j0 → F2, signBool (decide ((∑ t ∈ S, c w t) = 1))) := by
    intro z
    rw [Finset.mul_sum]
    simp_rw [hident]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hsum_add : (∑ t ∈ S, (c w + z) t) = (∑ t ∈ S, z t) + (∑ t ∈ S, c w t) := by
      simp only [Pi.add_apply, Finset.sum_add_distrib, add_comm]
    rw [hsum_add, zmod2_add_decide, signBool_xor]
    ring
  have hnonneg : ∀ S : Finset (Fin m2),
      0 ≤ ∑ w : Fin j0 → F2, signBool (decide ((∑ t ∈ S, c w t) = 1)) := by
    intro S
    let ℓ : (Fin j0 → F2) →ₗ[F2] F2 :=
      { toFun := fun w => ∑ t ∈ S, c w t
        map_add' := fun x y => by simp only [map_add, Pi.add_apply, Finset.sum_add_distrib]
        map_smul' := fun a x => by
          simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum] }
    obtain ⟨rS, hrS⟩ := linear_coord_dot ℓ
    have hrew : (∑ w : Fin j0 → F2, signBool (decide ((∑ t ∈ S, c w t) = 1))) =
        ∑ w : Fin j0 → F2, signBool (decide (dotProduct rS w = 1)) :=
      Finset.sum_congr rfl fun w _ => by rw [← hrS w]; rfl
    rw [hrew]
    by_cases hr0 : rS = 0
    · subst hr0
      simp only [zero_dotProduct]
      have hpos : ∀ _w : Fin j0 → F2, (0 : ℤ) ≤ signBool (decide ((0 : F2) = 1)) := fun _ => by decide
      exact Finset.sum_nonneg fun w _ => hpos w
    · rw [sum_sign_dot_univ rS hr0]
  have hle_z : (2 : ℤ) ^ m2 * (∑ w : Fin j0 → F2, (2 : ℤ) ^ (m2 - hamWt (c w + z0))) ≤
      (2 : ℤ) ^ m2 * (∑ w : Fin j0 → F2, (2 : ℤ) ^ (m2 - hamWt (c w + 0))) := by
    rw [hsum_ident z0, hsum_ident 0]
    refine Finset.sum_le_sum fun S _ => ?_
    have h0 : signBool (decide ((∑ t ∈ S, (0 : Fin m2 → F2) t) = 1)) = 1 := by simp [signBool]
    rw [h0, mul_one]
    have hcoeff : 0 ≤ (3 : ℤ) ^ (m2 - S.card) := by positivity
    have hnonnegS := hnonneg S
    have hsb := signBool_le_one (decide ((∑ t ∈ S, z0 t) = 1))
    have h1 : signBool (decide ((∑ t ∈ S, z0 t) = 1)) * (∑ w : Fin j0 → F2, signBool (decide ((∑ t ∈ S, c w t) = 1))) ≤
        1 * (∑ w : Fin j0 → F2, signBool (decide ((∑ t ∈ S, c w t) = 1))) :=
      mul_le_mul_of_nonneg_right hsb hnonnegS
    rw [one_mul] at h1
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 hcoeff
  have h2pos : (0 : ℤ) < (2 : ℤ) ^ m2 := by positivity
  have hle_sum : (∑ w : Fin j0 → F2, (2 : ℤ) ^ (m2 - hamWt (c w + z0))) ≤
      ∑ w : Fin j0 → F2, (2 : ℤ) ^ (m2 - hamWt (c w)) := by
    have hle' := le_of_mul_le_mul_left hle_z h2pos
    simpa only [add_zero] using hle'
  exact_mod_cast hle_sum

lemma pair_section (m1 : ℕ) : ∀ (r_rem : ℕ) (U : Submodule F2 (Fin (2 * m1) → F2)),
    2 * m1 - Module.finrank F2 U ≤ r_rem →
    ∃ (J0 : Finset (Fin m1))
      (τ : (({t : Fin m1 // t ∉ J0} × Bool) → F2) →ₗ[F2] (Fin (2 * m1) → F2)),
      J0.card ≤ r_rem ∧
      (∀ q, τ q ∈ U) ∧
      (∀ (t : Fin m1) (ht : t ∉ J0) (b : Bool) (q), τ q (pairIdx t b) = q (⟨t, ht⟩, b)) ∧
      (∀ t ∈ J0, (∀ q, τ q (pairIdx t false) = 0) ∨ (∀ q, τ q (pairIdx t true) = 0)) := by
  intro r_rem
  induction r_rem with
  | zero =>
    intro U hcod
    have hle : Module.finrank F2 U ≤ 2 * m1 := by
      have := Submodule.finrank_le U
      simpa using this
    have htop : U = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)
    let τ : (({t : Fin m1 // t ∉ (∅ : Finset (Fin m1))} × Bool) → F2) →ₗ[F2] (Fin (2 * m1) → F2) :=
      { toFun := fun q idx =>
          q (⟨((pairEquiv m1).symm idx).1, Finset.notMem_empty _⟩, ((pairEquiv m1).symm idx).2)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine ⟨∅, τ, by simp, fun _ => by rw [htop]; trivial, ?_, fun _ ht => absurd ht (Finset.notMem_empty _)⟩
    intro t ht b q
    dsimp only [τ, LinearMap.coe_mk, AddHom.coe_mk]
    have hinv : (pairEquiv m1).symm (pairIdx t b) = (t, b) := (pairEquiv m1).symm_apply_apply (t, b)
    rw [hinv]
  | succ r_rem ih =>
    intro U hcod
    by_cases hsmall : 2 * m1 - Module.finrank F2 U ≤ r_rem
    · rcases ih U hsmall with ⟨J0, τ, hcard, hmem, hcoord, hkill⟩
      exact ⟨J0, τ, by omega, hmem, hcoord, hkill⟩
    · have hleU : Module.finrank F2 U ≤ 2 * m1 := by
        have := Submodule.finrank_le U
        simpa using this
      obtain ⟨C_U, hcompl⟩ := Submodule.exists_isCompl U
      have hdimC : Module.finrank F2 C_U + Module.finrank F2 U = 2 * m1 := by
        have := Submodule.finrank_add_eq_of_isCompl hcompl.symm
        simpa using this
      have hposC : 0 < Module.finrank F2 C_U := by omega
      let bC := Module.finBasis F2 C_U
      let i0 : Fin (Module.finrank F2 C_U) := ⟨0, hposC⟩
      let πC : (Fin (2 * m1) → F2) →ₗ[F2] C_U := Submodule.linearProjOfIsCompl C_U U hcompl.symm
      let v0 : Fin (2 * m1) → F2 := (bC i0).val
      let φ : (Fin (2 * m1) → F2) →ₗ[F2] F2 := (bC.coord i0).comp πC
      have hφU : ∀ x ∈ U, φ x = 0 := by
        intro x hx
        have hpi : πC x = 0 := Submodule.linearProjOfIsCompl_apply_right hcompl.symm ⟨x, hx⟩
        simp [φ, hpi]
      have hφv0 : φ v0 = 1 := by
        have hpi : πC v0 = bC i0 := Submodule.linearProjOfIsCompl_apply_left hcompl.symm (bC i0)
        simp [φ, hpi]
      have hv0_ne : v0 ≠ 0 := by
        intro h0; rw [h0, map_zero] at hφv0; exact zero_ne_one hφv0
      let U' : Submodule F2 (Fin (2 * m1) → F2) := U ⊔ Submodule.span F2 {v0}
      have hU_eq : ∀ x, x ∈ U' → φ x = 0 → x ∈ U := by
        intro x hx hφx
        rcases Submodule.mem_sup.mp hx with ⟨u, hu, y, hy, rfl⟩
        rcases Submodule.mem_span_singleton.mp hy with ⟨c, rfl⟩
        rw [map_add, hφU u hu, zero_add, map_smul, hφv0, smul_eq_mul, mul_one] at hφx
        rw [hφx, zero_smul, add_zero]
        exact hu
      have hinf_bot : U ⊓ Submodule.span F2 {v0} = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rcases Submodule.mem_span_singleton.mp hx.2 with ⟨c, rfl⟩
        have h0 := hφU (c • v0) hx.1
        rw [map_smul, hφv0, smul_eq_mul, mul_one] at h0
        simp [h0]
      have hdimU' : Module.finrank F2 U' = Module.finrank F2 U + 1 := by
        have hsup := Submodule.finrank_sup_add_finrank_inf_eq U (Submodule.span F2 {v0})
        rw [hinf_bot, finrank_bot, add_zero, finrank_span_singleton hv0_ne] at hsup
        exact hsup
      rcases ih U' (by omega) with ⟨J', τ', hcard', hmem', hcoord', hkill'⟩
      let ψ : (({t : Fin m1 // t ∉ J'} × Bool) → F2) →ₗ[F2] F2 := φ.comp τ'
      by_cases hψ0 : ∀ p, ψ p = 0
      · refine ⟨J', τ', by omega, fun q => hU_eq (τ' q) (hmem' q) (hψ0 q), hcoord', hkill'⟩
      · have hex : ∃ idx : {t : Fin m1 // t ∉ J'} × Bool, ψ (Pi.single idx 1) = 1 := by
          by_contra hnot
          push Not at hnot
          apply hψ0
          intro p
          have hp : p = ∑ idx : {t : Fin m1 // t ∉ J'} × Bool, p idx • Pi.single idx (1 : F2) := by
            funext y; simp [Finset.sum_apply, Pi.single_apply]
          rw [hp, map_sum]
          refine Finset.sum_eq_zero fun idx _ => ?_
          rw [map_smul, smul_eq_mul]
          have hz : ψ (Pi.single idx 1) = 0 := by
            rcases zmod2_cases (ψ (Pi.single idx 1)) with h0 | h1
            · exact h0
            · exact absurd h1 (hnot idx)
          rw [hz, mul_zero]
        rcases hex with ⟨⟨t0, b0⟩, hψ1⟩
        let J0 : Finset (Fin m1) := insert t0.val J'
        have hJ0_card : J0.card ≤ r_rem + 1 := by
          have hle := Finset.card_insert_le t0.val J'
          dsimp only [J0]; omega
        let ext0 : (({t : Fin m1 // t ∉ J0} × Bool) → F2) →ₗ[F2] (({t : Fin m1 // t ∉ J'} × Bool) → F2) :=
          { toFun := fun q idx =>
              if h : idx.1.val = t0.val then 0
              else q (⟨idx.1.val, fun hmem => by
                rcases Finset.mem_insert.mp hmem with heq | hmem'
                · exact h heq
                · exact idx.1.property hmem'⟩, idx.2)
            map_add' := fun q1 q2 => by
              funext idx; simp only [Pi.add_apply]; split_ifs <;> simp
            map_smul' := fun c q => by
              funext idx; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
        let lift : (({t : Fin m1 // t ∉ J0} × Bool) → F2) →ₗ[F2] (({t : Fin m1 // t ∉ J'} × Bool) → F2) :=
          { toFun := fun q => ext0 q + ψ (ext0 q) • Pi.single (t0, b0) (1 : F2)
            map_add' := fun q1 q2 => by
              simp only [map_add, add_smul]; abel
            map_smul' := fun c q => by
              funext idx; simp [map_smul, smul_eq_mul]; ring }
        let τ : (({t : Fin m1 // t ∉ J0} × Bool) → F2) →ₗ[F2] (Fin (2 * m1) → F2) := τ'.comp lift
        refine ⟨J0, τ, hJ0_card, ?_, ?_, ?_⟩
        · intro q
          apply hU_eq (τ q) (hmem' (lift q))
          change ψ (lift q) = 0
          simp only [lift, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_smul, hψ1, smul_eq_mul, mul_one]
          exact z2_add_self _
        · intro t ht b q
          have hnt0 : t ≠ t0.val := fun h => ht (Finset.mem_insert.mpr (Or.inl h))
          have hntJ' : t ∉ J' := fun h => ht (Finset.mem_insert.mpr (Or.inr h))
          change τ' (lift q) (pairIdx t b) = _
          rw [hcoord' t hntJ' b (lift q)]
          have hne_idx : ((⟨t, hntJ'⟩ : {t : Fin m1 // t ∉ J'}), b) ≠ (t0, b0) := by
            intro heq
            exact hnt0 (congrArg (fun p => p.1.val) heq)
          simp [lift, ext0, hnt0, Pi.single_apply, hne_idx]
        · intro t ht
          rcases Finset.mem_insert.mp ht with rfl | ht'
          · cases b0
            · right
              intro q
              change τ' (lift q) (pairIdx t0.val true) = 0
              rw [hcoord' t0.val t0.property true (lift q)]
              have hne : (t0, true) ≠ (t0, false) := fun h => by cases congrArg Prod.snd h
              simp [lift, ext0, Pi.single_apply, hne]
            · left
              intro q
              change τ' (lift q) (pairIdx t0.val false) = 0
              rw [hcoord' t0.val t0.property false (lift q)]
              have hne : (t0, false) ≠ (t0, true) := fun h => Bool.false_ne_true (congrArg Prod.snd h)
              simp [lift, ext0, Pi.single_apply, hne]
          · rcases hkill' t ht' with hF | hT
            · exact Or.inl fun q => hF (lift q)
            · exact Or.inr fun q => hT (lift q)

def appendAffinesLoop (N m : ℕ) (cs : Fin m → Fin N → F2) (bs : Fin m → F2) :
    (k : ℕ) → k ≤ m → List Gate → (Fin m → ℕ) → List Gate × (Fin m → ℕ)
  | 0, _, gs, ws => (gs, ws)
  | k + 1, hk, gs, ws =>
    let res1 := appendAffinesLoop N m cs bs k (by omega) gs ws
    let resA := appendAffine N res1.1 (cs ⟨k, hk⟩) (bs ⟨k, hk⟩)
    (resA.1, fun l => if l.val = k then resA.2 else res1.2 l)

lemma appendAffinesLoop_spec (N m : ℕ) (cs : Fin m → Fin N → F2) (bs : Fin m → F2) :
    ∀ (k : ℕ) (hk : k ≤ m) (gs : List Gate) (ws : Fin m → ℕ),
      legalGates N gs →
      let res := appendAffinesLoop N m cs bs k hk gs ws
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates N res.1 ∧
        costGates res.1 = costGates gs ∧
        (∀ l : Fin m, l.val < k → res.2 l < N + res.1.length) ∧
        (∀ l : Fin m, l.val < k → ∀ u : Fin N → F2,
          (wiresOf res.1 (bitsOf N u)).getD (res.2 l) false = decide (dotProduct (cs l) u + bs l = 1)) := by
  intro k
  induction k with
  | zero =>
    intro hk gs ws hleg
    exact ⟨[], by simp [appendAffinesLoop], hleg, rfl, fun _ hl => by omega, fun _ hl => by omega⟩
  | succ k ih =>
    intro hk gs ws hleg
    rcases ih (by omega) gs ws hleg with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set res1 := appendAffinesLoop N m cs bs k (by omega) gs ws
    rcases appendAffine_spec N res1.1 (cs ⟨k, hk⟩) (bs ⟨k, hk⟩) h1leg with
      ⟨extA, hAeq, hAleg, hAcost, hAlt, hAsem⟩
    set resA := appendAffine N res1.1 (cs ⟨k, hk⟩) (bs ⟨k, hk⟩)
    refine ⟨ext1 ++ extA, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [appendAffinesLoop]
      change resA.1 = _
      rw [hAeq, h1eq, List.append_assoc]
    · exact hAleg
    · change costGates resA.1 = costGates gs; rw [hAcost, h1cost]
    · intro l hl
      simp only [appendAffinesLoop]
      change (if l.val = k then resA.2 else res1.2 l) < N + resA.1.length
      by_cases hlk : l.val = k
      · simp only [hlk, ↓reduceIte]; exact hAlt
      · simp only [hlk, ↓reduceIte]
        have := h1lt l (by omega)
        rw [hAeq, List.length_append]; omega
    · intro l hl u
      simp only [appendAffinesLoop]
      change (wiresOf resA.1 (bitsOf N u)).getD (if l.val = k then resA.2 else res1.2 l) false = _
      by_cases hlk : l.val = k
      · simp only [hlk, ↓reduceIte]
        have hleq : l = ⟨k, hk⟩ := Fin.ext hlk
        rw [hleq]; exact hAsem u
      · simp only [hlk, ↓reduceIte]
        rw [hAeq, wiresOf_append_getD_lt res1.1 extA (bitsOf N u) (by rw [bitsOf_len]; exact h1lt l (by omega))]
        exact h1sem l (by omega) u

def remapWire (n offset : ℕ) (yWire : Fin n → ℕ) (idx : ℕ) : ℕ :=
  if h : idx < n then yWire ⟨idx, h⟩ else offset + (idx - n)

def remapGate (n offset : ℕ) (yWire : Fin n → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapWire n offset yWire)⟩

lemma remap_gates_spec (N n : ℕ) (gs_pre gs : List Gate) (yWire : Fin n → ℕ)
    (hpre : legalGates N gs_pre) (hcost_pre : costGates gs_pre = 0)
    (hyw : ∀ l : Fin n, yWire l < N + gs_pre.length) (hgs : legalGates n gs) :
    let offset := N + gs_pre.length
    let gs_comb := gs_pre ++ gs.map (remapGate n offset yWire)
    legalGates N gs_comb ∧
    costGates gs_comb = costGates gs ∧
    (∀ idx < n + gs.length, remapWire n offset yWire idx < N + gs_comb.length) ∧
    (∀ (x : List Bool) (y : Fin n → F2), x.length = N →
      (∀ l : Fin n, (wiresOf gs_pre x).getD (yWire l) false = decide (y l = 1)) →
      ∀ idx < n + gs.length,
        (wiresOf gs_comb x).getD (remapWire n offset yWire idx) false =
          (wiresOf gs (bitsOf n y)).getD idx false) := by
  intro offset
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨by simpa using hpre, by simp only [List.map_nil, List.append_nil, hcost_pre]; simp [costGates], ?_, ?_⟩
    · intro idx hidx
      simp only [List.length_nil, Nat.add_zero] at hidx
      simp only [remapWire, hidx, ↓reduceDIte, List.map_nil, List.append_nil]
      exact hyw ⟨idx, hidx⟩
    · intro x y _ hy idx hidx
      simp only [List.length_nil, Nat.add_zero] at hidx
      simp only [remapWire, hidx, ↓reduceDIte, List.map_nil, List.append_nil]
      rw [hy ⟨idx, hidx⟩]
      change decide (y ⟨idx, hidx⟩ = 1) = (bitsOf n y).getD (⟨idx, hidx⟩ : Fin n).val false
      rw [bitsOf_getD]
  | append_singleton gs g ih =>
    have hpre_g := legalGates_prefix hgs
    rcases ih hpre_g.1 with ⟨hleg1, hcost1, hlt1, hsem1⟩
    set gs_c1 := gs_pre ++ gs.map (remapGate n offset yWire)
    set g' := remapGate n offset yWire g
    have hcomb_eq : gs_pre ++ (gs ++ [g]).map (remapGate n offset yWire) = gs_c1 ++ [g'] := by
      simp [gs_c1, g', List.append_assoc]
    have hback' : ∀ i ∈ g'.inputs, i < N + gs_c1.length := by
      intro i hi
      rcases List.mem_map.mp hi with ⟨idx, hidx, rfl⟩
      exact hlt1 idx (hpre_g.2.1 idx hidx)
    have hshape' : g'.inputs.length ≤ 2 ∧
        (g'.op = .and ∨ g'.op = .or ∨ g'.op = .mod 2 ∨ (g'.op = .not ∧ g'.inputs.length = 1)) := by
      simpa [g', remapGate] using hpre_g.2.2
    have hleg2 : legalGates N (gs_c1 ++ [g']) := legalGates_snoc hleg1 hback' hshape'
    have hcost2 : costGates (gs_c1 ++ [g']) = costGates (gs ++ [g]) := by
      rw [costGates_append gs_c1 [g'], costGates_append gs [g], hcost1]
      congr 1
      simp [costGates, g', remapGate]
    rw [hcomb_eq]
    refine ⟨hleg2, hcost2, ?_, ?_⟩
    · intro idx hidx
      simp only [List.length_append, List.length_singleton] at hidx ⊢
      by_cases hlt : idx < n + gs.length
      · have := hlt1 idx hlt; omega
      · have heq : idx = n + gs.length := by omega
        subst heq
        have hnot : ¬ (n + gs.length < n) := by omega
        simp only [remapWire, hnot, ↓reduceDIte, Nat.add_sub_cancel_left, gs_c1, offset,
          List.length_append, List.length_map]
        omega
    · intro x y hx hy idx hidx
      simp only [List.length_append, List.length_singleton] at hidx
      by_cases hlt : idx < n + gs.length
      · rw [wiresOf_append_getD_lt gs_c1 [g'] x (by rw [hx]; exact hlt1 idx hlt),
            wiresOf_append_getD_lt gs [g] (bitsOf n y) (by rw [bitsOf_len]; exact hlt)]
        exact hsem1 x y hx hy idx hlt
      · have heq : idx = n + gs.length := by omega
        subst heq
        have hnot : ¬ (n + gs.length < n) := by omega
        have hrew : remapWire n offset yWire (n + gs.length) = N + gs_c1.length := by
          simp only [remapWire, hnot, ↓reduceDIte, Nat.add_sub_cancel_left, gs_c1, offset,
            List.length_append, List.length_map]; omega
        rw [hrew, wiresOf_snoc_last_eq gs_c1 g' x hx, wiresOf_snoc_last_eq gs g (bitsOf n y) (bitsOf_len n y)]
        dsimp only [g', remapGate]
        congr 1
        rw [List.map_map]
        refine List.map_congr_left fun i hi => ?_
        exact hsem1 x y hx hy i (hpre_g.2.1 i hi)

def appendProdWiresLoop (N s : ℕ) (cA cB : Fin s → Fin N → F2) :
    (m : ℕ) → m ≤ s → List Gate → (Fin s → ℕ) → List Gate × (Fin s → ℕ)
  | 0, _, gs, ws => (gs, ws)
  | m + 1, hm, gs, ws =>
    let res1 := appendProdWiresLoop N s cA cB m (by omega) gs ws
    let resA := appendAffine N res1.1 (cA ⟨m, hm⟩) 0
    let resB := appendAffine N resA.1 (cB ⟨m, hm⟩) 0
    let gs4 := resB.1 ++ [⟨.and, [resA.2, resB.2]⟩]
    let wP := N + resB.1.length
    (gs4, fun i => if i.val = m then wP else res1.2 i)

lemma appendProdWiresLoop_spec (N s : ℕ) (cA cB : Fin s → Fin N → F2) :
    ∀ (m : ℕ) (hm : m ≤ s) (gs : List Gate) (ws : Fin s → ℕ),
      legalGates N gs →
      let res := appendProdWiresLoop N s cA cB m hm gs ws
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates N res.1 ∧
        costGates res.1 = costGates gs + m ∧
        (∀ i : Fin s, i.val < m → res.2 i < N + res.1.length) ∧
        (∀ i : Fin s, i.val < m → ∀ u : Fin N → F2,
          (wiresOf res.1 (bitsOf N u)).getD (res.2 i) false =
            decide (dotProduct (cA i) u * dotProduct (cB i) u = 1)) := by
  intro m
  induction m with
  | zero =>
    intro hm gs ws hleg
    exact ⟨[], by simp [appendProdWiresLoop], hleg, by simp [appendProdWiresLoop],
      fun _ hi => by omega, fun _ hi => by omega⟩
  | succ m ih =>
    intro hm gs ws hleg
    rcases ih (by omega) gs ws hleg with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set res1 := appendProdWiresLoop N s cA cB m (by omega) gs ws
    rcases appendAffine_spec N res1.1 (cA ⟨m, hm⟩) 0 h1leg with ⟨extA, hAeq, hAleg, hAcost, hAlt, hAsem⟩
    set resA := appendAffine N res1.1 (cA ⟨m, hm⟩) 0
    rcases appendAffine_spec N resA.1 (cB ⟨m, hm⟩) 0 hAleg with ⟨extB, hBeq, hBleg, hBcost, hBlt, hBsem⟩
    set resB := appendAffine N resA.1 (cB ⟨m, hm⟩) 0
    have hwA_ltB : resA.2 < N + resB.1.length := by rw [hBeq, List.length_append]; omega
    set gs4 := resB.1 ++ [⟨.and, [resA.2, resB.2]⟩]
    have h4leg : legalGates N gs4 :=
      legalGates_snoc hBleg (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hwA_ltB; exact hBlt)
        ⟨by simp, Or.inl rfl⟩
    have h4cost : costGates gs4 = costGates gs + (m + 1) := by
      rw [costGates_snoc_one resB.1 _ ⟨Or.inl rfl, rfl⟩, hBcost, hAcost, h1cost]; omega
    refine ⟨ext1 ++ extA ++ extB ++ [⟨.and, [resA.2, resB.2]⟩], ?_, h4leg, h4cost, ?_, ?_⟩
    · simp only [appendProdWiresLoop]
      change gs4 = _
      simp only [gs4, hBeq, hAeq, h1eq, List.append_assoc]
    · intro i hi
      simp only [appendProdWiresLoop]
      change (if i.val = m then N + resB.1.length else res1.2 i) < N + gs4.length
      by_cases him : i.val = m
      · simp only [him, ↓reduceIte, gs4, List.length_append, List.length_singleton]; omega
      · simp only [him, ↓reduceIte]
        have := h1lt i (by omega)
        simp only [gs4, hBeq, hAeq, List.length_append, List.length_singleton]; omega
    · intro i hi u
      simp only [appendProdWiresLoop]
      change (wiresOf gs4 (bitsOf N u)).getD (if i.val = m then N + resB.1.length else res1.2 i) false = _
      by_cases him : i.val = m
      · simp only [him, ↓reduceIte]
        have hieq : i = ⟨m, hm⟩ := Fin.ext him
        rw [hieq]
        change (wiresOf (resB.1 ++ [⟨.and, [resA.2, resB.2]⟩]) (bitsOf N u)).getD (N + resB.1.length) false = _
        rw [wiresOf_snoc_last_eq resB.1 _ (bitsOf N u) (bitsOf_len N u)]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        rw [hBeq, wiresOf_append_getD_lt resA.1 extB (bitsOf N u) (by rw [bitsOf_len]; exact hAlt),
            ← hBeq, hAsem u, hBsem u, add_zero, add_zero, zmod2_mul_decide]
      · simp only [him, ↓reduceIte]
        have hgs4 : gs4 = res1.1 ++ (extA ++ extB ++ [⟨.and, [resA.2, resB.2]⟩]) := by
          simp only [gs4, hBeq, hAeq, List.append_assoc]
        rw [hgs4, wiresOf_append_getD_lt res1.1 _ (bitsOf N u) (by rw [bitsOf_len]; exact h1lt i (by omega))]
        exact h1sem i (by omega) u

def appendQuadPriorsLoop (N j p_cnt : ℕ) (pWires : Fin p_cnt → ℕ)
    (cW cLin : Fin j → Fin N → F2) (bLin : Fin j → F2) (coeffP : Fin j → Fin p_cnt → F2) :
    (m : ℕ) → m ≤ j → List Gate → ℕ → List Gate × ℕ
  | 0, _, gs, acc => (gs, acc)
  | m + 1, hm, gs, acc =>
    let res1 := appendQuadPriorsLoop N j p_cnt pWires cW cLin bLin coeffP m (by omega) gs acc
    let resW := appendAffine N res1.1 (cW ⟨m, hm⟩) 0
    let resL := appendAffine N resW.1 (cLin ⟨m, hm⟩) (bLin ⟨m, hm⟩)
    let resR := appendXorWiresLoop N p_cnt (coeffP ⟨m, hm⟩) pWires p_cnt (le_refl p_cnt) resL.1 resL.2
    let gs4 := resR.1 ++ [⟨.and, [resW.2, resR.2]⟩]
    let wP := N + resR.1.length
    (gs4 ++ [⟨.mod 2, [res1.2, wP]⟩, ⟨.not, [N + gs4.length]⟩], N + gs4.length + 1)

lemma appendQuadPriorsLoop_spec (N j p_cnt : ℕ) (pWires : Fin p_cnt → ℕ)
    (cW cLin : Fin j → Fin N → F2) (bLin : Fin j → F2) (coeffP : Fin j → Fin p_cnt → F2) :
    ∀ (m : ℕ) (hm : m ≤ j) (gs : List Gate) (acc : ℕ),
      legalGates N gs → acc < N + gs.length → (∀ idx : Fin p_cnt, pWires idx < N + gs.length) →
      let res := appendQuadPriorsLoop N j p_cnt pWires cW cLin bLin coeffP m hm gs acc
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates N res.1 ∧
        costGates res.1 = costGates gs + m ∧
        res.2 < N + res.1.length ∧
        ∀ u : Fin N → F2,
          (wiresOf res.1 (bitsOf N u)).getD res.2 false =
            Bool.xor ((wiresOf gs (bitsOf N u)).getD acc false)
              (decide ((∑ a ∈ Finset.univ.filter (fun a : Fin j => a.val < m),
                dotProduct (cW a) u *
                  ((dotProduct (cLin a) u + bLin a) +
                    ∑ idx : Fin p_cnt, coeffP a idx *
                      (if (wiresOf gs (bitsOf N u)).getD (pWires idx) false then (1 : F2) else 0))) = 1)) := by
  intro m
  induction m with
  | zero =>
    intro hm gs acc hleg hacc _
    refine ⟨[], by simp [appendQuadPriorsLoop], hleg, by simp [appendQuadPriorsLoop], hacc, fun u => ?_⟩
    have hemp : Finset.univ.filter (fun a : Fin j => a.val < 0) = ∅ := by ext a; simp
    simp [appendQuadPriorsLoop, hemp]
  | succ m ih =>
    intro hm gs acc hleg hacc hpW
    rcases ih (by omega) gs acc hleg hacc hpW with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set res1 := appendQuadPriorsLoop N j p_cnt pWires cW cLin bLin coeffP m (by omega) gs acc
    rcases appendAffine_spec N res1.1 (cW ⟨m, hm⟩) 0 h1leg with ⟨extW, hWeq, hWleg, hWcost, hWlt, hWsem⟩
    set resW := appendAffine N res1.1 (cW ⟨m, hm⟩) 0
    rcases appendAffine_spec N resW.1 (cLin ⟨m, hm⟩) (bLin ⟨m, hm⟩) hWleg with ⟨extL, hLeq, hLleg, hLcost, hLlt, hLsem⟩
    set resL := appendAffine N resW.1 (cLin ⟨m, hm⟩) (bLin ⟨m, hm⟩)
    have hpW_L : ∀ idx : Fin p_cnt, pWires idx < N + resL.1.length := by
      intro idx; have := hpW idx
      rw [hLeq, hWeq, h1eq, List.length_append, List.length_append, List.length_append]; omega
    rcases appendXorWiresLoop_spec N p_cnt (coeffP ⟨m, hm⟩) pWires p_cnt (le_refl p_cnt) resL.1 resL.2 hLleg hLlt hpW_L with
      ⟨extR, hReq, hRleg, hRcost, hRlt, hRsem⟩
    set resR := appendXorWiresLoop N p_cnt (coeffP ⟨m, hm⟩) pWires p_cnt (le_refl p_cnt) resL.1 resL.2
    have hwW_ltR : resW.2 < N + resR.1.length := by
      rw [hReq, hLeq, List.length_append, List.length_append]; omega
    set gs4 := resR.1 ++ [⟨.and, [resW.2, resR.2]⟩]
    set wP := N + resR.1.length
    have h4leg : legalGates N gs4 :=
      legalGates_snoc hRleg (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hwW_ltR; exact hRlt)
        ⟨by simp, Or.inl rfl⟩
    have h4cost : costGates gs4 = costGates gs + (m + 1) := by
      rw [costGates_snoc_one resR.1 _ ⟨Or.inl rfl, rfl⟩, hRcost, hLcost, hWcost, h1cost]; omega
    have hacc1_lt4 : res1.2 < N + gs4.length := by
      simp only [gs4, hReq, hLeq, hWeq, List.length_append, List.length_singleton]; omega
    have hwP_lt4 : wP < N + gs4.length := by simp [gs4, wP]
    have hstep := addXor_step N gs4 res1.2 wP h4leg hacc1_lt4 hwP_lt4
    refine ⟨ext1 ++ extW ++ extL ++ extR ++ [⟨.and, [resW.2, resR.2]⟩, ⟨.mod 2, [res1.2, wP]⟩, ⟨.not, [N + gs4.length]⟩],
      ?_, hstep.1, ?_, ?_, ?_⟩
    · simp only [appendQuadPriorsLoop]
      change gs4 ++ [⟨.mod 2, [res1.2, wP]⟩, ⟨.not, [N + gs4.length]⟩] = _
      simp only [gs4, hReq, hLeq, hWeq, h1eq, List.append_assoc, List.cons_append, List.nil_append]
    · change costGates (gs4 ++ [⟨.mod 2, [res1.2, wP]⟩, ⟨.not, [N + gs4.length]⟩]) = _
      rw [hstep.2.1, h4cost]
    · change N + gs4.length + 1 < N + (gs4 ++ ([⟨.mod 2, [res1.2, wP]⟩, ⟨.not, [N + gs4.length]⟩] : List Gate)).length
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro u
      change (wiresOf (gs4 ++ [⟨.mod 2, [res1.2, wP]⟩, ⟨.not, [N + gs4.length]⟩]) (bitsOf N u)).getD (N + gs4.length + 1) false = _
      rw [hstep.2.2.2 (bitsOf N u) (bitsOf_len N u)]
      have hacc1_eq : (wiresOf gs4 (bitsOf N u)).getD res1.2 false = (wiresOf res1.1 (bitsOf N u)).getD res1.2 false := by
        have hgs4_eq : gs4 = res1.1 ++ (extW ++ extL ++ extR ++ [⟨.and, [resW.2, resR.2]⟩]) := by
          simp only [gs4, hReq, hLeq, hWeq, List.append_assoc]
        rw [hgs4_eq, wiresOf_append_getD_lt res1.1 _ (bitsOf N u) (by rw [bitsOf_len]; exact h1lt)]
      have hwP_eq : (wiresOf gs4 (bitsOf N u)).getD wP false =
          decide (dotProduct (cW ⟨m, hm⟩) u *
            ((dotProduct (cLin ⟨m, hm⟩) u + bLin ⟨m, hm⟩) +
              ∑ idx : Fin p_cnt, coeffP ⟨m, hm⟩ idx *
                (if (wiresOf gs (bitsOf N u)).getD (pWires idx) false then (1 : F2) else 0)) = 1) := by
        change (wiresOf (resR.1 ++ [⟨.and, [resW.2, resR.2]⟩]) (bitsOf N u)).getD (N + resR.1.length) false = _
        rw [wiresOf_snoc_last_eq resR.1 _ (bitsOf N u) (bitsOf_len N u)]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        have hwW_val : (wiresOf resR.1 (bitsOf N u)).getD resW.2 false = decide (dotProduct (cW ⟨m, hm⟩) u = 1) := by
          have hreq' : resR.1 = resW.1 ++ (extL ++ extR) := by simp only [hReq, hLeq, List.append_assoc]
          rw [hreq', wiresOf_append_getD_lt resW.1 _ (bitsOf N u) (by rw [bitsOf_len]; exact hWlt),
              hWsem u, add_zero]
        have hwR_val : (wiresOf resR.1 (bitsOf N u)).getD resR.2 false =
            decide ((dotProduct (cLin ⟨m, hm⟩) u + bLin ⟨m, hm⟩) +
              ∑ idx : Fin p_cnt, coeffP ⟨m, hm⟩ idx *
                (if (wiresOf gs (bitsOf N u)).getD (pWires idx) false then (1 : F2) else 0) = 1) := by
          rw [hRsem u, hLsem u]
          have huniv : Finset.univ.filter (fun idx : Fin p_cnt => idx.val < p_cnt) = Finset.univ := by
            ext idx; simp
          rw [huniv, ← zmod2_add_decide]
          apply congrArg (fun z : F2 => decide (z = 1))
          congr 1
          refine Finset.sum_congr rfl fun idx _ => ?_
          have hL_eq : resL.1 = gs ++ (ext1 ++ extW ++ extL) := by simp only [hLeq, hWeq, h1eq, List.append_assoc]
          rw [hL_eq, wiresOf_append_getD_lt gs _ (bitsOf N u) (by rw [bitsOf_len]; exact hpW idx)]
        rw [hwW_val, hwR_val, zmod2_mul_decide]
      rw [hacc1_eq, h1sem u, hwP_eq]
      have hsplit : (Finset.univ.filter (fun a : Fin j => a.val < m + 1)) =
          insert ⟨m, hm⟩ (Finset.univ.filter (fun a : Fin j => a.val < m)) := by
        ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      have hnotmem : (⟨m, hm⟩ : Fin j) ∉ Finset.univ.filter (fun a : Fin j => a.val < m) := by simp
      rw [hsplit, Finset.sum_insert hnotmem, zmod2_add_decide]
      cases (wiresOf gs (bitsOf N u)).getD acc false <;>
        cases decide (dotProduct (cW ⟨m, hm⟩) u *
          ((dotProduct (cLin ⟨m, hm⟩) u + bLin ⟨m, hm⟩) +
            ∑ idx : Fin p_cnt, coeffP ⟨m, hm⟩ idx *
              (if (wiresOf gs (bitsOf N u)).getD (pWires idx) false then (1 : F2) else 0)) = 1) <;>
        cases decide ((∑ a ∈ Finset.univ.filter (fun a : Fin j => a.val < m),
          dotProduct (cW a) u *
            ((dotProduct (cLin a) u + bLin a) +
              ∑ idx : Fin p_cnt, coeffP a idx *
                (if (wiresOf gs (bitsOf N u)).getD (pWires idx) false then (1 : F2) else 0))) = 1) <;> decide

lemma sum_prod_pairs {m : ℕ} (f : Fin m → F2 × F2 → ℤ) :
    (∑ uv : (Fin m → F2) × (Fin m → F2), ∏ i : Fin m, f i (uv.1 i, uv.2 i)) =
      ∏ i : Fin m, ∑ p : F2 × F2, f i p := by
  induction m with
  | zero =>
    have h1 : (∑ uv : (Fin 0 → F2) × (Fin 0 → F2), (1 : ℤ)) = 1 := by simp
    simpa using h1
  | succ m ih =>
    let eP : (F2 × F2) × ((Fin m → F2) × (Fin m → F2)) ≃ (Fin (m + 1) → F2) × (Fin (m + 1) → F2) :=
      { toFun := fun q => (Fin.cons q.1.1 q.2.1, Fin.cons q.1.2 q.2.2)
        invFun := fun uv => ((uv.1 0, uv.2 0), (Fin.tail uv.1, Fin.tail uv.2))
        left_inv := fun ⟨⟨a, b⟩, ⟨u, v⟩⟩ => by simp
        right_inv := fun ⟨u, v⟩ => by ext i <;> simp }
    rw [← Equiv.sum_comp eP, Fintype.sum_prod_type, Fin.prod_univ_succ]
    have hsplit : ∀ p : F2 × F2,
        (∑ uv : (Fin m → F2) × (Fin m → F2),
          ∏ i : Fin (m + 1), f i ((eP (p, uv)).1 i, (eP (p, uv)).2 i)) =
        f 0 p * ∑ uv : (Fin m → F2) × (Fin m → F2), ∏ i : Fin m, f i.succ (uv.1 i, uv.2 i) := by
      intro p
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun uv _ => ?_
      rw [Fin.prod_univ_succ]
      simp [eP]
    simp_rw [hsplit, ← Finset.sum_mul, ih]

lemma dual_equiv (k m r : ℕ)
    (e : (Fin (k + 2 * m + r) → F2) ≃ₗ[F2]
      (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2)))) :
    ∃ eDual : (Fin (k + 2 * m + r) → F2) ≃ₗ[F2]
      (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2))),
      (∀ x y, dotProduct x y =
        dotProduct (eDual x).1 (e y).1 + dotProduct (eDual x).2.1 (e y).2.1 +
        dotProduct (eDual x).2.2.1 (e y).2.2.1 + dotProduct (eDual x).2.2.2 (e y).2.2.2) ∧
      (∀ x s0, dotProduct (eDual x).1 s0 = dotProduct (e.symm (s0, (0, (0, 0)))) x) ∧
      (∀ x i, (eDual x).2.1 i = dotProduct (e.symm (0, (Pi.single i 1, (0, 0)))) x) ∧
      (∀ x i, (eDual x).2.2.1 i = dotProduct (e.symm (0, (0, (Pi.single i 1, 0)))) x) ∧
      (∀ x t, (eDual x).2.2.2 t = dotProduct (e.symm (0, (0, (0, Pi.single t 1)))) x) := by
  let V := Fin (k + 2 * m + r) → F2
  let P := (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2)))
  let φ : V →ₗ[F2] P :=
    { toFun := fun x =>
        (fun a => dotProduct x (e.symm (Pi.single a 1, (0, (0, 0)))),
         (fun i => dotProduct x (e.symm (0, (Pi.single i 1, (0, 0)))),
          (fun i => dotProduct x (e.symm (0, (0, (Pi.single i 1, 0)))),
           fun t => dotProduct x (e.symm (0, (0, (0, Pi.single t 1)))))))
      map_add' := fun x y => by
        apply Prod.ext
        · funext a; exact add_dotProduct x y _
        · apply Prod.ext
          · funext i; exact add_dotProduct x y _
          · apply Prod.ext
            · funext i; exact add_dotProduct x y _
            · funext t; exact add_dotProduct x y _
      map_smul' := fun c x => by
        rw [Prod.smul_mk, Prod.smul_mk, Prod.smul_mk]
        apply Prod.ext
        · funext a; exact smul_dotProduct c x _
        · apply Prod.ext
          · funext i; exact smul_dotProduct c x _
          · apply Prod.ext
            · funext i; exact smul_dotProduct c x _
            · funext t; exact smul_dotProduct c x _ }
  have hdot : ∀ x y : V, dotProduct x y =
      dotProduct (φ x).1 (e y).1 + dotProduct (φ x).2.1 (e y).2.1 +
      dotProduct (φ x).2.2.1 (e y).2.2.1 + dotProduct (φ x).2.2.2 (e y).2.2.2 := by
    intro x y
    have hy_decomp : e y =
        (∑ a : Fin k, (e y).1 a • (Pi.single a (1 : F2), (0, (0, 0)))) +
        (∑ i : Fin m, (e y).2.1 i • (0, (Pi.single i (1 : F2), (0, 0)))) +
        (∑ i : Fin m, (e y).2.2.1 i • (0, (0, (Pi.single i (1 : F2), 0)))) +
        (∑ t : Fin r, (e y).2.2.2 t • (0, (0, (0, Pi.single t (1 : F2))))) := by
      apply Prod.ext
      · simp [Prod.fst_sum, ← vec_eq_sum_single]
      · apply Prod.ext
        · simp [Prod.snd_sum, Prod.fst_sum, ← vec_eq_sum_single]
        · apply Prod.ext
          · simp [Prod.snd_sum, Prod.fst_sum, ← vec_eq_sum_single]
          · simp [Prod.snd_sum, ← vec_eq_sum_single]
    have hy_eq : y = e.symm (e y) := (e.symm_apply_apply y).symm
    conv_lhs => rw [hy_eq, hy_decomp, map_add, map_add, map_add, map_sum, map_sum, map_sum, map_sum,
      dotProduct_add, dotProduct_add, dotProduct_add, dotProduct_sum, dotProduct_sum, dotProduct_sum, dotProduct_sum]
    simp only [map_smul, dotProduct_smul, smul_eq_mul, φ, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1; congr 1; congr 1
    · exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).mpr fun x hx => ?_
    funext l
    have h0 := hdot x (Pi.single l 1)
    rw [hx] at h0
    simp only [Prod.fst_zero, Prod.snd_zero, zero_dotProduct, add_zero, dotProduct_single, mul_one] at h0
    exact h0
  have hbij : Function.Bijective φ := by
    refine ⟨hinj, ?_⟩
    have hcard : Fintype.card V = Fintype.card P := Fintype.card_congr e.toEquiv
    exact Finite.injective_iff_surjective_of_equiv e.toEquiv |>.mp hinj
  let eDual : V ≃ₗ[F2] P := LinearEquiv.ofBijective φ hbij
  refine ⟨eDual, hdot, ?_, ?_, ?_, ?_⟩
  · intro x s0
    have hs : s0 = ∑ a : Fin k, s0 a • Pi.single a (1 : F2) := vec_eq_sum_single s0
    have heq : (s0, ((0 : Fin m → F2), ((0 : Fin m → F2), (0 : Fin r → F2)))) =
        ∑ a : Fin k, s0 a • (Pi.single a (1 : F2), (0, (0, 0))) := by
      apply Prod.ext
      · simp [Prod.fst_sum, ← hs]
      · simp [Prod.snd_sum]
    rw [heq, map_sum, sum_dotProduct]
    simp only [eDual, LinearEquiv.ofBijective_apply, φ, LinearMap.coe_mk, AddHom.coe_mk,
      map_smul, smul_dotProduct, smul_eq_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [dotProduct_comm, mul_comm]
  · intro x i; simp [eDual, φ, dotProduct_comm]
  · intro x i; simp [eDual, φ, dotProduct_comm]
  · intro x t; simp [eDual, φ, dotProduct_comm]

lemma conjunct3_proof (k m r : ℕ)
    (e : (Fin (k + 2 * m + r) → F2) ≃ₗ[F2]
      (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2))))
    (A : Fin m → (Fin k → F2)) (h : (Fin k → F2) → F2)
    (j : ℕ) (B : (Fin j → F2) →ₗ[F2] (Fin k → F2)) (J : Finset (Fin m))
    (hB : Function.Injective B) (hq : isQuad (fun u => h (B u))) :
    let n := k + 2 * m + r
    let base := 2 * m + r
    let g := fun y : Fin n → F2 =>
      h (e y).1 + ∑ i : Fin m, dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
    let weight := fun (s : Fin k → F2) =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ dotProduct (A i) s ≠ 0)).card
    let mass := ∑ u : Fin j → F2, 2 ^ (m - weight (B u))
    ∃ C : Circuit, legalGates (2 * n) C.gates ∧ costGates C.gates ≤ base + j + J.card ∧
      2 ^ (k + m) * (∑ x : Fin n → F2, ∑ y : Fin n → F2,
        if C.eval (bitsOf n x ++ bitsOf n y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs = 2 ^ (2 * n) * mass := by
  intro n base g weight mass
  rcases hq with ⟨z0, l_q, M_q, hq_eq⟩
  rcases linear_map_left_inv B hB with ⟨π, hπB⟩
  rcases dual_equiv k m r e with ⟨eDual, hdot_dual, hdualS, hdualU, hdualV, hdualZ⟩
  let wMap : (Fin n → F2) →ₗ[F2] (Fin j → F2) :=
    π.comp ((LinearMap.fst F2 _ _).comp e.toLinearMap)
  have hcoordW : ∀ a : Fin j, ∃ rW : Fin n → F2, ∀ y, wMap y a = dotProduct rW y :=
    fun a => linear_coord_dot ((LinearMap.proj a).comp wMap)
  choose rW hrW using hcoordW
  have hcoordU : ∀ i : Fin m, ∃ rU : Fin n → F2, ∀ y, (e y).2.1 i = dotProduct rU y :=
    fun i => linear_coord_dot ((LinearMap.proj i).comp ((LinearMap.fst F2 _ _).comp ((LinearMap.snd F2 _ _).comp e.toLinearMap)))
  choose rU hrU using hcoordU
  have hcoordV : ∀ i : Fin m, ∃ rV : Fin n → F2, ∀ y, (e y).2.2.1 i = dotProduct rV y :=
    fun i => linear_coord_dot ((LinearMap.proj i).comp ((LinearMap.fst F2 _ _).comp ((LinearMap.snd F2 _ _).comp ((LinearMap.snd F2 _ _).comp e.toLinearMap))))
  choose rV hrV using hcoordV
  have hcoordZ : ∀ t : Fin r, ∃ rZ : Fin n → F2, ∀ y, (e y).2.2.2 t = dotProduct rZ y :=
    fun t => linear_coord_dot ((LinearMap.proj t).comp ((LinearMap.snd F2 _ _).comp ((LinearMap.snd F2 _ _).comp ((LinearMap.snd F2 _ _).comp e.toLinearMap))))
  choose rZ hrZ using hcoordZ
  let eJ : Fin J.card ≃ J := (Fintype.equivFinOfCardEq (Fintype.card_coe J)).symm
  let cPA : Fin J.card → Fin (2 * n) → F2 := fun idx => concatVec 0 (rU (eJ idx).val)
  let cPB : Fin J.card → Fin (2 * n) → F2 := fun idx => concatVec 0 (rV (eJ idx).val)
  have hnil : legalGates (2 * n) [] := ⟨fun idx hidx => by simp at hidx, fun h hh => by simp at hh⟩
  rcases appendProdWiresLoop_spec (2 * n) J.card cPA cPB J.card (le_refl _) [] (fun _ => 0) hnil with
    ⟨_, _, h1leg, h1cost, h1lt, h1sem⟩
  set resP := appendProdWiresLoop (2 * n) J.card cPA cPB J.card (le_refl _) [] (fun _ => 0)
  have h2spec := appendConst_spec (2 * n) resP.1 z0 h1leg
  set g0 := if z0 = 1 then Gate.mk .and [] else Gate.mk .or []
  set gs2 := resP.1 ++ [g0]
  set acc0 := 2 * n + resP.1.length
  have hpW_lt2 : ∀ idx : Fin J.card, resP.2 idx < 2 * n + gs2.length := by
    intro idx; have := h1lt idx idx.isLt
    simp only [gs2, List.length_append, List.length_singleton]; omega
  let cW : Fin j → Fin (2 * n) → F2 := fun a => concatVec 0 (rW a)
  let cLin : Fin j → Fin (2 * n) → F2 := fun a =>
    concatVec (e.symm (B (Pi.single a 1), (0, (0, 0)))) (∑ b : Fin j, M_q a b • rW b)
  let coeffP : Fin j → Fin J.card → F2 := fun a idx => dotProduct (A (eJ idx).val) (B (Pi.single a 1))
  rcases appendQuadPriorsLoop_spec (2 * n) j J.card resP.2 cW cLin l_q coeffP j (le_refl _) gs2 acc0
      h2spec.1 h2spec.2.2.1 hpW_lt2 with
    ⟨ext3, h3eq, h3leg, h3cost, h3lt, h3sem⟩
  set res3 := appendQuadPriorsLoop (2 * n) j J.card resP.2 cW cLin l_q coeffP j (le_refl _) gs2 acc0
  let cBA : Fin base → Fin (2 * n) → F2 := fun idx =>
    if h1 : idx.val < m then concatVec (e.symm (0, (Pi.single ⟨idx.val, h1⟩ 1, (0, 0)))) 0
    else if h2 : idx.val < 2 * m then concatVec (e.symm (0, (0, (Pi.single ⟨idx.val - m, by omega⟩ 1, 0)))) 0
    else concatVec (e.symm (0, (0, (0, Pi.single ⟨idx.val - 2 * m, by omega⟩ 1)))) 0
  let cBB : Fin base → Fin (2 * n) → F2 := fun idx =>
    if h1 : idx.val < m then concatVec 0 (rU ⟨idx.val, h1⟩)
    else if h2 : idx.val < 2 * m then concatVec 0 (rV ⟨idx.val - m, by omega⟩)
    else concatVec 0 (rZ ⟨idx.val - 2 * m, by omega⟩)
  rcases appendSumProdsLoop_spec (2 * n) base cBA cBB (fun _ => 0) (fun _ => 0) base (le_refl _) res3.1 res3.2 h3leg h3lt with
    ⟨_, _, h4leg, h4cost, _, h4sem⟩
  set res4 := appendSumProdsLoop (2 * n) base cBA cBB (fun _ => 0) (fun _ => 0) base (le_refl _) res3.1 res3.2
  refine ⟨⟨res4.1, res4.2⟩, h4leg, ?_, ?_⟩
  · have hc0 : costGates ([] : List Gate) = 0 := by simp [costGates]
    dsimp only [res4, res3, gs2, resP] at h4cost h3cost h2spec h1cost ⊢
    have hc2 := h2spec.2.1
    omega
  · have hCe : ∀ x y : Fin n → F2,
        (Circuit.mk res4.1 res4.2).eval (bitsOf n x ++ bitsOf n y) =
          decide (h (B (π (e y).1)) + dotProduct (eDual x).1 (B (π (e y).1)) +
            (∑ i ∈ J, dotProduct (A i) (B (π (e y).1)) * (e y).2.1 i * (e y).2.2.1 i) +
            dotProduct (eDual x).2.1 (e y).2.1 +
            dotProduct (eDual x).2.2.1 (e y).2.2.1 +
            dotProduct (eDual x).2.2.2 (e y).2.2.2 = 1) := by
      intro x y
      change (wiresOf res4.1 (bitsOf n x ++ bitsOf n y)).getD res4.2 false = _
      rw [bitsOf_concatVec, h4sem (concatVec x y), h3sem (concatVec x y)]
      have hacc0 : (wiresOf gs2 (bitsOf (2 * n) (concatVec x y))).getD acc0 false = decide (z0 = 1) :=
        h2spec.2.2.2 (bitsOf (2 * n) (concatVec x y)) (bitsOf_len (2 * n) _)
      rw [hacc0]
      have hunivB : Finset.univ.filter (fun idx : Fin base => idx.val < base) = Finset.univ := by ext idx; simp
      have hunivJ : Finset.univ.filter (fun a : Fin j => a.val < j) = Finset.univ := by ext a; simp
      rw [hunivB, hunivJ, ← zmod2_add_decide, ← zmod2_add_decide]
      congr 1
      have hpVal : ∀ idx : Fin J.card,
          (if (wiresOf gs2 (bitsOf (2 * n) (concatVec x y))).getD (resP.2 idx) false then (1 : F2) else 0) =
            (e y).2.1 (eJ idx).val * (e y).2.2.1 (eJ idx).val := by
        intro idx
        rw [wiresOf_append_getD_lt resP.1 [g0] (bitsOf (2 * n) (concatVec x y))
              (by rw [bitsOf_len]; exact h1lt idx idx.isLt),
            h1sem idx idx.isLt (concatVec x y), zmod2_decide_bool]
        simp only [cPA, cPB, dotProduct_concatVec, zero_dotProduct, zero_add, ← hrU, ← hrV]
      have hsumBase : (∑ idx : Fin base, (dotProduct (cBA idx) (concatVec x y) + 0) * (dotProduct (cBB idx) (concatVec x y) + 0)) =
          dotProduct (eDual x).2.1 (e y).2.1 + dotProduct (eDual x).2.2.1 (e y).2.2.1 +
          dotProduct (eDual x).2.2.2 (e y).2.2.2 := by
        let eBase : Fin m ⊕ (Fin m ⊕ Fin r) ≃ Fin base :=
          { toFun := Sum.elim (fun i => ⟨i.val, by omega⟩)
              (Sum.elim (fun i => ⟨m + i.val, by omega⟩) (fun t => ⟨2 * m + t.val, by omega⟩))
            invFun := fun idx =>
              if h1 : idx.val < m then Sum.inl ⟨idx.val, h1⟩
              else if h2 : idx.val < 2 * m then Sum.inr (Sum.inl ⟨idx.val - m, by omega⟩)
              else Sum.inr (Sum.inr ⟨idx.val - 2 * m, by omega⟩)
            left_inv := fun s => by
              rcases s with i | (i | t)
              · simp [i.isLt]
              · have h1 : ¬ (m + i.val < m) := by omega
                have h2 : m + i.val < 2 * m := by omega
                simp [h1, h2]
              · have h1 : ¬ (2 * m + t.val < m) := by omega
                have h2 : ¬ (2 * m + t.val < 2 * m) := by omega
                simp [h1, h2]
            right_inv := fun idx => by
              by_cases h1 : idx.val < m
              · simp [h1]
              · by_cases h2 : idx.val < 2 * m
                · simp only [h1, h2, ↓reduceDIte, Sum.elim_inr, Sum.elim_inl]
                  apply Fin.ext; dsimp; omega
                · simp only [h1, h2, ↓reduceDIte, Sum.elim_inr]
                  apply Fin.ext; dsimp; omega }
        rw [← Equiv.sum_comp eBase, Fintype.sum_sum_type, Fintype.sum_sum_type]
        simp only [add_zero]
        have s1 : (∑ i : Fin m, dotProduct (cBA (eBase (Sum.inl i))) (concatVec x y) *
            dotProduct (cBB (eBase (Sum.inl i))) (concatVec x y)) =
            ∑ i : Fin m, (eDual x).2.1 i * (e y).2.1 i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [eBase, Equiv.coe_fn_mk, Sum.elim_inl, cBA, cBB, i.isLt, ↓reduceDIte,
            dotProduct_concatVec, zero_dotProduct, add_zero, zero_add, ← hdualU x i, ← hrU i y]
        have s2 : (∑ i : Fin m, dotProduct (cBA (eBase (Sum.inr (Sum.inl i)))) (concatVec x y) *
            dotProduct (cBB (eBase (Sum.inr (Sum.inl i)))) (concatVec x y)) =
            ∑ i : Fin m, (eDual x).2.2.1 i * (e y).2.2.1 i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have h1 : ¬ (m + i.val < m) := by omega
          have h2 : m + i.val < 2 * m := by omega
          simp only [eBase, Equiv.coe_fn_mk, Sum.elim_inr, Sum.elim_inl, cBA, cBB, h1, h2, ↓reduceDIte,
            dotProduct_concatVec, zero_dotProduct, add_zero, zero_add, Nat.add_sub_cancel_left,
            ← hdualV x i, ← hrV i y]
        have s3 : (∑ t : Fin r, dotProduct (cBA (eBase (Sum.inr (Sum.inr t)))) (concatVec x y) *
            dotProduct (cBB (eBase (Sum.inr (Sum.inr t)))) (concatVec x y)) =
            ∑ t : Fin r, (eDual x).2.2.2 t * (e y).2.2.2 t := by
          refine Finset.sum_congr rfl fun t _ => ?_
          have h1 : ¬ (2 * m + t.val < m) := by omega
          have h2 : ¬ (2 * m + t.val < 2 * m) := by omega
          simp only [eBase, Equiv.coe_fn_mk, Sum.elim_inr, cBA, cBB, h1, h2, ↓reduceDIte,
            dotProduct_concatVec, zero_dotProduct, add_zero, zero_add, Nat.add_sub_cancel_left,
            ← hdualZ x t, ← hrZ t y]
        rw [s1, s2, s3]; simp only [dotProduct]; ring
      set w := π (e y).1
      have hw_coord : ∀ a : Fin j, dotProduct (cW a) (concatVec x y) = w a := by
        intro a
        simp only [cW, dotProduct_concatVec, zero_dotProduct, zero_add, ← hrW a y]
        rfl
      have hB_exp : ∀ (v : Fin k → F2), dotProduct v (B w) = ∑ a : Fin j, w a * dotProduct v (B (Pi.single a 1)) := by
        intro v
        conv_lhs => rw [vec_eq_sum_single w, map_sum, dotProduct_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_smul, dotProduct_smul, smul_eq_mul]
      have hsumJ_term : (∑ a : Fin j, dotProduct (cW a) (concatVec x y) *
          ((dotProduct (cLin a) (concatVec x y) + l_q a) +
            ∑ idx : Fin J.card, coeffP a idx *
              (if (wiresOf gs2 (bitsOf (2 * n) (concatVec x y))).getD (resP.2 idx) false then (1 : F2) else 0))) =
          dotProduct l_q w + (∑ a : Fin j, ∑ b : Fin j, M_q a b * w a * w b) +
          dotProduct (eDual x).1 (B w) +
          ∑ i ∈ J, dotProduct (A i) (B w) * (e y).2.1 i * (e y).2.2.1 i := by
        simp_rw [hw_coord, hpVal]
        have hlin : ∀ a : Fin j, dotProduct (cLin a) (concatVec x y) =
            dotProduct (eDual x).1 (B (Pi.single a 1)) + ∑ b : Fin j, M_q a b * w b := by
          intro a
          simp only [cLin, dotProduct_concatVec, ← hdualS x (B (Pi.single a 1)), sum_dotProduct]
          congr 1
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [smul_dotProduct, smul_eq_mul, ← hrW b y]; rfl
        simp_rw [hlin]
        have h1 : (∑ a : Fin j, w a * ((dotProduct (eDual x).1 (B (Pi.single a 1)) + ∑ b : Fin j, M_q a b * w b + l_q a) +
            ∑ idx : Fin J.card, coeffP a idx * ((e y).2.1 (eJ idx).val * (e y).2.2.1 (eJ idx).val))) =
            (∑ a : Fin j, l_q a * w a) +
            (∑ a : Fin j, ∑ b : Fin j, M_q a b * w a * w b) +
            (∑ a : Fin j, w a * dotProduct (eDual x).1 (B (Pi.single a 1))) +
            (∑ a : Fin j, ∑ idx : Fin J.card, w a * coeffP a idx * ((e y).2.1 (eJ idx).val * (e y).2.2.1 (eJ idx).val)) := by
          have hstep : ∀ a : Fin j,
              w a * ((dotProduct (eDual x).1 (B (Pi.single a 1)) + ∑ b : Fin j, M_q a b * w b + l_q a) +
                ∑ idx : Fin J.card, coeffP a idx * ((e y).2.1 (eJ idx).val * (e y).2.2.1 (eJ idx).val)) =
              ((l_q a * w a + ∑ b : Fin j, M_q a b * w a * w b) +
                w a * dotProduct (eDual x).1 (B (Pi.single a 1))) +
              ∑ idx : Fin J.card, w a * coeffP a idx * ((e y).2.1 (eJ idx).val * (e y).2.2.1 (eJ idx).val) := by
            intro a
            rw [mul_add, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
            have hA : (∑ b : Fin j, w a * (M_q a b * w b)) = ∑ b : Fin j, M_q a b * w a * w b :=
              Finset.sum_congr rfl fun b _ => by ring
            have hB' : (∑ idx : Fin J.card, w a * (coeffP a idx * ((e y).2.1 (eJ idx).val * (e y).2.2.1 (eJ idx).val))) =
                ∑ idx : Fin J.card, w a * coeffP a idx * ((e y).2.1 (eJ idx).val * (e y).2.2.1 (eJ idx).val) :=
              Finset.sum_congr rfl fun idx _ => by ring
            rw [hA, hB']; ring
          simp_rw [hstep, Finset.sum_add_distrib]
        rw [h1, ← hB_exp (eDual x).1]
        have hJsum : (∑ a : Fin j, ∑ idx : Fin J.card, w a * coeffP a idx * ((e y).2.1 (eJ idx).val * (e y).2.2.1 (eJ idx).val)) =
            ∑ i ∈ J, dotProduct (A i) (B w) * (e y).2.1 i * (e y).2.2.1 i := by
          rw [Finset.sum_comm]
          have hinner : ∀ idx : Fin J.card,
              (∑ a : Fin j, w a * coeffP a idx * ((e y).2.1 (eJ idx).val * (e y).2.2.1 (eJ idx).val)) =
              dotProduct (A (eJ idx).val) (B w) * (e y).2.1 (eJ idx).val * (e y).2.2.1 (eJ idx).val := by
            intro idx
            rw [← Finset.sum_mul, ← hB_exp (A (eJ idx).val)]; ring
          simp_rw [hinner]
          rw [Equiv.sum_comp eJ (fun i : J => dotProduct (A i.val) (B w) * (e y).2.1 i.val * (e y).2.2.1 i.val)]
          exact Finset.sum_coe_sort J (fun i => dotProduct (A i) (B w) * (e y).2.1 i * (e y).2.2.1 i)
        rw [hJsum]
        rfl
      have hqw : h (B w) = z0 + dotProduct l_q w + ∑ a, ∑ b, M_q a b * w a * w b := hq_eq w
      rw [hsumBase, hsumJ_term, hqw]
      ring
    have htotal : (∑ x : Fin n → F2, ∑ y : Fin n → F2,
        if (Circuit.mk res4.1 res4.2).eval (bitsOf n x ++ bitsOf n y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1) =
        (2 : ℤ) ^ (n + r + m) * (mass : ℤ) := by
      rw [Finset.sum_comm]
      have hinner_y : ∀ y : Fin n → F2,
          (∑ x : Fin n → F2,
            if (Circuit.mk res4.1 res4.2).eval (bitsOf n x ++ bitsOf n y) = decide (dotProduct x y + g y = 1)
            then (1 : ℤ) else -1) =
          if (e y).1 ∈ LinearMap.range B then
            (2 : ℤ) ^ n * signBool (decide ((∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ J),
              dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i) = 1))
          else 0 := by
        intro y
        set s := (e y).1
        set u := (e y).2.1
        set v := (e y).2.2.1
        set w := π s
        have hterm : ∀ x : Fin n → F2,
            (if (Circuit.mk res4.1 res4.2).eval (bitsOf n x ++ bitsOf n y) = decide (dotProduct x y + g y = 1)
              then (1 : ℤ) else -1) =
            signBool (decide (dotProduct (B w + s) (eDual x).1 = 1)) *
              signBool (decide ((h (B w) + h s +
                (∑ i ∈ J, dotProduct (A i) (B w) * u i * v i) +
                (∑ i : Fin m, dotProduct (A i) s * u i * v i)) = 1)) := by
          intro x
          rw [hCe x y]
          have hxy : dotProduct x y = dotProduct (eDual x).1 s + dotProduct (eDual x).2.1 u +
              dotProduct (eDual x).2.2.1 v + dotProduct (eDual x).2.2.2 (e y).2.2.2 := hdot_dual x y
          have hiff : ∀ b1 b2 : F2, (if decide (b1 = 1) = decide (b2 = 1) then (1 : ℤ) else -1) =
              signBool (decide (b1 + b2 = 1)) := by
            intro b1 b2; fin_cases b1 <;> fin_cases b2 <;> decide
          rw [hiff, ← signBool_xor, ← zmod2_add_decide]
          congr 2
          rw [hxy]
          dsimp only [g, s, u, v, w]
          rw [add_dotProduct, dotProduct_comm (B (π (e y).1)), dotProduct_comm (e y).1]
          have hcancel : ∀ p q r1 r2 : F2,
              (p + q + r1 + r2) + (r1 + r2) = p + q := by
            intro p q r1 r2
            have : (p + q + r1 + r2) + (r1 + r2) = p + q + (r1 + r1) + (r2 + r2) := by ring
            rw [this, z2_add_self, z2_add_self, add_zero, add_zero]
          have hbig : (h (B (π (e y).1)) + dotProduct (eDual x).1 (B (π (e y).1)) +
              (∑ i ∈ J, dotProduct (A i) (B (π (e y).1)) * (e y).2.1 i * (e y).2.2.1 i) +
              dotProduct (eDual x).2.1 (e y).2.1 + dotProduct (eDual x).2.2.1 (e y).2.2.1 +
              dotProduct (eDual x).2.2.2 (e y).2.2.2) +
              (dotProduct (eDual x).1 (e y).1 + dotProduct (eDual x).2.1 (e y).2.1 +
              dotProduct (eDual x).2.2.1 (e y).2.2.1 + dotProduct (eDual x).2.2.2 (e y).2.2.2 +
              (h (e y).1 + ∑ i : Fin m, dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i)) =
              (dotProduct (eDual x).1 (B (π (e y).1)) + dotProduct (eDual x).1 (e y).1) +
              (h (B (π (e y).1)) + h (e y).1 +
                (∑ i ∈ J, dotProduct (A i) (B (π (e y).1)) * (e y).2.1 i * (e y).2.2.1 i) +
                ∑ i : Fin m, dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i) +
              ((dotProduct (eDual x).2.1 (e y).2.1 + dotProduct (eDual x).2.1 (e y).2.1) +
               (dotProduct (eDual x).2.2.1 (e y).2.2.1 + dotProduct (eDual x).2.2.1 (e y).2.2.1) +
               (dotProduct (eDual x).2.2.2 (e y).2.2.2 + dotProduct (eDual x).2.2.2 (e y).2.2.2)) := by ring
          rw [hbig]; simp only [z2_add_self, add_zero]
        simp_rw [hterm, ← Finset.sum_mul]
        have hxsum : (∑ x : Fin n → F2, signBool (decide (dotProduct (B w + s) (eDual x).1 = 1))) =
            (2 : ℤ) ^ base * ∑ xS : Fin k → F2, signBool (decide (dotProduct (B w + s) xS = 1)) := by
          rw [← Equiv.sum_comp eDual.symm.toEquiv]
          simp only [LinearEquiv.coe_toEquiv, LinearEquiv.apply_symm_apply]
          rw [Fintype.sum_prod_type]
          have hconst : ∀ xS : Fin k → F2,
              (∑ _rest : (Fin m → F2) × ((Fin m → F2) × (Fin r → F2)),
                signBool (decide (dotProduct (B w + s) xS = 1))) =
              (2 : ℤ) ^ base * signBool (decide (dotProduct (B w + s) xS = 1)) := by
            intro xS
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_pi,
              Finset.prod_const, Fintype.card_fin, ZMod.card, nsmul_eq_mul]
            push_cast
            have hpow : (2 : ℤ) ^ m * ((2 : ℤ) ^ m * (2 : ℤ) ^ r) = (2 : ℤ) ^ base := by
              dsimp only [base]; rw [← pow_add, ← pow_add]; congr 1; omega
            rw [hpow]
          simp_rw [hconst, ← Finset.mul_sum]
        rw [hxsum]
        by_cases hsB : s ∈ LinearMap.range B
        · simp only [hsB, ↓reduceIte]
          rcases hsB with ⟨w0, hw0⟩
          have hBw : B w = s := by dsimp only [w]; rw [← hw0, hπB w0]
          have hzero : B w + s = 0 := by rw [hBw]; exact zmod2_vec_add_self s
          rw [hzero]
          have hcardS : (∑ _xS : Fin k → F2, signBool (decide (dotProduct (0 : Fin k → F2) _xS = 1))) = (2 : ℤ) ^ k := by
            simp only [zero_dotProduct]
            change (∑ _xS : Fin k → F2, (1 : ℤ)) = (2 : ℤ) ^ k
            simp [ZMod.card]
          rw [hcardS, ← pow_add, show base + k = n by omega]
          congr 2
          rw [hBw, z2_add_self, zero_add]
          have hsplit : (∑ i : Fin m, dotProduct (A i) s * u i * v i) =
              (∑ i ∈ J, dotProduct (A i) s * u i * v i) +
              (∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ J), dotProduct (A i) s * u i * v i) := by
            have h1 := (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => i ∈ J)
              (fun i => dotProduct (A i) s * u i * v i)).symm
            have hfilt : Finset.univ.filter (fun i : Fin m => i ∈ J) = J := by ext i; simp
            rwa [hfilt] at h1
          rw [hsplit, ← add_assoc, z2_add_self, zero_add]
        · simp only [hsB, ↓reduceIte]
          have hne : B w + s ≠ 0 := by
            intro h0
            apply hsB
            refine ⟨w, ?_⟩
            funext a
            exact z2_eq_of_add_eq_zero (congrFun h0 a)
          rw [sum_sign_dot_univ _ hne, mul_zero, zero_mul]
      simp_rw [hinner_y]
      rw [← Equiv.sum_comp e.symm.toEquiv]
      simp only [LinearEquiv.coe_toEquiv, LinearEquiv.apply_symm_apply]
      rw [Fintype.sum_prod_type]
      have hs_sum : (∑ s : Fin k → F2,
          ∑ rest : (Fin m → F2) × ((Fin m → F2) × (Fin r → F2)),
            if s ∈ LinearMap.range B then
              (2 : ℤ) ^ n * signBool (decide ((∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ J),
                dotProduct (A i) s * rest.1 i * rest.2.1 i) = 1))
            else 0) =
          ∑ w : Fin j → F2,
            ∑ rest : (Fin m → F2) × ((Fin m → F2) × (Fin r → F2)),
              (2 : ℤ) ^ n * signBool (decide ((∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ J),
                dotProduct (A i) (B w) * rest.1 i * rest.2.1 i) = 1)) := by
        have hstep : ∀ s : Fin k → F2,
            (∑ rest : (Fin m → F2) × ((Fin m → F2) × (Fin r → F2)),
              if s ∈ LinearMap.range B then
                (2 : ℤ) ^ n * signBool (decide ((∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ J),
                  dotProduct (A i) s * rest.1 i * rest.2.1 i) = 1))
              else 0) =
            if s ∈ LinearMap.range B then
              ∑ rest : (Fin m → F2) × ((Fin m → F2) × (Fin r → F2)),
                (2 : ℤ) ^ n * signBool (decide ((∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ J),
                  dotProduct (A i) s * rest.1 i * rest.2.1 i) = 1))
            else 0 := by
          intro s; split_ifs <;> simp
        simp_rw [hstep, ← Finset.sum_filter]
        have himg : Finset.univ.image (fun w : Fin j → F2 => B w) =
            Finset.univ.filter (fun s : Fin k → F2 => s ∈ LinearMap.range B) := by
          ext s; simp [LinearMap.mem_range]
        rw [← himg, Finset.sum_image (fun w1 _ w2 _ h => hB h)]
      rw [hs_sum]
      have hper_w : ∀ w : Fin j → F2,
          (∑ rest : (Fin m → F2) × ((Fin m → F2) × (Fin r → F2)),
            (2 : ℤ) ^ n * signBool (decide ((∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ J),
              dotProduct (A i) (B w) * rest.1 i * rest.2.1 i) = 1))) =
          (2 : ℤ) ^ (n + r + m) * (2 : ℤ) ^ (m - weight (B w)) := by
        intro w
        rw [← Finset.mul_sum]
        let eRest : ((Fin m → F2) × (Fin m → F2)) × (Fin r → F2) ≃
            (Fin m → F2) × ((Fin m → F2) × (Fin r → F2)) :=
          { toFun := fun p => (p.1.1, (p.1.2, p.2))
            invFun := fun p => ((p.1, p.2.1), p.2.2)
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [← Equiv.sum_comp eRest, Fintype.sum_prod_type]
        have hz_const : ∀ uv : (Fin m → F2) × (Fin m → F2),
            (∑ _z : Fin r → F2,
              signBool (decide ((∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ J),
                dotProduct (A i) (B w) * uv.1 i * uv.2 i) = 1))) =
            (2 : ℤ) ^ r * signBool (decide ((∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ J),
              dotProduct (A i) (B w) * uv.1 i * uv.2 i) = 1)) := by
          intro uv; simp [ZMod.card]
        simp_rw [eRest, Equiv.coe_fn_mk, hz_const, ← Finset.mul_sum]
        have huv_sum : (∑ uv : (Fin m → F2) × (Fin m → F2),
            signBool (decide ((∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ J),
              dotProduct (A i) (B w) * uv.1 i * uv.2 i) = 1))) =
            (2 : ℤ) ^ m * (2 : ℤ) ^ (m - weight (B w)) := by
          have hrew_prod : ∀ uv : (Fin m → F2) × (Fin m → F2),
              signBool (decide ((∑ i ∈ Finset.univ.filter (fun i : Fin m => i ∉ J),
                dotProduct (A i) (B w) * uv.1 i * uv.2 i) = 1)) =
              ∏ i : Fin m, signBool (decide ((if i ∉ J then dotProduct (A i) (B w) * uv.1 i * uv.2 i else 0) = 1)) := by
            intro uv
            rw [← signBool_sum_f2 Finset.univ, ← Finset.sum_filter]
          simp_rw [hrew_prod]
          rw [sum_prod_pairs (fun i p => signBool (decide ((if i ∉ J then dotProduct (A i) (B w) * p.1 * p.2 else 0) = 1)))]
          have hfactor : ∀ i : Fin m,
              (∑ p : F2 × F2, signBool (decide ((if i ∉ J then dotProduct (A i) (B w) * p.1 * p.2 else 0) = 1))) =
              (2 : ℤ) * (if i ∉ J ∧ dotProduct (A i) (B w) ≠ 0 then (1 : ℤ) else 2) := by
            intro i
            by_cases hiJ : i ∉ J
            · simp only [hiJ, ↓reduceIte, true_and]
              rcases zmod2_cases (dotProduct (A i) (B w)) with h0 | h1
              · rw [h0]; decide
              · rw [h1]; decide
            · simp only [hiJ, ↓reduceIte, false_and]; decide
          simp_rw [hfactor, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          congr 1
          rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
          congr 1
          have hcomp := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin m))
            (fun i => i ∉ J ∧ dotProduct (A i) (B w) ≠ 0) (fun _ => (1 : ℕ))
          simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at hcomp
          dsimp only [weight]; omega
        rw [huv_sum, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
      simp_rw [hper_w, ← Finset.mul_sum]
      congr 1
      dsimp only [mass]
      push_cast; rfl
    rw [htotal, Int.natAbs_mul]
    have h1 : ((2 : ℤ) ^ (n + r + m)).natAbs = 2 ^ (n + r + m) := by
      rw [show (2 : ℤ) ^ (n + r + m) = ((2 ^ (n + r + m) : ℕ) : ℤ) by push_cast; rfl, Int.natAbs_natCast]
    rw [h1, Int.natAbs_natCast, ← mul_assoc, ← pow_add]
    congr 2
    omega

lemma conjunct1_back (k m r : ℕ)
    (e : (Fin (k + 2 * m + r) → F2) ≃ₗ[F2]
      (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2))))
    (A : Fin m → (Fin k → F2)) (h : (Fin k → F2) → F2)
    (s T : ℕ) (hs : s ≤ 2 * m + r) (hT : T ≤ 2 ^ (k + 2 * m + r + s)) :
    let n := k + 2 * m + r
    let g := fun y : Fin n → F2 =>
      h (e y).1 + ∑ i : Fin m, dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
    ∃ C : Circuit, legalGates (2 * n) C.gates ∧ costGates C.gates ≤ s ∧
      T ≤ (∑ x : Fin n → F2, ∑ y : Fin n → F2,
        if C.eval (bitsOf n x ++ bitsOf n y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs := by
  intro n g
  let E0 := (Fin m → F2) × ((Fin m → F2) × (Fin r → F2))
  have hdimE0 : Module.finrank F2 E0 = 2 * m + r := by
    simp only [E0, Module.finrank_prod, Module.finrank_fin_fun]; omega
  let eE0 : (Fin (2 * m + r) → F2) ≃ₗ[F2] E0 :=
    LinearEquiv.ofFinrankEq _ _ (by rw [Module.finrank_fin_fun, hdimE0])
  let embS : (Fin s → F2) →ₗ[F2] (Fin (2 * m + r) → F2) :=
    { toFun := fun v idx => if hlt : idx.val < s then v ⟨idx.val, hlt⟩ else 0
      map_add' := fun u v => by funext idx; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c v => by funext idx; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
  have hembS_inj : Function.Injective embS := by
    intro u v huv
    funext i
    have := congrFun huv ⟨i.val, by omega⟩
    simpa [embS, i.isLt] using this
  let B0 : (Fin s → F2) →ₗ[F2] (Fin n → F2) :=
    e.symm.toLinearMap.comp ((LinearMap.inr F2 (Fin k → F2) E0).comp (eE0.toLinearMap.comp embS))
  have hB0_inj : Function.Injective B0 :=
    e.symm.injective.comp (LinearMap.inr_injective.comp (eE0.injective.comp hembS_inj))
  have hB0_fst : ∀ v : Fin s → F2, (e (B0 v)).1 = 0 := by
    intro v; simp [B0]
  apply viaFlat_to_viaCircuit n s g T B0 0 (fun _ => h 0) hB0_inj (isQuad_const (h 0))
  have hsum : (∑ v : Fin s → F2, if g (0 + B0 v) = h 0 then (1 : ℤ) else -1).natAbs = 2 ^ s := by
    have hg0 : ∀ v : Fin s → F2, g (0 + B0 v) = h 0 := by
      intro v
      rw [zero_add]
      simp [g, hB0_fst v]
    simp only [hg0, ↓reduceIte]
    have hcard : (∑ _v : Fin s → F2, (1 : ℤ)) = ((2 ^ s : ℕ) : ℤ) := by
      simp [ZMod.card]
    rw [hcard, Int.natAbs_natCast]
  rw [hsum, ← pow_add]
  exact hT



lemma weighted_avg_prod_exists {N K : ℕ} (hN : 0 < N) (r B : Fin N → ℕ) (M : ℕ)
    (hsum : ∑ i : Fin N, 2 ^ (K - r i) = 2 ^ K)
    (hM : M ≤ ∑ i : Fin N, 2 ^ (K - r i) * B i) :
    ∃ i : Fin N, M ≤ 2 ^ K * B i := by
  by_contra hnot
  push Not at hnot
  have hlt : ∑ i : Fin N, 2 ^ (K - r i) * (2 ^ K * B i) < ∑ i : Fin N, 2 ^ (K - r i) * M := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
    intro i _
    exact Nat.mul_lt_mul_of_pos_left (hnot i) (Nat.pow_pos (by omega))
  have hlhs : ∑ i : Fin N, 2 ^ (K - r i) * (2 ^ K * B i) =
      2 ^ K * ∑ i : Fin N, 2 ^ (K - r i) * B i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hrhs : ∑ i : Fin N, 2 ^ (K - r i) * M = 2 ^ K * M := by
    rw [← Finset.sum_mul, hsum]
  rw [hlhs, hrhs] at hlt
  have hle : 2 ^ K * M ≤ 2 ^ K * ∑ i : Fin N, 2 ^ (K - r i) * B i := Nat.mul_le_mul_left _ hM
  omega

lemma weighted_avg_exists {N K : ℕ} (hN : 0 < N) (r S : Fin N → ℕ) (M : ℕ)
    (hr : ∀ i, r i ≤ K) (hsum : ∑ i : Fin N, 2 ^ (K - r i) = 2 ^ K)
    (hM : M ≤ ∑ i : Fin N, S i) :
    ∃ i : Fin N, M ≤ 2 ^ (r i) * S i := by
  by_contra hnot
  push Not at hnot
  have hlt : ∑ i : Fin N, 2 ^ (K - r i) * (2 ^ (r i) * S i) < ∑ i : Fin N, 2 ^ (K - r i) * M := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
    intro i _
    exact Nat.mul_lt_mul_of_pos_left (hnot i) (Nat.pow_pos (by omega))
  have hlhs : ∑ i : Fin N, 2 ^ (K - r i) * (2 ^ (r i) * S i) = 2 ^ K * ∑ i : Fin N, S i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hr i)]
  have hrhs : ∑ i : Fin N, 2 ^ (K - r i) * M = 2 ^ K * M := by
    rw [← Finset.sum_mul, hsum]
  rw [hlhs, hrhs] at hlt
  have hle : 2 ^ K * M ≤ 2 ^ K * ∑ i : Fin N, S i := Nat.mul_le_mul_left _ hM
  omega

lemma natAbs_sum_le_sum_natAbs {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs := by
  have htri := Finset.abs_sum_le_sum_abs f s
  have hcast : ((∑ i ∈ s, f i).natAbs : ℤ) ≤ ((∑ i ∈ s, (f i).natAbs : ℕ) : ℤ) := by
    simpa [Int.natCast_natAbs, Nat.cast_sum] using htri
  exact Int.ofNat_le.mp hcast

lemma bilinear_expand {d : ℕ} (L1 L2 : (Fin d → F2) →ₗ[F2] F2) (q h : Fin d → F2) :
    L1 q * L2 h + L1 h * L2 q =
      ∑ α : Fin d, ∑ β : Fin d,
        (L1 (Pi.single α 1) * L2 (Pi.single β 1) + L1 (Pi.single β 1) * L2 (Pi.single α 1)) * h β * q α := by
  have h1 : L1 q * L2 h = ∑ α : Fin d, ∑ β : Fin d, (L1 (Pi.single α 1) * L2 (Pi.single β 1)) * h β * q α := by
    conv_lhs => rw [vec_eq_sum_single q, vec_eq_sum_single h, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
  have h2 : L1 h * L2 q = ∑ α : Fin d, ∑ β : Fin d, (L1 (Pi.single β 1) * L2 (Pi.single α 1)) * h β * q α := by
    conv_lhs => rw [vec_eq_sum_single h, vec_eq_sum_single q, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun β _ => by ring

lemma diagPair_mulVec_dot {m2 : ℕ} (d : Fin m2 → F2) (q h : Fin (2 * m2) → F2) :
    dotProduct (diagPair d *ᵥ h) q =
      ∑ t : Fin m2, d t * (q (pairIdx t false) * h (pairIdx t true) + q (pairIdx t true) * h (pairIdx t false)) := by
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul]
  rw [← Equiv.sum_comp (pairEquiv m2)]
  simp_rw [← Equiv.sum_comp (pairEquiv m2)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Fintype.sum_bool]
  have hpair_f : ∀ s : Fin m2 × Bool,
      diagPair d (pairIdx t false) (pairEquiv m2 s) * h (pairEquiv m2 s) * q (pairIdx t false) =
        if s = (t, true) then d t * q (pairIdx t false) * h (pairIdx t true) else 0 := by
    rintro ⟨s, b⟩
    simp only [pairEquiv, Equiv.coe_fn_mk, diagPair, Matrix.of_apply]
    by_cases hst : s = t ∧ b = true
    · rcases hst with ⟨rfl, rfl⟩
      have hdiv : (pairIdx s false).val / 2 = (pairIdx s true).val / 2 := by simp [pairIdx]; omega
      have hne : pairIdx s false ≠ pairIdx s true := by
        intro heq; have := congrArg Fin.val heq; simp [pairIdx] at this
      have hidx : (⟨(pairIdx s false).val / 2, by omega⟩ : Fin m2) = s := by
        apply Fin.ext; simp [pairIdx]
      have hcond : (pairIdx s false).val / 2 = (pairIdx s true).val / 2 ∧ pairIdx s false ≠ pairIdx s true := ⟨hdiv, hne⟩
      rw [ite_eq_left_iff.mpr (fun hn => absurd hcond hn), ite_eq_left_iff.mpr (fun hn => absurd rfl hn), hidx]
      ring
    · have hnot : ¬ ((pairIdx t false).val / 2 = (pairIdx s b).val / 2 ∧ pairIdx t false ≠ pairIdx s b) := by
        rintro ⟨hdiv, hne⟩
        cases b
        · have hs_eq : s = t := by apply Fin.ext; simp [pairIdx] at hdiv; omega
          subst hs_eq; exact hne rfl
        · have hs_eq : s = t := by apply Fin.ext; simp [pairIdx] at hdiv; omega
          exact hst ⟨hs_eq, rfl⟩
      have hne_pair : (s, b) ≠ (t, true) := fun heq => hst ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
      simp [hnot, hne_pair]
  have hpair_t : ∀ s : Fin m2 × Bool,
      diagPair d (pairIdx t true) (pairEquiv m2 s) * h (pairEquiv m2 s) * q (pairIdx t true) =
        if s = (t, false) then d t * q (pairIdx t true) * h (pairIdx t false) else 0 := by
    rintro ⟨s, b⟩
    simp only [pairEquiv, Equiv.coe_fn_mk, diagPair, Matrix.of_apply]
    by_cases hst : s = t ∧ b = false
    · rcases hst with ⟨rfl, rfl⟩
      have hdiv : (pairIdx s true).val / 2 = (pairIdx s false).val / 2 := by simp [pairIdx]; omega
      have hne : pairIdx s true ≠ pairIdx s false := by
        intro heq; have := congrArg Fin.val heq; simp [pairIdx] at this
      have hidx : (⟨(pairIdx s true).val / 2, by omega⟩ : Fin m2) = s := by
        apply Fin.ext; simp [pairIdx]; omega
      have hcond : (pairIdx s true).val / 2 = (pairIdx s false).val / 2 ∧ pairIdx s true ≠ pairIdx s false := ⟨hdiv, hne⟩
      rw [ite_eq_left_iff.mpr (fun hn => absurd hcond hn), ite_eq_left_iff.mpr (fun hn => absurd rfl hn), hidx]
      ring
    · have hnot : ¬ ((pairIdx t true).val / 2 = (pairIdx s b).val / 2 ∧ pairIdx t true ≠ pairIdx s b) := by
        rintro ⟨hdiv, hne⟩
        cases b
        · have hs_eq : s = t := by apply Fin.ext; simp [pairIdx] at hdiv; omega
          exact hst ⟨hs_eq, rfl⟩
        · have hs_eq : s = t := by apply Fin.ext; simp [pairIdx] at hdiv; omega
          subst hs_eq; exact hne rfl
      have hne_pair : (s, b) ≠ (t, false) := fun heq => hst ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
      simp [hnot, hne_pair]
  have hf_sum : (∑ s : Fin m2 × Bool,
      diagPair d (pairEquiv m2 (t, false)) (pairEquiv m2 s) * h (pairEquiv m2 s) * q (pairEquiv m2 (t, false))) =
      d t * q (pairIdx t false) * h (pairIdx t true) := by
    change (∑ s : Fin m2 × Bool,
      diagPair d (pairIdx t false) (pairEquiv m2 s) * h (pairEquiv m2 s) * q (pairIdx t false)) = _
    simp_rw [hpair_f]
    simp
  have ht_sum : (∑ s : Fin m2 × Bool,
      diagPair d (pairEquiv m2 (t, true)) (pairEquiv m2 s) * h (pairEquiv m2 s) * q (pairEquiv m2 (t, true))) =
      d t * q (pairIdx t true) * h (pairIdx t false) := by
    change (∑ s : Fin m2 × Bool,
      diagPair d (pairIdx t true) (pairEquiv m2 s) * h (pairEquiv m2 s) * q (pairIdx t true)) = _
    simp_rw [hpair_t]
    simp
  rw [hf_sum, ht_sum]; ring

def polarMatrix {k m r m1 m2 : ℕ}
    (e : (Fin (k + 2 * m + r) → F2) ≃ₗ[F2]
      (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2))))
    (A : Fin m → (Fin k → F2)) (a1 : Fin (k + 2 * m + r) → F2)
    (σD : (Fin (2 * m1) → F2) →ₗ[F2] (Fin (k + 2 * m + r) → F2))
    (τ2 : (Fin (2 * m2) → F2) →ₗ[F2] (Fin (2 * m1) → F2))
    (sTap : Fin (k + 2 * m + r) → (Fin (2 * m1) → F2)) :
    Matrix (Fin (2 * m2)) (Fin (2 * m2)) F2 :=
  let Lq : (Fin (2 * m2) → F2) →ₗ[F2] (Fin (k + 2 * m + r) → F2) := σD.comp τ2
  let Ltap : Fin (k + 2 * m + r) → (Fin (2 * m2) → F2) →ₗ[F2] F2 := fun l => (dotLin (sTap l)).comp τ2
  let Ly : Fin (k + 2 * m + r) → (Fin (2 * m2) → F2) →ₗ[F2] F2 := fun l => (LinearMap.proj l).comp Lq
  let Lu : Fin m → (Fin (2 * m2) → F2) →ₗ[F2] F2 := fun i =>
    (LinearMap.proj i).comp ((LinearMap.fst F2 _ _).comp ((LinearMap.snd F2 _ _).comp (e.toLinearMap.comp Lq)))
  let Lv : Fin m → (Fin (2 * m2) → F2) →ₗ[F2] F2 := fun i =>
    (LinearMap.proj i).comp ((LinearMap.fst F2 _ _).comp ((LinearMap.snd F2 _ _).comp ((LinearMap.snd F2 _ _).comp (e.toLinearMap.comp Lq))))
  Matrix.of fun α β =>
    (∑ l : Fin (k + 2 * m + r), (Ltap l (Pi.single α 1) * Ly l (Pi.single β 1) +
      Ltap l (Pi.single β 1) * Ly l (Pi.single α 1))) +
    (∑ i : Fin m, dotProduct (A i) (e a1).1 *
      (Lu i (Pi.single α 1) * Lv i (Pi.single β 1) +
       Lu i (Pi.single β 1) * Lv i (Pi.single α 1)))

lemma polarMatrix_diag {k m r m1 m2 : ℕ}
    (e : (Fin (k + 2 * m + r) → F2) ≃ₗ[F2]
      (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2))))
    (A : Fin m → (Fin k → F2)) (a1 : Fin (k + 2 * m + r) → F2)
    (σD : (Fin (2 * m1) → F2) →ₗ[F2] (Fin (k + 2 * m + r) → F2))
    (τ2 : (Fin (2 * m2) → F2) →ₗ[F2] (Fin (2 * m1) → F2))
    (sTap : Fin (k + 2 * m + r) → (Fin (2 * m1) → F2)) (α : Fin (2 * m2)) :
    polarMatrix e A a1 σD τ2 sTap α α = 0 := by
  simp only [polarMatrix, Matrix.of_apply]
  have h1 : (∑ l : Fin (k + 2 * m + r),
      (((dotLin (sTap l)).comp τ2) (Pi.single α 1) * ((LinearMap.proj l).comp (σD.comp τ2)) (Pi.single α 1) +
       ((dotLin (sTap l)).comp τ2) (Pi.single α 1) * ((LinearMap.proj l).comp (σD.comp τ2)) (Pi.single α 1))) = 0 :=
    Finset.sum_eq_zero fun l _ => z2_add_self _
  have h2 : (∑ i : Fin m, dotProduct (A i) (e a1).1 *
      (((LinearMap.proj i).comp ((LinearMap.fst F2 _ _).comp ((LinearMap.snd F2 _ _).comp (e.toLinearMap.comp (σD.comp τ2))))) (Pi.single α 1) *
       ((LinearMap.proj i).comp ((LinearMap.fst F2 _ _).comp ((LinearMap.snd F2 _ _).comp ((LinearMap.snd F2 _ _).comp (e.toLinearMap.comp (σD.comp τ2)))))) (Pi.single α 1) +
       ((LinearMap.proj i).comp ((LinearMap.fst F2 _ _).comp ((LinearMap.snd F2 _ _).comp (e.toLinearMap.comp (σD.comp τ2))))) (Pi.single α 1) *
       ((LinearMap.proj i).comp ((LinearMap.fst F2 _ _).comp ((LinearMap.snd F2 _ _).comp ((LinearMap.snd F2 _ _).comp (e.toLinearMap.comp (σD.comp τ2)))))) (Pi.single α 1))) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [z2_add_self, mul_zero]
  rw [h1, h2, add_zero]

lemma polarMatrix_symm {k m r m1 m2 : ℕ}
    (e : (Fin (k + 2 * m + r) → F2) ≃ₗ[F2]
      (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2))))
    (A : Fin m → (Fin k → F2)) (a1 : Fin (k + 2 * m + r) → F2)
    (σD : (Fin (2 * m1) → F2) →ₗ[F2] (Fin (k + 2 * m + r) → F2))
    (τ2 : (Fin (2 * m2) → F2) →ₗ[F2] (Fin (2 * m1) → F2))
    (sTap : Fin (k + 2 * m + r) → (Fin (2 * m1) → F2)) (α β : Fin (2 * m2)) :
    polarMatrix e A a1 σD τ2 sTap α β = polarMatrix e A a1 σD τ2 sTap β α := by
  simp only [polarMatrix, Matrix.of_apply]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => add_comm _ _
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 1; exact add_comm _ _

lemma conjunct2_gauss_leaf {k m r j0 m1 m2 : ℕ}
    (e : (Fin (k + 2 * m + r) → F2) ≃ₗ[F2]
      (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2))))
    (A : Fin m → (Fin k → F2)) (h : (Fin k → F2) → F2)
    (D0 : Circuit) (tap0 : Fin (k + 2 * m + r) → ℕ)
    (a1 : Fin (k + 2 * m + r) → F2)
    (B : (Fin j0 → F2) →ₗ[F2] (Fin k → F2))
    (Act : Finset (Fin m)) (hAct : Act = Finset.univ.filter (fun i : Fin m => ∃ w : Fin j0 → F2, dotProduct (A i) (B w) ≠ 0))
    (eAct : Fin m1 ≃ Act) (J0 : Finset (Fin m1)) (eRem : Fin m2 ≃ {t : Fin m1 // t ∉ J0})
    (σS : (Fin j0 → F2) →ₗ[F2] (Fin (k + 2 * m + r) → F2))
    (hσS_fst : ∀ w, (e (σS w)).1 = B w)
    (σD : (Fin (2 * m1) → F2) →ₗ[F2] (Fin (k + 2 * m + r) → F2))
    (hσD_fst : ∀ p, (e (σD p)).1 = 0)
    (hσD_u : ∀ p (t : Fin m1), (e (σD p)).2.1 (eAct t).val = p (pairIdx t false))
    (hσD_v : ∀ p (t : Fin m1), (e (σD p)).2.2.1 (eAct t).val = p (pairIdx t true))
    (τ2 : (Fin (2 * m2) → F2) →ₗ[F2] (Fin (2 * m1) → F2))
    (hτ2_coord : ∀ (t' : Fin m2) (b : Bool) (q : Fin (2 * m2) → F2),
      τ2 q (pairIdx (eRem t').val b) = q (pairIdx t' b))
    (hτ2_kill : ∀ t ∈ J0, (∀ q, τ2 q (pairIdx t false) = 0) ∨ (∀ q, τ2 q (pairIdx t true) = 0))
    (pBase : Fin (2 * m1) → F2) (w : Fin j0 → F2)
    (sOut : Fin (2 * m1) → F2) (bOut : Bool)
    (sTap : Fin (k + 2 * m + r) → (Fin (2 * m1) → F2)) (bTap : Fin (k + 2 * m + r) → Bool)
    (hOut_eval : ∀ q : Fin (2 * m2) → F2,
      D0.eval (bitsOf (k + 2 * m + r) (a1 + σD (pBase + τ2 q) + σS w)) =
        Bool.xor bOut (decide (dotProduct sOut (τ2 q) = 1)))
    (hTap_eval : ∀ (l : Fin (k + 2 * m + r)) (q : Fin (2 * m2) → F2),
      (D0.wires (bitsOf (k + 2 * m + r) (a1 + σD (pBase + τ2 q) + σS w))).getD (tap0 l) false =
        Bool.xor (bTap l) (decide (dotProduct (sTap l) (τ2 q) = 1))) :
    let n := k + 2 * m + r
    let g : (Fin n → F2) → F2 := fun y =>
      h (e y).1 + ∑ i : Fin m, dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
    let pos0 : (Fin n → F2) → (Fin n → F2) := fun y l =>
      if (D0.wires (bitsOf n y)).getD (tap0 l) false then (1 : F2) else 0
    let K := polarMatrix e A a1 σD τ2 sTap
    let cVec : Fin m2 → F2 := fun t' => dotProduct (A (eAct (eRem t').val).val) (B w)
    (∑ q : Fin (2 * m2) → F2,
      signBool (Bool.xor (D0.eval (bitsOf n (a1 + σD (pBase + τ2 q) + σS w)))
        (decide (dotProduct (pos0 (a1 + σD (pBase + τ2 q) + σS w)) (a1 + σD (pBase + τ2 q) + σS w) = 1))) *
      signBool (decide (g (a1 + σD (pBase + τ2 q) + σS w) = 1))).natAbs ≤
      2 ^ (2 * m2 - (K + diagPair cVec).rank / 2) := by
  intro n g pos0 K cVec
  let Lq : (Fin (2 * m2) → F2) →ₗ[F2] (Fin n → F2) := σD.comp τ2
  let Ltap : Fin n → (Fin (2 * m2) → F2) →ₗ[F2] F2 := fun l => (dotLin (sTap l)).comp τ2
  let Ly : Fin n → (Fin (2 * m2) → F2) →ₗ[F2] F2 := fun l => (LinearMap.proj l).comp Lq
  let Lu : Fin m → (Fin (2 * m2) → F2) →ₗ[F2] F2 := fun i =>
    (LinearMap.proj i).comp ((LinearMap.fst F2 _ _).comp ((LinearMap.snd F2 _ _).comp (e.toLinearMap.comp Lq)))
  let Lv : Fin m → (Fin (2 * m2) → F2) →ₗ[F2] F2 := fun i =>
    (LinearMap.proj i).comp ((LinearMap.fst F2 _ _).comp ((LinearMap.snd F2 _ _).comp ((LinearMap.snd F2 _ _).comp (e.toLinearMap.comp Lq))))
  let yq : (Fin (2 * m2) → F2) → (Fin n → F2) := fun q => a1 + σD (pBase + τ2 q) + σS w
  let E : (Fin (2 * m2) → F2) → F2 := fun q =>
    (if D0.eval (bitsOf n (yq q)) then (1 : F2) else 0) +
    dotProduct (pos0 (yq q)) (yq q) + g (yq q)
  have hterm_eq : ∀ q : Fin (2 * m2) → F2,
      signBool (Bool.xor (D0.eval (bitsOf n (yq q))) (decide (dotProduct (pos0 (yq q)) (yq q) = 1))) *
        signBool (decide (g (yq q) = 1)) = signBool (decide (E q = 1)) := by
    intro q
    dsimp only [E]
    rw [zmod2_add_decide ((if D0.eval (bitsOf n (yq q)) then (1 : F2) else 0) + dotProduct (pos0 (yq q)) (yq q)) (g (yq q)),
      zmod2_add_decide (if D0.eval (bitsOf n (yq q)) then (1 : F2) else 0) (dotProduct (pos0 (yq q)) (yq q)),
      zmod2_bool_decide, ← signBool_xor]
  have hsum_eq :
      (∑ q : Fin (2 * m2) → F2,
        signBool (Bool.xor (D0.eval (bitsOf n (a1 + σD (pBase + τ2 q) + σS w)))
          (decide (dotProduct (pos0 (a1 + σD (pBase + τ2 q) + σS w)) (a1 + σD (pBase + τ2 q) + σS w) = 1))) *
        signBool (decide (g (a1 + σD (pBase + τ2 q) + σS w) = 1))) =
      ∑ q : Fin (2 * m2) → F2, signBool (decide (E q = 1)) :=
    Finset.sum_congr rfl fun q _ => hterm_eq q
  rw [hsum_eq]
  have hyq_shift : ∀ q : Fin (2 * m2) → F2, yq q = yq 0 + Lq q := by
    intro q
    dsimp only [yq, Lq, LinearMap.comp_apply]
    rw [map_zero, add_zero, map_add]
    abel
  have hE_polar : ∀ q h_vec : Fin (2 * m2) → F2,
      E (q + h_vec) + E q = E h_vec + E 0 + dotProduct ((K + diagPair cVec) *ᵥ h_vec) q := by
    intro q h_vec
    have hsum4 : E (q + h_vec) + E q + E h_vec + E 0 = dotProduct ((K + diagPair cVec) *ᵥ h_vec) q := by
      have hOut_aff : ∀ v : Fin (2 * m2) → F2,
          (if D0.eval (bitsOf n (yq v)) then (1 : F2) else 0) =
            (if bOut then (1 : F2) else 0) + dotProduct sOut (τ2 v) := by
        intro v
        rw [hOut_eval v]
        cases bOut <;> rcases zmod2_cases (dotProduct sOut (τ2 v)) with hv | hv <;> simp [hv] <;> decide
      have hOut4 : (if D0.eval (bitsOf n (yq (q + h_vec))) then (1 : F2) else 0) +
          (if D0.eval (bitsOf n (yq q)) then (1 : F2) else 0) +
          (if D0.eval (bitsOf n (yq h_vec)) then (1 : F2) else 0) +
          (if D0.eval (bitsOf n (yq 0)) then (1 : F2) else 0) = 0 := by
        simp_rw [hOut_aff, map_add, map_zero, dotProduct_add, dotProduct_zero, add_zero]
        rw [← add_assoc (if bOut then (1 : F2) else 0) (dotProduct sOut (τ2 q)) (dotProduct sOut (τ2 h_vec))]
        exact z2_polar_aff (if bOut then (1 : F2) else 0) (dotProduct sOut (τ2 q)) (dotProduct sOut (τ2 h_vec))
      have hTap_aff : ∀ (l : Fin n) (v : Fin (2 * m2) → F2),
          pos0 (yq v) l = (if bTap l then (1 : F2) else 0) + Ltap l v := by
        intro l v
        dsimp only [pos0, Ltap, LinearMap.comp_apply, dotLin, LinearMap.coe_mk, AddHom.coe_mk]
        rw [hTap_eval l v]
        cases bTap l <;> rcases zmod2_cases (dotProduct (sTap l) (τ2 v)) with hv | hv <;> simp [hv] <;> decide
      have hDot4 : dotProduct (pos0 (yq (q + h_vec))) (yq (q + h_vec)) +
          dotProduct (pos0 (yq q)) (yq q) +
          dotProduct (pos0 (yq h_vec)) (yq h_vec) +
          dotProduct (pos0 (yq 0)) (yq 0) =
          ∑ l : Fin n, (Ltap l q * Ly l h_vec + Ltap l h_vec * Ly l q) := by
        simp only [dotProduct, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hTap_aff l (q + h_vec), hTap_aff l q, hTap_aff l h_vec, hTap_aff l 0,
          hyq_shift (q + h_vec), hyq_shift q, hyq_shift h_vec]
        simp only [map_add, map_zero, add_zero, Pi.add_apply]
        change ((if bTap l then (1 : F2) else 0) + (Ltap l q + Ltap l h_vec)) * (yq 0 l + (Ly l q + Ly l h_vec)) +
          ((if bTap l then (1 : F2) else 0) + Ltap l q) * (yq 0 l + Ly l q) +
          ((if bTap l then (1 : F2) else 0) + Ltap l h_vec) * (yq 0 l + Ly l h_vec) +
          (if bTap l then (1 : F2) else 0) * yq 0 l = _
        rw [← add_assoc (if bTap l then (1 : F2) else 0) (Ltap l q) (Ltap l h_vec),
          ← add_assoc (yq 0 l) (Ly l q) (Ly l h_vec)]
        exact z2_polar_prod (if bTap l then (1 : F2) else 0) (yq 0 l) (Ltap l q) (Ltap l h_vec) (Ly l q) (Ly l h_vec)
      have he1_const : ∀ v : Fin (2 * m2) → F2, (e (yq v)).1 = (e a1).1 + B w := by
        intro v
        dsimp only [yq]
        rw [map_add, map_add, Prod.fst_add, Prod.fst_add, hσD_fst, hσS_fst, add_zero]
      have hG4 : g (yq (q + h_vec)) + g (yq q) + g (yq h_vec) + g (yq 0) =
          (∑ i : Fin m, dotProduct (A i) (e a1).1 * (Lu i q * Lv i h_vec + Lu i h_vec * Lv i q)) +
          (∑ t' : Fin m2, cVec t' *
            (q (pairIdx t' false) * h_vec (pairIdx t' true) + q (pairIdx t' true) * h_vec (pairIdx t' false))) := by
        dsimp only [g]
        simp_rw [he1_const]
        have hh4 : h ((e a1).1 + B w) + h ((e a1).1 + B w) + h ((e a1).1 + B w) + h ((e a1).1 + B w) = 0 := by
          have : ∀ z : F2, z + z + z + z = (z + z) + (z + z) := fun z => by ring
          rw [this, z2_add_self]
        have hsum_g4 : (h ((e a1).1 + B w) + ∑ i : Fin m, dotProduct (A i) ((e a1).1 + B w) * (e (yq (q + h_vec))).2.1 i * (e (yq (q + h_vec))).2.2.1 i) +
            (h ((e a1).1 + B w) + ∑ i : Fin m, dotProduct (A i) ((e a1).1 + B w) * (e (yq q)).2.1 i * (e (yq q)).2.2.1 i) +
            (h ((e a1).1 + B w) + ∑ i : Fin m, dotProduct (A i) ((e a1).1 + B w) * (e (yq h_vec)).2.1 i * (e (yq h_vec)).2.2.1 i) +
            (h ((e a1).1 + B w) + ∑ i : Fin m, dotProduct (A i) ((e a1).1 + B w) * (e (yq 0)).2.1 i * (e (yq 0)).2.2.1 i) =
            ∑ i : Fin m, dotProduct (A i) ((e a1).1 + B w) * (Lu i q * Lv i h_vec + Lu i h_vec * Lv i q) := by
          have hrearr : ∀ z1 z2 z3 z4 s1 s2 s3 s4 : F2,
              (z1 + s1) + (z2 + s2) + (z3 + s3) + (z4 + s4) = (z1 + z2 + z3 + z4) + (s1 + s2 + s3 + s4) := by
            intros; ring
          rw [hrearr, hh4, zero_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hpol : (e (yq (q + h_vec))).2.1 i * (e (yq (q + h_vec))).2.2.1 i +
              (e (yq q)).2.1 i * (e (yq q)).2.2.1 i +
              (e (yq h_vec)).2.1 i * (e (yq h_vec)).2.2.1 i +
              (e (yq 0)).2.1 i * (e (yq 0)).2.2.1 i =
              Lu i q * Lv i h_vec + Lu i h_vec * Lv i q := by
            rw [hyq_shift (q + h_vec), hyq_shift q, hyq_shift h_vec]
            simp only [map_add, Prod.snd_add, Prod.fst_add, Pi.add_apply]
            change ((e (yq 0)).2.1 i + (Lu i q + Lu i h_vec)) * ((e (yq 0)).2.2.1 i + (Lv i q + Lv i h_vec)) +
              ((e (yq 0)).2.1 i + Lu i q) * ((e (yq 0)).2.2.1 i + Lv i q) +
              ((e (yq 0)).2.1 i + Lu i h_vec) * ((e (yq 0)).2.2.1 i + Lv i h_vec) +
              (e (yq 0)).2.1 i * (e (yq 0)).2.2.1 i = _
            rw [← add_assoc ((e (yq 0)).2.1 i) (Lu i q) (Lu i h_vec),
              ← add_assoc ((e (yq 0)).2.2.1 i) (Lv i q) (Lv i h_vec)]
            exact z2_polar_prod ((e (yq 0)).2.1 i) ((e (yq 0)).2.2.1 i) (Lu i q) (Lu i h_vec) (Lv i q) (Lv i h_vec)
          calc dotProduct (A i) ((e a1).1 + B w) * (e (yq (q + h_vec))).2.1 i * (e (yq (q + h_vec))).2.2.1 i +
                dotProduct (A i) ((e a1).1 + B w) * (e (yq q)).2.1 i * (e (yq q)).2.2.1 i +
                dotProduct (A i) ((e a1).1 + B w) * (e (yq h_vec)).2.1 i * (e (yq h_vec)).2.2.1 i +
                dotProduct (A i) ((e a1).1 + B w) * (e (yq 0)).2.1 i * (e (yq 0)).2.2.1 i
              = dotProduct (A i) ((e a1).1 + B w) *
                  ((e (yq (q + h_vec))).2.1 i * (e (yq (q + h_vec))).2.2.1 i +
                   (e (yq q)).2.1 i * (e (yq q)).2.2.1 i +
                   (e (yq h_vec)).2.1 i * (e (yq h_vec)).2.2.1 i +
                   (e (yq 0)).2.1 i * (e (yq 0)).2.2.1 i) := by ring
            _ = dotProduct (A i) ((e a1).1 + B w) * (Lu i q * Lv i h_vec + Lu i h_vec * Lv i q) := by rw [hpol]
        rw [hsum_g4]
        simp_rw [dotProduct_add, add_mul, Finset.sum_add_distrib]
        congr 1
        have hBW_filt : (∑ i : Fin m, dotProduct (A i) (B w) * (Lu i q * Lv i h_vec + Lu i h_vec * Lv i q)) =
            ∑ t' : Fin m2, cVec t' *
              (q (pairIdx t' false) * h_vec (pairIdx t' true) + q (pairIdx t' true) * h_vec (pairIdx t' false)) := by
          let f_emb : Fin m2 → Fin m := fun t' => (eAct (eRem t').val).val
          have hf_inj : Function.Injective f_emb := fun t1 t2 h =>
            eRem.injective (Subtype.ext (eAct.injective (Subtype.ext h)))
          rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f_emb))]
          · rw [Finset.sum_image (fun a _ b _ h => hf_inj h)]
            refine Finset.sum_congr rfl fun t' _ => ?_
            have hLu : ∀ v, Lu (f_emb t') v = v (pairIdx t' false) := by
              intro v
              change (e (σD (τ2 v))).2.1 (eAct (eRem t').val).val = _
              rw [hσD_u, hτ2_coord]
            have hLv : ∀ v, Lv (f_emb t') v = v (pairIdx t' true) := by
              intro v
              change (e (σD (τ2 v))).2.2.1 (eAct (eRem t').val).val = _
              rw [hσD_v, hτ2_coord]
            rw [hLu q, hLv h_vec, hLu h_vec, hLv q]
            dsimp only [cVec, f_emb]; ring
          · intro i _ hi_not
            by_cases hiAct : i ∈ Act
            · set t := eAct.symm ⟨i, hiAct⟩
              have htJ0 : t ∈ J0 := by
                by_contra hntJ0
                apply hi_not
                refine Finset.mem_image.mpr ⟨eRem.symm ⟨t, hntJ0⟩, Finset.mem_univ _, ?_⟩
                dsimp only [f_emb]
                rw [Equiv.apply_symm_apply]
                exact congrArg Subtype.val (eAct.apply_symm_apply ⟨i, hiAct⟩)
              have hi_eq : i = (eAct t).val := (congrArg Subtype.val (eAct.apply_symm_apply ⟨i, hiAct⟩)).symm
              have hLu_eq : ∀ v, Lu i v = τ2 v (pairIdx t false) := by
                intro v; rw [hi_eq]; exact hσD_u (τ2 v) t
              have hLv_eq : ∀ v, Lv i v = τ2 v (pairIdx t true) := by
                intro v; rw [hi_eq]; exact hσD_v (τ2 v) t
              rcases hτ2_kill t htJ0 with hF | hT
              · rw [hLu_eq q, hLu_eq h_vec, hF q, hF h_vec]; ring
              · rw [hLv_eq q, hLv_eq h_vec, hT q, hT h_vec]; ring
            · have hAi0 : dotProduct (A i) (B w) = 0 := by
                by_contra hne
                exact hiAct (hAct ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨w, hne⟩⟩)
              rw [hAi0, zero_mul]
        exact hBW_filt
      have hE4 : E (q + h_vec) + E q + E h_vec + E 0 =
          ((if D0.eval (bitsOf n (yq (q + h_vec))) then (1 : F2) else 0) +
            (if D0.eval (bitsOf n (yq q)) then (1 : F2) else 0) +
            (if D0.eval (bitsOf n (yq h_vec)) then (1 : F2) else 0) +
            (if D0.eval (bitsOf n (yq 0)) then (1 : F2) else 0)) +
          (dotProduct (pos0 (yq (q + h_vec))) (yq (q + h_vec)) +
            dotProduct (pos0 (yq q)) (yq q) +
            dotProduct (pos0 (yq h_vec)) (yq h_vec) +
            dotProduct (pos0 (yq 0)) (yq 0)) +
          (g (yq (q + h_vec)) + g (yq q) + g (yq h_vec) + g (yq 0)) := by
        dsimp only [E]; ring
      rw [hE4, hOut4, zero_add, hDot4, hG4, Matrix.add_mulVec, add_dotProduct, diagPair_mulVec_dot]
      have hK_eq : dotProduct (K *ᵥ h_vec) q =
          (∑ l : Fin n, (Ltap l q * Ly l h_vec + Ltap l h_vec * Ly l q)) +
          (∑ i : Fin m, dotProduct (A i) (e a1).1 * (Lu i q * Lv i h_vec + Lu i h_vec * Lv i q)) := by
        have h1 : (∑ l : Fin n, (Ltap l q * Ly l h_vec + Ltap l h_vec * Ly l q)) =
            ∑ α : Fin (2 * m2), ∑ β : Fin (2 * m2),
              (∑ l : Fin n, (Ltap l (Pi.single α 1) * Ly l (Pi.single β 1) +
                Ltap l (Pi.single β 1) * Ly l (Pi.single α 1))) * h_vec β * q α := by
          simp_rw [bilinear_expand (Ltap _) (Ly _) q h_vec]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun β _ => ?_
          simp only [Finset.sum_mul]
        have h2 : (∑ i : Fin m, dotProduct (A i) (e a1).1 * (Lu i q * Lv i h_vec + Lu i h_vec * Lv i q)) =
            ∑ α : Fin (2 * m2), ∑ β : Fin (2 * m2),
              (∑ i : Fin m, dotProduct (A i) (e a1).1 *
                (Lu i (Pi.single α 1) * Lv i (Pi.single β 1) +
                 Lu i (Pi.single β 1) * Lv i (Pi.single α 1))) * h_vec β * q α := by
          simp_rw [bilinear_expand (Lu _) (Lv _) q h_vec, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun β _ => ?_
          simp only [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => by ring
        rw [h1, h2]
        have hsplit : ∀ f1 f2 : Fin (2 * m2) → Fin (2 * m2) → F2,
            dotProduct ((Matrix.of fun α β => f1 α β + f2 α β) *ᵥ h_vec) q =
              (∑ α, ∑ β, f1 α β * h_vec β * q α) + (∑ α, ∑ β, f2 α β * h_vec β * q α) := by
          intro f1 f2
          simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.sum_mul, add_mul, Finset.sum_add_distrib]
        exact hsplit _ _
      rw [hK_eq]; ring
    have hstep := congrArg (· + (E h_vec + E 0)) hsum4
    have hlhs : E (q + h_vec) + E q + E h_vec + E 0 + (E h_vec + E 0) = E (q + h_vec) + E q := by
      have : E (q + h_vec) + E q + E h_vec + E 0 + (E h_vec + E 0) =
          E (q + h_vec) + E q + (E h_vec + E h_vec) + (E 0 + E 0) := by ring
      rw [this, z2_add_self, z2_add_self, add_zero, add_zero]
    rw [hlhs] at hstep
    rw [hstep, add_comm]
  have hMd : ∀ α, (K + diagPair cVec) α α = 0 := fun α => by
    simp only [K, Matrix.add_apply, polarMatrix_diag, diagPair_diag, add_zero]
  have hMs : ∀ α β, (K + diagPair cVec) α β = (K + diagPair cVec) β α := fun α β => by
    simp only [K, Matrix.add_apply, polarMatrix_symm, diagPair_symm]
  exact gauss_sum_sq_bound (K + diagPair cVec) hMd hMs E hE_polar

lemma pow2_combine_eq (k m r m1 jcard rstar w : ℕ)
    (hm1 : m1 ≤ m) (h2m1 : 2 * m1 ≤ 2 * m + r) (hj : jcard ≤ m1)
    (hr : rstar ≤ 2 * jcard) (hw : w ≤ m1 - jcard) :
    2 ^ (k + m) * (2 ^ (k + 2 * m + r) * (2 ^ ((2 * m + r) - 2 * m1) *
      (2 ^ rstar * (2 ^ (2 * jcard - rstar) * (2 ^ (m1 - jcard) * 2 ^ ((m1 - jcard) - w)))))) =
    2 ^ (2 * (k + 2 * m + r)) * 2 ^ (m - w) := by
  simp only [← pow_add]
  congr 1; omega

lemma conjunct2_forward (k m r : ℕ)
    (e : (Fin (k + 2 * m + r) → F2) ≃ₗ[F2]
      (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2))))
    (A : Fin m → (Fin k → F2)) (h : (Fin k → F2) → F2)
    (s T : ℕ) (hs : 2 * m + r ≤ s)
    (C : Circuit) (hleg : legalGates (2 * (k + 2 * m + r)) C.gates)
    (hcost : costGates C.gates ≤ s)
    (hT : T ≤ (∑ x : Fin (k + 2 * m + r) → F2, ∑ y : Fin (k + 2 * m + r) → F2,
      if C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y) =
        decide (dotProduct x y + (h (e y).1 + ∑ i : Fin m,
          dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i) = 1)
      then (1 : ℤ) else -1).natAbs) :
    let n := k + 2 * m + r
    let base := 2 * m + r
    let weight := fun (J : Finset (Fin m)) (s : Fin k → F2) =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ dotProduct (A i) s ≠ 0)).card
    let mass := fun (j : ℕ) (B : (Fin j → F2) →ₗ[F2] (Fin k → F2)) (J : Finset (Fin m)) =>
      ∑ u : Fin j → F2, 2 ^ (m - weight J (B u))
    ∃ (j : ℕ) (B : (Fin j → F2) →ₗ[F2] (Fin k → F2)) (J : Finset (Fin m)),
      Function.Injective B ∧ base + j + J.card ≤ s ∧ 2 ^ (k + m) * T ≤ 2 ^ (2 * n) * mass j B J := by
  intro n base weight mass
  let g : (Fin n → F2) → F2 := fun y =>
    h (e y).1 + ∑ i : Fin m, dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
  rcases forward_decomp_bounds n s g C hleg hcost with
    ⟨N, r_b, W_b, a_b, D_b, tap_b, hNpos, hmeta, hsum_b, hB_le, hraw⟩
  set pos_b := fun (i : Fin N) (y : Fin n → F2) (l : Fin n) =>
    if ((D_b i).wires (bitsOf n y)).getD (tap_b i l) false then (1 : F2) else 0
  set Bval := fun i : Fin N =>
    (∑ y : Fin n → F2, if y - a_b i ∈ W_b i then
      signBool (Bool.xor ((D_b i).eval (bitsOf n y)) (decide (dotProduct (pos_b i y) y = 1))) *
        signBool (decide (g y = 1))
    else 0).natAbs
  rcases weighted_avg_prod_exists hNpos r_b Bval T hsum_b (le_trans hT hraw) with ⟨i0, hi0⟩
  have hm0 := hmeta i0
  set r0 := r_b i0
  set W0 := W_b i0
  set a0 := a_b i0
  set D0 := D_b i0
  set tap0 := tap_b i0
  set c0 := costGates D0.gates
  by_cases hr0_le : r0 ≤ base
  · refine ⟨0, 0, ∅, fun u v _ => Subsingleton.elim u v, by simp; omega, ?_⟩
    have hTle : T ≤ 2 ^ (n + base) := by
      have h1 : Bval i0 ≤ 2 ^ base := le_trans (hB_le i0) (Nat.pow_le_pow_right (by omega) hr0_le)
      calc T ≤ 2 ^ n * Bval i0 := hi0
        _ ≤ 2 ^ n * 2 ^ base := Nat.mul_le_mul_left _ h1
        _ = 2 ^ (n + base) := (pow_add 2 n base).symm
    have hmass0 : mass 0 0 ∅ = 2 ^ m := by
      dsimp only [mass, weight]
      have hwt0 : ∀ u : Fin 0 → F2,
          ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ (∅ : Finset (Fin m)) ∧ dotProduct (A i) ((0 : (Fin 0 → F2) →ₗ[F2] (Fin k → F2)) u) ≠ 0)).card = 0 := by
        intro _; simp
      simp_rw [hwt0, Nat.sub_zero]
      simp
    rw [hmass0]
    calc 2 ^ (k + m) * T ≤ 2 ^ (k + m) * 2 ^ (n + base) := Nat.mul_le_mul_left _ hTle
      _ = 2 ^ (2 * n) * 2 ^ m := by
        rw [← pow_add, ← pow_add]; congr 1; omega
  · set j0 := r0 - base
    have hr0_eq : r0 = base + j0 := by omega
    have hdimW0e : 2 * m + r + j0 ≤ Module.finrank F2 (W0.map e.toLinearMap) := by
      rw [LinearEquiv.finrank_map_eq e W0, hm0.1]; omega
    rcases selector_917 k m r j0 A (W0.map e.toLinearMap) hdimW0e with ⟨B, hB_inj, hB_lift, hB_free⟩
    let Act : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => ∃ w : Fin j0 → F2, dotProduct (A i) (B w) ≠ 0)
    let m1 := Act.card
    let eAct : Fin m1 ≃ Act := (Fintype.equivFinOfCardEq (Fintype.card_coe Act)).symm
    have hm1_le_m : m1 ≤ m := by
      have := Finset.card_le_univ Act; simpa using this
    have hliftS : ∀ t : Fin j0, ∃ v ∈ W0, (e v).1 = B (Pi.single t 1) := by
      intro t
      rcases hB_lift (Pi.single t 1) with ⟨w, hw, hweq⟩
      rcases Submodule.mem_map.mp hw with ⟨v, hv, rfl⟩
      exact ⟨v, hv, hweq⟩
    choose vS hvS_mem hvS_fst using hliftS
    let σS : (Fin j0 → F2) →ₗ[F2] (Fin n → F2) :=
      { toFun := fun w => ∑ t : Fin j0, w t • vS t
        map_add' := fun w1 w2 => by simp [add_smul, Finset.sum_add_distrib]
        map_smul' := fun c w => by simp [Finset.smul_sum, smul_smul] }
    have hσS_mem : ∀ w, σS w ∈ W0 := fun w => by
      show ∑ t : Fin j0, w t • vS t ∈ W0
      exact Submodule.sum_mem W0 fun t _ => W0.smul_mem _ (hvS_mem t)
    have hσS_fst : ∀ w, (e (σS w)).1 = B w := by
      intro w
      dsimp only [σS, LinearMap.coe_mk, AddHom.coe_mk]
      rw [map_sum, Prod.fst_sum]
      conv_rhs => rw [vec_eq_sum_single w, map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_smul, Prod.smul_fst, hvS_fst t, map_smul]
    have hliftU : ∀ t : Fin m1, ∃ v ∈ W0, (e v).1 = 0 ∧
        ∀ t' : Fin m1, (e v).2.1 (eAct t').val = (if t' = t then 1 else 0) ∧ (e v).2.2.1 (eAct t').val = 0 := by
      intro t
      rcases hB_free (Pi.single (eAct t).val 1) 0 with ⟨w, hw, hw1, hw2⟩
      rcases Submodule.mem_map.mp hw with ⟨v, hv, rfl⟩
      refine ⟨v, hv, hw1, fun t' => ?_⟩
      have hact' : ∃ a, dotProduct (A (eAct t').val) (B a) ≠ 0 := (Finset.mem_filter.mp (eAct t').property).2
      rcases hw2 (eAct t').val hact' with ⟨hu, hv'⟩
      refine ⟨?_, hv'⟩
      change (e.toLinearMap v).2.1 (eAct t').val = _
      rw [hu, Pi.single_apply]
      by_cases heq : t' = t
      · subst heq; simp
      · have hne : (eAct t').val ≠ (eAct t).val := fun h => heq (eAct.injective (Subtype.ext h))
        simp [heq, hne]
    choose vU hvU_mem hvU_fst hvU_coord using hliftU
    have hliftV : ∀ t : Fin m1, ∃ v ∈ W0, (e v).1 = 0 ∧
        ∀ t' : Fin m1, (e v).2.1 (eAct t').val = 0 ∧ (e v).2.2.1 (eAct t').val = (if t' = t then 1 else 0) := by
      intro t
      rcases hB_free 0 (Pi.single (eAct t).val 1) with ⟨w, hw, hw1, hw2⟩
      rcases Submodule.mem_map.mp hw with ⟨v, hv, rfl⟩
      refine ⟨v, hv, hw1, fun t' => ?_⟩
      have hact' : ∃ a, dotProduct (A (eAct t').val) (B a) ≠ 0 := (Finset.mem_filter.mp (eAct t').property).2
      rcases hw2 (eAct t').val hact' with ⟨hu, hv'⟩
      refine ⟨hu, ?_⟩
      change (e.toLinearMap v).2.2.1 (eAct t').val = _
      rw [hv', Pi.single_apply]
      by_cases heq : t' = t
      · subst heq; simp
      · have hne : (eAct t').val ≠ (eAct t).val := fun h => heq (eAct.injective (Subtype.ext h))
        simp [heq, hne]
    choose vV hvV_mem hvV_fst hvV_coord using hliftV
    let σD : (Fin (2 * m1) → F2) →ₗ[F2] (Fin n → F2) :=
      { toFun := fun p => ∑ t : Fin m1, (p (pairIdx t false) • vU t + p (pairIdx t true) • vV t)
        map_add' := fun p1 p2 => by
          simp only [Pi.add_apply, add_smul, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun t _ => by abel
        map_smul' := fun c p => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_add, smul_smul] }
    have hσD_mem : ∀ p, σD p ∈ W0 := fun p => by
      show ∑ t : Fin m1, (p (pairIdx t false) • vU t + p (pairIdx t true) • vV t) ∈ W0
      exact Submodule.sum_mem W0 fun t _ => W0.add_mem (W0.smul_mem _ (hvU_mem t)) (W0.smul_mem _ (hvV_mem t))
    have hσD_fst : ∀ p, (e (σD p)).1 = 0 := by
      intro p
      dsimp only [σD, LinearMap.coe_mk, AddHom.coe_mk]
      rw [map_sum, Prod.fst_sum]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [map_add, Prod.fst_add, map_smul, map_smul, Prod.smul_fst, Prod.smul_fst, hvU_fst t, hvV_fst t]
      simp
    have hσD_u : ∀ p (t : Fin m1), (e (σD p)).2.1 (eAct t).val = p (pairIdx t false) := by
      intro p t
      dsimp only [σD, LinearMap.coe_mk, AddHom.coe_mk]
      rw [map_sum, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
      have hterm : ∀ t' : Fin m1,
          (e (p (pairIdx t' false) • vU t' + p (pairIdx t' true) • vV t')).2.1 (eAct t).val =
            if t = t' then p (pairIdx t false) else 0 := by
        intro t'
        rw [map_add, map_smul, map_smul]
        simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, Prod.smul_snd, Prod.smul_fst,
          Pi.smul_apply, smul_eq_mul, (hvU_coord t' t).1, (hvV_coord t' t).1, mul_zero, add_zero]
        by_cases heq : t = t'
        · subst heq; simp
        · simp [heq]
      simp_rw [hterm]
      simp
    have hσD_v : ∀ p (t : Fin m1), (e (σD p)).2.2.1 (eAct t).val = p (pairIdx t true) := by
      intro p t
      dsimp only [σD, LinearMap.coe_mk, AddHom.coe_mk]
      rw [map_sum, Prod.snd_sum, Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
      have hterm : ∀ t' : Fin m1,
          (e (p (pairIdx t' false) • vU t' + p (pairIdx t' true) • vV t')).2.2.1 (eAct t).val =
            if t = t' then p (pairIdx t true) else 0 := by
        intro t'
        rw [map_add, map_smul, map_smul]
        simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, Prod.smul_snd, Prod.smul_fst,
          Pi.smul_apply, smul_eq_mul, (hvU_coord t' t).2, (hvV_coord t' t).2, mul_zero, zero_add]
        by_cases heq : t = t'
        · subst heq; simp
        · simp [heq]
      simp_rw [hterm]
      simp
    let σSD : (Fin (2 * m1) → F2) × (Fin j0 → F2) →ₗ[F2] W0 :=
      { toFun := fun pw => ⟨σD pw.1 + σS pw.2, W0.add_mem (hσD_mem pw.1) (hσS_mem pw.2)⟩
        map_add' := fun a b => Subtype.ext (by simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add]; abel)
        map_smul' := fun c a => Subtype.ext (by simp only [Prod.smul_fst, Prod.smul_snd, map_smul, SetLike.val_smul, RingHom.id_apply, smul_add]) }
    have hσSD_inj : Function.Injective σSD := by
      refine (injective_iff_map_eq_zero σSD).mpr fun ⟨p, w⟩ hpw => ?_
      have hv0 : σD p + σS w = 0 := congrArg Subtype.val hpw
      have hBw0 : B w = 0 := by
        have h1 := congrArg (fun x => (e x).1) hv0
        rw [map_add, Prod.fst_add, hσD_fst p, hσS_fst w, zero_add, map_zero, Prod.fst_zero] at h1
        exact h1
      have hw0 : w = 0 := (injective_iff_map_eq_zero B).mp hB_inj w hBw0
      subst hw0
      rw [map_zero, add_zero] at hv0
      have hp0 : p = 0 := by
        funext idx
        have hidx : idx = pairIdx ((pairEquiv m1).symm idx).1 ((pairEquiv m1).symm idx).2 :=
          ((pairEquiv m1).apply_symm_apply idx).symm
        rw [hidx]
        cases hb : ((pairEquiv m1).symm idx).2
        · have hu := hσD_u p ((pairEquiv m1).symm idx).1
          rw [hv0, map_zero] at hu; exact hu.symm
        · have hv := hσD_v p ((pairEquiv m1).symm idx).1
          rw [hv0, map_zero] at hv; exact hv.symm
      exact Prod.ext hp0 rfl
    let W_SD : Submodule F2 W0 := LinearMap.range σSD
    obtain ⟨W_rem, hcompl_W⟩ := Submodule.exists_isCompl W_SD
    have hdim_SD : Module.finrank F2 W_SD = 2 * m1 + j0 := by
      rw [(LinearEquiv.ofInjective σSD hσSD_inj).finrank_eq.symm, Module.finrank_prod,
        Module.finrank_fin_fun, Module.finrank_fin_fun]
    have hdim_rem_add : Module.finrank F2 W_rem + (2 * m1 + j0) = r0 := by
      have h1 := Submodule.finrank_add_eq_of_isCompl hcompl_W.symm
      rw [hdim_SD, hm0.1] at h1
      exact h1
    have h2m1_le_base : 2 * m1 ≤ base := by omega
    have hdim_rem : Module.finrank F2 W_rem = base - 2 * m1 := by omega
    let πR := W_rem.projectionOnto W_SD hcompl_W.symm
    let πS := W_SD.projectionOnto W_rem hcompl_W
    let eSD := LinearEquiv.ofInjective σSD hσSD_inj
    let eW0_split : W_rem × ((Fin j0 → F2) × (Fin (2 * m1) → F2)) ≃ W0 :=
      { toFun := fun q => q.1.val + σSD (q.2.2, q.2.1)
        invFun := fun v => (πR v, ((eSD.symm (πS v)).2, (eSD.symm (πS v)).1))
        left_inv := fun q => by
          rcases q with ⟨wr, ⟨w, p⟩⟩
          dsimp only
          have hmemS : σSD (p, w) ∈ W_SD := ⟨(p, w), rfl⟩
          have hπR : πR (wr.val + σSD (p, w)) = wr := by
            dsimp only [πR]
            rw [map_add, Submodule.projectionOnto_apply_left hcompl_W.symm wr,
              Submodule.projectionOnto_apply_right hcompl_W.symm ⟨σSD (p, w), hmemS⟩, add_zero]
          have hπS : πS (wr.val + σSD (p, w)) = ⟨σSD (p, w), hmemS⟩ := by
            dsimp only [πS]
            rw [map_add, Submodule.projectionOnto_apply_right hcompl_W wr,
              Submodule.projectionOnto_apply_left hcompl_W ⟨σSD (p, w), hmemS⟩, zero_add]
          apply Prod.ext
          · exact hπR
          · dsimp only
            rw [hπS]
            have heq : (⟨σSD (p, w), hmemS⟩ : W_SD) = eSD (p, w) := rfl
            rw [heq, LinearEquiv.symm_apply_apply]
        right_inv := fun v => by
          dsimp only
          have h1 : σSD ((eSD.symm (πS v)).1, (eSD.symm (πS v)).2) = (πS v).val :=
            congrArg Subtype.val (eSD.apply_symm_apply (πS v))
          rw [h1]
          have hv : v ∈ W_rem ⊔ W_SD := by rw [hcompl_W.symm.sup_eq_top]; trivial
          rcases Submodule.mem_sup.mp hv with ⟨a, ha, b, hb, rfl⟩
          dsimp only [πR, πS]
          rw [map_add, Submodule.projectionOnto_apply_left hcompl_W.symm ⟨a, ha⟩,
            Submodule.projectionOnto_apply_right hcompl_W.symm ⟨b, hb⟩, add_zero,
            map_add, Submodule.projectionOnto_apply_right hcompl_W ⟨a, ha⟩,
            Submodule.projectionOnto_apply_left hcompl_W ⟨b, hb⟩, zero_add] }
    have hcard_rem : Fintype.card W_rem = 2 ^ (base - 2 * m1) := by
      have hc := Fintype.card_congr eW0_split
      rw [Fintype.card_prod, Fintype.card_prod, card_submodule_zmod2, hm0.1] at hc
      have hcard_p : Fintype.card (Fin j0 → F2) * Fintype.card (Fin (2 * m1) → F2) = 2 ^ (j0 + 2 * m1) := by
        simp [ZMod.card, ← pow_add]
      rw [hcard_p] at hc
      have hpow : 2 ^ r0 = 2 ^ (base - 2 * m1) * 2 ^ (j0 + 2 * m1) := by
        rw [← pow_add]; congr 1; omega
      rw [hpow] at hc
      exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by omega)) hc
    let termY : (Fin n → F2) → ℤ := fun y =>
      signBool (Bool.xor (D0.eval (bitsOf n y)) (decide (dotProduct (pos_b i0 y) y = 1))) *
        signBool (decide (g y = 1))
    have hBval_rew : Bval i0 =
        (∑ wr : W_rem, ∑ w : Fin j0 → F2, ∑ p : Fin (2 * m1) → F2,
          termY (a0 + wr.val.val + σD p + σS w)).natAbs := by
      dsimp only [Bval, termY]
      congr 1
      have hsub : (∑ y ∈ Finset.univ.filter (fun y : Fin n → F2 => y - a0 ∈ W0), termY y) =
          ∑ v : W0, termY (a0 + v.val) := by
        rw [← Finset.sum_coe_sort (Finset.univ.filter (fun y : Fin n → F2 => y - a0 ∈ W0))]
        let eFilt : W0 ≃ (Finset.univ.filter (fun y : Fin n → F2 => y - a0 ∈ W0)) :=
          { toFun := fun v => ⟨a0 + v.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩
            invFun := fun y => ⟨y.val - a0, (Finset.mem_filter.mp y.property).2⟩
            left_inv := fun v => Subtype.ext (by show a0 + v.val - a0 = v.val; abel)
            right_inv := fun y => Subtype.ext (by show a0 + (y.val - a0) = y.val; abel) }
        exact (Equiv.sum_comp eFilt (fun y => termY y.val)).symm
      rw [← Finset.sum_filter, hsub, ← Equiv.sum_comp eW0_split, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun wr _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun p _ => ?_
      have heq_y : a0 + (eW0_split (wr, (w, p))).val = a0 + wr.val.val + σD p + σS w := by
        show a0 + (wr.val.val + (σD p + σS w)) = a0 + wr.val.val + σD p + σS w
        abel
      rw [heq_y]
    have hmax_wr : ∃ wr0 : W_rem,
        Bval i0 ≤ 2 ^ (base - 2 * m1) *
          (∑ w : Fin j0 → F2, ∑ p : Fin (2 * m1) → F2,
            termY (a0 + wr0.val.val + σD p + σS w)).natAbs := by
      have hne : (Finset.univ : Finset W_rem).Nonempty := ⟨0, Finset.mem_univ _⟩
      obtain ⟨wr0, _, hwr0_max⟩ := Finset.exists_max_image Finset.univ
        (fun wr : W_rem => (∑ w : Fin j0 → F2, ∑ p : Fin (2 * m1) → F2,
          termY (a0 + wr.val.val + σD p + σS w)).natAbs) hne
      refine ⟨wr0, ?_⟩
      rw [hBval_rew]
      calc (∑ wr : W_rem, ∑ w : Fin j0 → F2, ∑ p : Fin (2 * m1) → F2,
              termY (a0 + wr.val.val + σD p + σS w)).natAbs
          ≤ ∑ wr : W_rem, (∑ w : Fin j0 → F2, ∑ p : Fin (2 * m1) → F2,
              termY (a0 + wr.val.val + σD p + σS w)).natAbs := natAbs_sum_le_sum_natAbs _ _
        _ ≤ ∑ _wr : W_rem, (∑ w : Fin j0 → F2, ∑ p : Fin (2 * m1) → F2,
              termY (a0 + wr0.val.val + σD p + σS w)).natAbs :=
            Finset.sum_le_sum fun wr _ => hwr0_max wr (Finset.mem_univ wr)
        _ = 2 ^ (base - 2 * m1) * (∑ w : Fin j0 → F2, ∑ p : Fin (2 * m1) → F2,
              termY (a0 + wr0.val.val + σD p + σS w)).natAbs := by
            rw [Finset.sum_const, Finset.card_univ, hcard_rem, smul_eq_mul]
    rcases hmax_wr with ⟨wr0, hwr0_le⟩
    set a1 := a0 + wr0.val.val
    let yPW : (Fin (2 * m1) → F2) → (Fin j0 → F2) → (Fin n → F2) := fun p w => a1 + σD p + σS w
    have hcoordY : ∀ l : Fin n, ∃ cY : Fin (2 * m1 + j0) → F2, ∀ p w,
        yPW p w l = dotProduct cY (concatVec2 p w) + a1 l := by
      intro l
      obtain ⟨cD, hcD⟩ := linear_coord_dot ((LinearMap.proj l).comp σD)
      obtain ⟨cS, hcS⟩ := linear_coord_dot ((LinearMap.proj l).comp σS)
      refine ⟨concatVec2 cD cS, fun p w => ?_⟩
      rw [dotProduct_concatVec2]
      have h1 : σD p l = dotProduct cD p := hcD p
      have h2 : σS w l = dotProduct cS w := hcS w
      dsimp only [yPW]
      simp only [Pi.add_apply, h1, h2]
      ring
    choose cY hcY using hcoordY
    have hnil_pre : legalGates (2 * m1 + j0) [] := ⟨fun j hj => by simp at hj, fun h hh => by simp at hh⟩
    rcases appendAffinesLoop_spec (2 * m1 + j0) n cY a1 n (le_refl n) [] (fun _ => 0) hnil_pre with
      ⟨_, _, hpre_leg, hpre_cost, hpre_lt, hpre_sem⟩
    set resPre := appendAffinesLoop (2 * m1 + j0) n cY a1 n (le_refl n) [] (fun _ => 0)
    have hpre_cost0 : costGates resPre.1 = 0 := by
      have : costGates ([] : List Gate) = 0 := by simp [costGates]
      dsimp only [resPre] at hpre_cost ⊢; omega
    set offset := 2 * m1 + j0 + resPre.1.length
    have hremap := remap_gates_spec (2 * m1 + j0) n resPre.1 D0.gates resPre.2
      hpre_leg hpre_cost0 (fun l => hpre_lt l l.isLt) hm0.2.2.1
    set gs_comb := resPre.1 ++ D0.gates.map (remapGate n offset resPre.2)
    rcases build_branch_list (2 * m1) j0 gs_comb hremap.1 with ⟨L, hLpos, hLval, hLpart⟩
    let hpart_L : ∀ w : Fin j0 → F2, (Σ ℓ : Fin L.length, (L.get ℓ).U) ≃ (Fin (2 * m1) → F2) := fun w =>
      let idxOf : (Fin (2 * m1) → F2) → Fin L.length := fun p => (hLpart w p).choose
      have hidx_mem : ∀ p, p - (L.get (idxOf p)).pos w ∈ (L.get (idxOf p)).U := fun p => (hLpart w p).choose_spec.1
      have hidx_uniq : ∀ p ℓ, p - (L.get ℓ).pos w ∈ (L.get ℓ).U → ℓ = idxOf p := fun p ℓ hℓ => (hLpart w p).choose_spec.2 ℓ hℓ
      { toFun := fun q => (L.get q.1).pos w + q.2.val
        invFun := fun p => ⟨idxOf p, ⟨p - (L.get (idxOf p)).pos w, hidx_mem p⟩⟩
        left_inv := fun ⟨ℓ, ⟨u, hu⟩⟩ => by
          have hmem : (L.get ℓ).pos w + u - (L.get ℓ).pos w ∈ (L.get ℓ).U := by simpa using hu
          have hℓ : idxOf ((L.get ℓ).pos w + u) = ℓ := (hidx_uniq _ ℓ hmem).symm
          dsimp only
          generalize hidx_mem ((L.get ℓ).pos w + u) = hjm
          revert hjm
          generalize idxOf ((L.get ℓ).pos w + u) = ℓ' at hℓ ⊢
          subst hℓ
          intro _
          congr 1; apply Subtype.ext; simp
        right_inv := fun p => by show (L.get (idxOf p)).pos w + (p - (L.get (idxOf p)).pos w) = p; abel }
    have hsum_L : (∑ ℓ : Fin L.length, 2 ^ (2 * m1 - (L.get ℓ).r)) = 2 ^ (2 * m1) := by
      have hcard_sig : Fintype.card (Σ ℓ : Fin L.length, (L.get ℓ).U) =
          ∑ ℓ : Fin L.length, 2 ^ (2 * m1 - (L.get ℓ).r) := by
        rw [Fintype.card_sigma]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        have hBi := hLval (L.get ℓ) (List.get_mem L ℓ)
        rw [card_submodule_zmod2]
        congr 1; have := hBi.1; omega
      have hcard_P : Fintype.card (Fin (2 * m1) → F2) = 2 ^ (2 * m1) := by simp [ZMod.card]
      rw [← hcard_sig, ← hcard_P]
      exact Fintype.card_congr (hpart_L 0)
    have hsum_split_L : (∑ w : Fin j0 → F2, ∑ p : Fin (2 * m1) → F2, termY (yPW p w)).natAbs ≤
        ∑ ℓ : Fin L.length, ∑ w : Fin j0 → F2,
          (∑ u : (L.get ℓ).U, termY (yPW ((L.get ℓ).pos w + u.val) w)).natAbs := by
      have heq_sum : (∑ w : Fin j0 → F2, ∑ p : Fin (2 * m1) → F2, termY (yPW p w)) =
          ∑ ℓ : Fin L.length, ∑ w : Fin j0 → F2,
            ∑ u : (L.get ℓ).U, termY (yPW ((L.get ℓ).pos w + u.val) w) := by
        have hinner : ∀ w : Fin j0 → F2,
            (∑ p : Fin (2 * m1) → F2, termY (yPW p w)) =
            ∑ ℓ : Fin L.length, ∑ u : (L.get ℓ).U, termY (yPW ((L.get ℓ).pos w + u.val) w) := by
          intro w
          rw [← Equiv.sum_comp (hpart_L w), Fintype.sum_sigma]
          rfl
        simp_rw [hinner]
        rw [Finset.sum_comm]
      rw [heq_sum]
      refine le_trans (natAbs_sum_le_sum_natAbs _ _) (Finset.sum_le_sum fun ℓ _ => natAbs_sum_le_sum_natAbs _ _)
    rcases weighted_avg_exists hLpos (fun ℓ => (L.get ℓ).r)
        (fun ℓ => ∑ w : Fin j0 → F2, (∑ u : (L.get ℓ).U, termY (yPW ((L.get ℓ).pos w + u.val) w)).natAbs)
        (∑ w : Fin j0 → F2, ∑ p : Fin (2 * m1) → F2, termY (yPW p w)).natAbs
        (fun ℓ => by have := (hLval (L.get ℓ) (List.get_mem L ℓ)).1; omega)
        hsum_L hsum_split_L with ⟨ℓ0, hℓ0_le⟩
    set B_L := L.get ℓ0
    have hBL_val : ValidBranch gs_comb B_L := hLval B_L (List.get_mem L ℓ0)
    set U_star := B_L.U
    set r_star := B_L.r
    have hr_star_le_c0 : r_star ≤ c0 := by
      have h1 := hBL_val.2.2.1
      rw [hremap.2.1] at h1
      dsimp only [r_star, c0]; omega
    have hcod_U : 2 * m1 - Module.finrank F2 U_star ≤ r_star := by
      have := hBL_val.1; dsimp only [U_star, r_star]; omega
    rcases pair_section m1 r_star U_star hcod_U with ⟨J0, τ, hJ0_card, hτ_mem, hτ_coord, hτ_kill⟩
    have hJ0_le_m1 : J0.card ≤ m1 := by
      have := Finset.card_le_univ J0; simpa using this
    set m2 := m1 - J0.card
    have hcard_rem_t : Fintype.card {t : Fin m1 // t ∉ J0} = m2 := by
      rw [Fintype.card_subtype]
      have hf : Finset.univ.filter (fun t : Fin m1 => t ∉ J0) = Finset.univ \ J0 := by
        ext t; simp
      rw [hf, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    let eRem : Fin m2 ≃ {t : Fin m1 // t ∉ J0} := (Fintype.equivFinOfCardEq hcard_rem_t).symm
    let τ2 : (Fin (2 * m2) → F2) →ₗ[F2] (Fin (2 * m1) → F2) :=
      { toFun := fun q => τ (fun tb => q (pairIdx (eRem.symm tb.1) tb.2))
        map_add' := fun q1 q2 => by
          rw [← map_add]; congr 1
        map_smul' := fun c q => by
          rw [← map_smul]; congr 1 }
    have hτ2_mem : ∀ q, τ2 q ∈ U_star := fun q => hτ_mem _
    have hτ2_coord : ∀ (t' : Fin m2) (b : Bool) (q : Fin (2 * m2) → F2),
        τ2 q (pairIdx (eRem t').val b) = q (pairIdx t' b) := by
      intro t' b q
      dsimp only [τ2, LinearMap.coe_mk, AddHom.coe_mk]
      rw [hτ_coord (eRem t').val (eRem t').property b]
      simp [Equiv.symm_apply_apply]
    have hτ2_kill : ∀ t ∈ J0, (∀ q, τ2 q (pairIdx t false) = 0) ∨ (∀ q, τ2 q (pairIdx t true) = 0) := by
      intro t ht
      rcases hτ_kill t ht with hF | hT
      · exact Or.inl fun q => hF _
      · exact Or.inr fun q => hT _
    have hτ2_inj : Function.Injective τ2 := by
      refine (injective_iff_map_eq_zero τ2).mpr fun q hq => ?_
      funext idx
      have hidx : idx = pairIdx ((pairEquiv m2).symm idx).1 ((pairEquiv m2).symm idx).2 :=
        ((pairEquiv m2).apply_symm_apply idx).symm
      rw [hidx, ← hτ2_coord ((pairEquiv m2).symm idx).1 ((pairEquiv m2).symm idx).2 q, hq]
      rfl
    let τ2_sub : (Fin (2 * m2) → F2) →ₗ[F2] U_star := τ2.codRestrict U_star hτ2_mem
    have hτ2_sub_inj : Function.Injective τ2_sub := fun q1 q2 h => hτ2_inj (congrArg Subtype.val h)
    let Rτ : Submodule F2 U_star := LinearMap.range τ2_sub
    obtain ⟨U_ker, hcompl_U⟩ := Submodule.exists_isCompl Rτ
    have hdim_Rτ : Module.finrank F2 Rτ = 2 * m2 := by
      rw [(LinearEquiv.ofInjective τ2_sub hτ2_sub_inj).finrank_eq.symm, Module.finrank_fin_fun]
    have hdim_Uker_add : Module.finrank F2 U_ker + 2 * m2 = Module.finrank F2 U_star := by
      have h1 := Submodule.finrank_add_eq_of_isCompl hcompl_U.symm
      rw [hdim_Rτ] at h1; exact h1
    have hr_star_le_2J0 : r_star ≤ 2 * J0.card := by
      have h1 := hBL_val.1
      dsimp only [U_star, r_star, m2] at hdim_Uker_add h1 ⊢
      omega
    have hdim_Uker : Module.finrank F2 U_ker = 2 * J0.card - r_star := by
      have h1 := hBL_val.1
      dsimp only [U_star, r_star, m2] at hdim_Uker_add h1 ⊢
      omega
    let πK := U_ker.projectionOnto Rτ hcompl_U.symm
    let πR := Rτ.projectionOnto U_ker hcompl_U
    let eR := LinearEquiv.ofInjective τ2_sub hτ2_sub_inj
    let eU_split : U_ker × (Fin (2 * m2) → F2) ≃ U_star :=
      { toFun := fun p => p.1.val + τ2_sub p.2
        invFun := fun u => (πK u, eR.symm (πR u))
        left_inv := fun p => by
          rcases p with ⟨u0, q⟩
          dsimp only
          have hmemR : τ2_sub q ∈ Rτ := ⟨q, rfl⟩
          apply Prod.ext
          · dsimp only [πK]
            rw [map_add, Submodule.projectionOnto_apply_left hcompl_U.symm u0,
              Submodule.projectionOnto_apply_right hcompl_U.symm ⟨τ2_sub q, hmemR⟩, add_zero]
          · dsimp only [πR]
            rw [map_add, Submodule.projectionOnto_apply_right hcompl_U u0,
              Submodule.projectionOnto_apply_left hcompl_U ⟨τ2_sub q, hmemR⟩, zero_add]
            have heq : (⟨τ2_sub q, hmemR⟩ : Rτ) = eR q := rfl
            rw [heq, LinearEquiv.symm_apply_apply]
        right_inv := fun u => by
          dsimp only
          have h1 : τ2_sub (eR.symm (πR u)) = (πR u).val :=
            congrArg Subtype.val (eR.apply_symm_apply (πR u))
          rw [h1]
          have hu : u ∈ U_ker ⊔ Rτ := by rw [hcompl_U.symm.sup_eq_top]; trivial
          rcases Submodule.mem_sup.mp hu with ⟨a, ha, b, hb, rfl⟩
          dsimp only [πK, πR]
          rw [map_add, Submodule.projectionOnto_apply_left hcompl_U.symm ⟨a, ha⟩,
            Submodule.projectionOnto_apply_right hcompl_U.symm ⟨b, hb⟩, add_zero,
            map_add, Submodule.projectionOnto_apply_right hcompl_U ⟨a, ha⟩,
            Submodule.projectionOnto_apply_left hcompl_U ⟨b, hb⟩, zero_add] }
    have hcard_Uker : Fintype.card U_ker = 2 ^ (2 * J0.card - r_star) := by
      have hc := Fintype.card_congr eU_split
      rw [Fintype.card_prod, card_submodule_zmod2] at hc
      have hcard_q : Fintype.card (Fin (2 * m2) → F2) = 2 ^ (2 * m2) := by simp [ZMod.card]
      rw [hcard_q] at hc
      have hpow : 2 ^ Module.finrank F2 U_star = 2 ^ (2 * J0.card - r_star) * 2 ^ (2 * m2) := by
        have h1 := hBL_val.1
        rw [← pow_add]; congr 1
        dsimp only [U_star, r_star, m2] at h1 ⊢; omega
      rw [hpow] at hc
      exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by omega)) hc
    let wOut := remapWire n offset resPre.2 D0.output
    let wTap : Fin n → ℕ := fun l => remapWire n offset resPre.2 (tap0 l)
    let sTap : Fin n → (Fin (2 * m1) → F2) := fun l => B_L.slope (wTap l)
    let K : Matrix (Fin (2 * m2)) (Fin (2 * m2)) F2 := polarMatrix e A a1 σD τ2 sTap
    have hKd : ∀ α, K α α = 0 := polarMatrix_diag e A a1 σD τ2 sTap
    have hKs : ∀ α β, K α β = K β α := polarMatrix_symm e A a1 σD τ2 sTap
    let cLin : (Fin j0 → F2) →ₗ[F2] (Fin m2 → F2) :=
      { toFun := fun w t' => dotProduct (A (eAct (eRem t').val).val) (B w)
        map_add' := fun w1 w2 => by funext t'; simp only [Pi.add_apply, map_add, dotProduct_add]
        map_smul' := fun s w => by funext t'; simp [map_smul, dotProduct_smul] }
    have hgauss_per : ∀ (w : Fin j0 → F2) (u0 : U_ker),
        (∑ q : Fin (2 * m2) → F2,
          termY (yPW (B_L.pos w + (u0.val.val + τ2 q)) w)).natAbs ≤
        2 ^ (2 * m2 - (K + diagPair (cLin w)).rank / 2) := by
      intro w u0
      have hD0_wire : ∀ idx < n + D0.gates.length, ∀ q : Fin (2 * m2) → F2,
          (wiresOf D0.gates (bitsOf n (a1 + σD ((B_L.pos w + u0.val.val) + τ2 q) + σS w))).getD idx false =
            Bool.xor
              (Bool.xor ((wiresOf B_L.gates (bitsOf j0 w)).getD (B_L.off (remapWire n offset resPre.2 idx)) false)
                (decide (dotProduct (B_L.slope (remapWire n offset resPre.2 idx)) u0.val.val = 1)))
              (decide (dotProduct (B_L.slope (remapWire n offset resPre.2 idx)) (τ2 q) = 1)) := by
        intro idx hidx q
        have hlen_in : (bitsOf (2 * m1) (B_L.pos w + (u0.val.val + τ2 q)) ++ bitsOf j0 w).length = 2 * m1 + j0 := by
          simp [bitsOf_len]
        have hpre_ok : ∀ l : Fin n,
            (wiresOf resPre.1 (bitsOf (2 * m1) (B_L.pos w + (u0.val.val + τ2 q)) ++ bitsOf j0 w)).getD (resPre.2 l) false =
              decide ((a1 + σD ((B_L.pos w + u0.val.val) + τ2 q) + σS w) l = 1) := by
          intro l
          rw [bitsOf_concatVec2, hpre_sem l l.isLt, ← hcY l]
          simp only [yPW, add_assoc]
        rw [← hremap.2.2.2 _ _ hlen_in hpre_ok idx hidx]
        have hu_mem : u0.val.val + τ2 q ∈ U_star := U_star.add_mem u0.val.property (hτ2_mem q)
        rw [hBL_val.2.2.2.2.2 (remapWire n offset resPre.2 idx) (hremap.2.2.1 idx hidx) w (u0.val.val + τ2 q) hu_mem,
          dotProduct_add, zmod2_add_decide, Bool.xor_assoc]
      have hres := conjunct2_gauss_leaf e A h D0 tap0 a1 B Act rfl eAct J0 eRem σS hσS_fst σD
        hσD_fst hσD_u hσD_v τ2 hτ2_coord hτ2_kill (B_L.pos w + u0.val.val) w
        (B_L.slope wOut)
        (Bool.xor ((wiresOf B_L.gates (bitsOf j0 w)).getD (B_L.off wOut) false)
          (decide (dotProduct (B_L.slope wOut) u0.val.val = 1)))
        sTap
        (fun l => Bool.xor ((wiresOf B_L.gates (bitsOf j0 w)).getD (B_L.off (wTap l)) false)
          (decide (dotProduct (B_L.slope (wTap l)) u0.val.val = 1)))
        (fun q => hD0_wire D0.output hm0.2.2.2.2.1 q)
        (fun l q => hD0_wire (tap0 l) (hm0.2.2.2.2.2 l) q)
      have heq_sum : (∑ q : Fin (2 * m2) → F2, termY (yPW (B_L.pos w + (u0.val.val + τ2 q)) w)) =
          ∑ q : Fin (2 * m2) → F2,
            signBool (Bool.xor (D0.eval (bitsOf n (a1 + σD ((B_L.pos w + u0.val.val) + τ2 q) + σS w)))
              (decide (dotProduct (fun l => if (D0.wires (bitsOf n (a1 + σD ((B_L.pos w + u0.val.val) + τ2 q) + σS w))).getD (tap0 l) false then (1 : F2) else 0)
                (a1 + σD ((B_L.pos w + u0.val.val) + τ2 q) + σS w) = 1))) *
            signBool (decide (g (a1 + σD ((B_L.pos w + u0.val.val) + τ2 q) + σS w) = 1)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        dsimp only [termY, yPW, pos_b, D0, tap0]
        simp only [← add_assoc]
      rw [heq_sum]
      exact hres
    rcases schur_hamming_center m2 K hKd hKs with ⟨z0, hz0⟩
    have hUstar_bound : ∀ w : Fin j0 → F2,
        (∑ u : U_star, termY (yPW (B_L.pos w + u.val) w)).natAbs ≤
        2 ^ (2 * J0.card - r_star) * (2 ^ m2 * 2 ^ (m2 - hamWt (cLin w + z0))) := by
      intro w
      rw [← Equiv.sum_comp eU_split, Fintype.sum_prod_type]
      have htri : (∑ u0 : U_ker, ∑ q : Fin (2 * m2) → F2, termY (yPW (B_L.pos w + (eU_split (u0, q)).val) w)).natAbs ≤
          ∑ u0 : U_ker, (∑ q : Fin (2 * m2) → F2, termY (yPW (B_L.pos w + (u0.val.val + τ2 q)) w)).natAbs :=
        natAbs_sum_le_sum_natAbs _ _
      have hper_u0 : ∀ u0 : U_ker,
          (∑ q : Fin (2 * m2) → F2, termY (yPW (B_L.pos w + (u0.val.val + τ2 q)) w)).natAbs ≤
          2 ^ m2 * 2 ^ (m2 - hamWt (cLin w + z0)) := by
        intro u0
        have hg1 := hgauss_per w u0
        have hrk := hz0 (cLin w)
        have hwt_le : hamWt (cLin w + z0) ≤ m2 := by
          have := Finset.card_le_univ (Finset.univ.filter (fun t : Fin m2 => (cLin w + z0) t ≠ 0))
          simpa [hamWt] using this
        have hdiv_le : hamWt (cLin w + z0) ≤ (K + diagPair (cLin w)).rank / 2 := by
          dsimp only [hamDist] at hrk; omega
        have hexp : 2 * m2 - (K + diagPair (cLin w)).rank / 2 ≤ m2 + (m2 - hamWt (cLin w + z0)) := by omega
        calc (∑ q : Fin (2 * m2) → F2, termY (yPW (B_L.pos w + (u0.val.val + τ2 q)) w)).natAbs
            ≤ 2 ^ (2 * m2 - (K + diagPair (cLin w)).rank / 2) := hg1
          _ ≤ 2 ^ (m2 + (m2 - hamWt (cLin w + z0))) := Nat.pow_le_pow_right (by omega) hexp
          _ = 2 ^ m2 * 2 ^ (m2 - hamWt (cLin w + z0)) := pow_add 2 m2 _
      calc (∑ u0 : U_ker, ∑ q : Fin (2 * m2) → F2, termY (yPW (B_L.pos w + (eU_split (u0, q)).val) w)).natAbs
          ≤ ∑ u0 : U_ker, (∑ q : Fin (2 * m2) → F2, termY (yPW (B_L.pos w + (u0.val.val + τ2 q)) w)).natAbs := htri
        _ ≤ ∑ _u0 : U_ker, (2 ^ m2 * 2 ^ (m2 - hamWt (cLin w + z0))) := Finset.sum_le_sum fun u0 _ => hper_u0 u0
        _ = 2 ^ (2 * J0.card - r_star) * (2 ^ m2 * 2 ^ (m2 - hamWt (cLin w + z0))) := by
            rw [Finset.sum_const, Finset.card_univ, hcard_Uker, smul_eq_mul]
    let J : Finset (Fin m) := J0.image (fun t => (eAct t).val)
    have hJ_card : J.card = J0.card :=
      Finset.card_image_of_injective J0 (fun t1 t2 h => eAct.injective (Subtype.ext h))
    have hwt_eq : ∀ w : Fin j0 → F2, weight J (B w) = hamWt (cLin w) := by
      intro w
      dsimp only [weight, hamWt]
      apply Finset.card_bij (fun i hi => by
        have hact : i ∈ Act := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨w, (Finset.mem_filter.mp hi).2.2⟩⟩
        have hntJ0 : eAct.symm ⟨i, hact⟩ ∉ J0 := by
          intro hmem
          apply (Finset.mem_filter.mp hi).2.1
          exact Finset.mem_image.mpr ⟨eAct.symm ⟨i, hact⟩, hmem, congrArg Subtype.val (eAct.apply_symm_apply ⟨i, hact⟩)⟩
        exact eRem.symm ⟨eAct.symm ⟨i, hact⟩, hntJ0⟩)
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        dsimp only [cLin, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Equiv.apply_symm_apply]
        have hval : (eAct (eAct.symm ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨w, hi.2⟩⟩⟩)).val = i :=
          congrArg Subtype.val (eAct.apply_symm_apply _)
        rw [hval]; exact hi.2
      · intro i1 hi1 i2 hi2 h
        have h1 := congrArg (fun t' => (eAct (eRem t').val).val) h
        simp only [Equiv.apply_symm_apply] at h1
        exact h1
      · intro t' ht'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht'
        let i := (eAct (eRem t').val).val
        have hi_notJ : i ∉ J := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨t, htJ0, hteq⟩
          have ht_eq : t = (eRem t').val := eAct.injective (Subtype.ext hteq)
          exact (eRem t').property (ht_eq ▸ htJ0)
        refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi_notJ, ht'⟩, ?_⟩
        apply eRem.injective
        rw [Equiv.apply_symm_apply]
        apply Subtype.ext
        apply eAct.injective
        rw [Equiv.apply_symm_apply]
    refine ⟨j0, B, J, hB_inj, ?_, ?_⟩
    · rw [hJ_card, ← hr0_eq]
      exact le_trans (Nat.add_le_add_left (le_trans hJ0_card hr_star_le_c0) r0)
        (by rw [add_comm r0 c0]; exact hm0.2.2.2.1)
    · have hT_chain : T ≤ 2 ^ n * (2 ^ (base - 2 * m1) *
          (2 ^ r_star * (2 ^ (2 * J0.card - r_star) * (2 ^ m2 * ∑ w : Fin j0 → F2, 2 ^ (m2 - hamWt (cLin w)))))) := by
        have hsum_w : ∑ w : Fin j0 → F2, (∑ u : U_star, termY (yPW (B_L.pos w + u.val) w)).natAbs ≤
            2 ^ (2 * J0.card - r_star) * (2 ^ m2 * ∑ w : Fin j0 → F2, 2 ^ (m2 - hamWt (cLin w))) := by
          calc ∑ w : Fin j0 → F2, (∑ u : U_star, termY (yPW (B_L.pos w + u.val) w)).natAbs
              ≤ ∑ w : Fin j0 → F2, 2 ^ (2 * J0.card - r_star) * (2 ^ m2 * 2 ^ (m2 - hamWt (cLin w + z0))) :=
                Finset.sum_le_sum fun w _ => hUstar_bound w
            _ = 2 ^ (2 * J0.card - r_star) * (2 ^ m2 * ∑ w : Fin j0 → F2, 2 ^ (m2 - hamWt (cLin w + z0))) := by
                simp_rw [← Finset.mul_sum]
            _ ≤ 2 ^ (2 * J0.card - r_star) * (2 ^ m2 * ∑ w : Fin j0 → F2, 2 ^ (m2 - hamWt (cLin w))) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (walsh_coset_bound cLin z0))
        calc T ≤ 2 ^ n * Bval i0 := hi0
          _ ≤ 2 ^ n * (2 ^ (base - 2 * m1) *
              (∑ w : Fin j0 → F2, ∑ p : Fin (2 * m1) → F2, termY (yPW p w)).natAbs) :=
              Nat.mul_le_mul_left _ hwr0_le
          _ ≤ 2 ^ n * (2 ^ (base - 2 * m1) *
              (2 ^ r_star * ∑ w : Fin j0 → F2, (∑ u : U_star, termY (yPW (B_L.pos w + u.val) w)).natAbs)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hℓ0_le)
          _ ≤ 2 ^ n * (2 ^ (base - 2 * m1) *
              (2 ^ r_star * (2 ^ (2 * J0.card - r_star) * (2 ^ m2 * ∑ w : Fin j0 → F2, 2 ^ (m2 - hamWt (cLin w)))))) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsum_w))
      have hfactor_eq : 2 ^ (k + m) * (2 ^ n * (2 ^ (base - 2 * m1) *
          (2 ^ r_star * (2 ^ (2 * J0.card - r_star) * (2 ^ m2 * ∑ w : Fin j0 → F2, 2 ^ (m2 - hamWt (cLin w))))))) =
          2 ^ (2 * n) * mass j0 B J := by
        dsimp only [mass]
        simp_rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hwt_eq w]
        have hwt_le : hamWt (cLin w) ≤ m2 := by
          have := Finset.card_le_univ (Finset.univ.filter (fun t : Fin m2 => cLin w t ≠ 0))
          simpa [hamWt] using this
        exact pow2_combine_eq k m r m1 J0.card r_star (hamWt (cLin w)) hm1_le_m h2m1_le_base hJ0_le_m1 hr_star_le_2J0 hwt_le
      calc 2 ^ (k + m) * T
          ≤ 2 ^ (k + m) * (2 ^ n * (2 ^ (base - 2 * m1) *
              (2 ^ r_star * (2 ^ (2 * J0.card - r_star) * (2 ^ m2 * ∑ w : Fin j0 → F2, 2 ^ (m2 - hamWt (cLin w))))))) :=
            Nat.mul_le_mul_left _ hT_chain
        _ = 2 ^ (2 * n) * mass j0 B J := hfactor_eq

lemma conjunct4_proof (k m r : ℕ)
    (e : (Fin (k + 2 * m + r) → F2) ≃ₗ[F2]
      (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2))))
    (A : Fin m → (Fin k → F2)) (h : (Fin k → F2) → F2)
    (s : ℕ) (C : Circuit) (hleg : legalGates (2 * (k + 2 * m + r)) C.gates)
    (hcost : costGates C.gates ≤ s)
    (hT : 2 ^ (2 * (k + 2 * m + r)) ≤ (∑ x : Fin (k + 2 * m + r) → F2, ∑ y : Fin (k + 2 * m + r) → F2,
      if C.eval (bitsOf (k + 2 * m + r) x ++ bitsOf (k + 2 * m + r) y) =
        decide (dotProduct x y + (h (e y).1 + ∑ i : Fin m,
          dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i) = 1)
      then (1 : ℤ) else -1).natAbs) :
    (k + 2 * m + r) + ((Finset.univ : Finset (Fin m)).filter (fun i => A i ≠ 0)).card ≤ s := by
  let n := k + 2 * m + r
  let g : (Fin n → F2) → F2 := fun y =>
    h (e y).1 + ∑ i : Fin m, dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
  have hle_pow : 2 ^ (2 * n) ≤ 2 ^ (n + s) := viaCircuit_le_bound n s g (2 ^ (2 * n)) C hleg hcost hT
  have hn_le_s : n ≤ s := by
    have h2 : 2 * n ≤ n + s := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hle_pow
    omega
  have hbase_le_s : 2 * m + r ≤ s := by omega
  rcases conjunct2_forward k m r e A h s (2 ^ (2 * n)) hbase_le_s C hleg hcost hT with
    ⟨j, B, J, hB_inj, hcostJ, hmassJ⟩
  have hpos2n : 0 < 2 ^ (2 * n) := Nat.pow_pos (by omega)
  have hmass_ge : 2 ^ (k + m) ≤ ∑ u : Fin j → F2,
      2 ^ (m - ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ dotProduct (A i) (B u) ≠ 0)).card) := by
    have h1 : 2 ^ (2 * n) * 2 ^ (k + m) ≤ 2 ^ (2 * n) *
        ∑ u : Fin j → F2, 2 ^ (m - ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ dotProduct (A i) (B u) ≠ 0)).card) := by
      rw [mul_comm (2 ^ (2 * n)) (2 ^ (k + m))]; exact hmassJ
    exact Nat.le_of_mul_le_mul_left h1 hpos2n
  have hj_le_k : j ≤ k := by
    have h1 := LinearMap.finrank_le_finrank_of_injective hB_inj
    simpa only [Module.finrank_fin_fun] using h1
  have hmass_le : (∑ u : Fin j → F2,
      2 ^ (m - ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ dotProduct (A i) (B u) ≠ 0)).card)) ≤
      2 ^ (j + m) := by
    calc (∑ u : Fin j → F2,
            2 ^ (m - ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ dotProduct (A i) (B u) ≠ 0)).card))
        ≤ ∑ _u : Fin j → F2, 2 ^ m :=
          Finset.sum_le_sum fun u _ => Nat.pow_le_pow_right (by omega) (Nat.sub_le m _)
      _ = 2 ^ (j + m) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin, ZMod.card, smul_eq_mul, ← pow_add]
  have hk_le_j : k ≤ j := by
    have h1 : 2 ^ (k + m) ≤ 2 ^ (j + m) := le_trans hmass_ge hmass_le
    have h2 : k + m ≤ j + m := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp h1
    omega
  have hjk : j = k := by omega
  have hB_surj : Function.Surjective B := by
    have hcard : Fintype.card (Fin j → F2) = Fintype.card (Fin k → F2) := by simp [hjk]
    exact (Fintype.bijective_iff_injective_and_card B).mpr ⟨hB_inj, hcard⟩ |>.2
  have hwt_zero : ∀ u : Fin j → F2,
      ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ dotProduct (A i) (B u) ≠ 0)).card = 0 := by
    intro u
    by_contra hne
    have hpos : 0 < ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ dotProduct (A i) (B u) ≠ 0)).card :=
      Nat.pos_of_ne_zero hne
    have hm_pos : 0 < m := by
      have hle : ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ dotProduct (A i) (B u) ≠ 0)).card ≤ m := by
        have := Finset.card_le_univ (Finset.univ.filter (fun i : Fin m => i ∉ J ∧ dotProduct (A i) (B u) ≠ 0))
        simpa using this
      omega
    have hlt_u : 2 ^ (m - ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ dotProduct (A i) (B u) ≠ 0)).card) < 2 ^ m :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    have hlt_sum : (∑ v : Fin j → F2,
        2 ^ (m - ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ dotProduct (A i) (B v) ≠ 0)).card)) <
        ∑ _v : Fin j → F2, 2 ^ m :=
      Finset.sum_lt_sum (fun v _ => Nat.pow_le_pow_right (by omega) (Nat.sub_le m _))
        ⟨u, Finset.mem_univ u, hlt_u⟩
    have hrhs : ∑ _v : Fin j → F2, 2 ^ m = 2 ^ (k + m) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ZMod.card, smul_eq_mul, ← pow_add, hjk]
    omega
  have hsubJ : (Finset.univ : Finset (Fin m)).filter (fun i => A i ≠ 0) ⊆ J := by
    intro i hi
    have hAne : A i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hex : ∃ a : Fin k, A i a ≠ 0 := by
      by_contra hnot; push Not at hnot; exact hAne (funext hnot)
    rcases hex with ⟨a, ha⟩
    rcases hB_surj (Pi.single a 1) with ⟨u, hu⟩
    by_contra hi_notJ
    have hmem : i ∈ (Finset.univ : Finset (Fin m)).filter (fun l => l ∉ J ∧ dotProduct (A l) (B u) ≠ 0) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi_notJ, ?_⟩
      rw [hu, dotProduct_single, mul_one]; exact ha
    have hcard0 := hwt_zero u
    rw [Finset.card_eq_zero] at hcard0
    rw [hcard0] at hmem
    exact Finset.notMem_empty i hmem
  have hact_le : ((Finset.univ : Finset (Fin m)).filter (fun i => A i ≠ 0)).card ≤ J.card :=
    Finset.card_le_card hsubJ
  omega

end PEqualNP.Outside.L_meta_32569_aux

theorem PEqualNP.Outside.L_meta_32569 : (∀ k m r : ℕ,
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
  let quad := fun (j : ℕ) (f : (Fin j → F) → F) =>
    ∃ (z : F) (l : Fin j → F) (M : Fin j → Fin j → F), ∀ u,
      f u = z + dotProduct l u + ∑ a, ∑ b, M a b * u a * u b
  ∀ (e : V ≃ₗ[F] S × (D × (D × Z))) (A : Fin m → S) (h : S → F),
    let active := ((Finset.univ : Finset (Fin m)).filter (fun i => A i ≠ 0)).card
    let g := fun (y : V) => h (e y).1 + ∑ i : Fin m,
      dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
    let raw := fun (C : Circ) => (∑ x : V, ∑ y : V,
      if C.eval (bits n x ++ bits n y) = decide (dotProduct x y + g y = 1)
      then (1 : ℤ) else -1).natAbs
    let weight := fun (J : Finset (Fin m)) (s : S) =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ J ∧ dotProduct (A i) s ≠ 0)).card
    let mass := fun (j : ℕ) (B : (Fin j → F) →ₗ[F] S) (J : Finset (Fin m)) =>
      ∑ u : Fin j → F, 2^(m-weight J (B u))
    let fits := fun (s T : ℕ) => ∃ C : Circ, legal (2*n) C ∧ cost C ≤ s ∧ T ≤ raw C
    let code := fun (s T : ℕ) => ∃ (j : ℕ) (B : (Fin j → F) →ₗ[F] S) (J : Finset (Fin m)),
      Function.Injective B ∧ base+j+J.card ≤ s ∧ 2^(k+m)*T ≤ 2^(2*n)*mass j B J
    (∀ s T : ℕ, s ≤ base → (fits s T ↔ T ≤ 2^(n+s))) ∧
    (∀ s T : ℕ, base ≤ s → (fits s T → code s T) ∧ (quad k h → (code s T → fits s T))) ∧
    (∀ (j : ℕ) (B : (Fin j → F) →ₗ[F] S) (J : Finset (Fin m)), Function.Injective B →
      quad j (fun u => h (B u)) → ∃ C : Circ, legal (2*n) C ∧ cost C ≤ base+j+J.card ∧
        2^(k+m)*raw C = 2^(2*n)*mass j B J) ∧
    (∀ s : ℕ, fits s (2^(2*n)) → n+active ≤ s) ∧
    (quad k h → fits (n+active) (2^(2*n)))) := by
  intro k m r n Circ F legal cost bits V S D Z base quad e A h active g raw weight mass fits code
  have hconj3 : ∀ (j : ℕ) (B : (Fin j → F) →ₗ[F] S) (J : Finset (Fin m)), Function.Injective B →
      quad j (fun u => h (B u)) → ∃ C : Circ, legal (2*n) C ∧ cost C ≤ base+j+J.card ∧
        2^(k+m)*raw C = 2^(2*n)*mass j B J := by
    intro j B J hB hq
    exact PEqualNP.Outside.L_meta_32569_aux.conjunct3_proof k m r e A h j B J hB hq
  have hconj2_back : ∀ s T : ℕ, quad k h → code s T → fits s T := by
    rintro s T hqh ⟨j, B, J, hB, hcostJ, hmassJ⟩
    have hqB : quad j (fun u => h (B u)) :=
      PEqualNP.Outside.L_meta_32569_aux.isQuad_comp_linear B hqh
    rcases hconj3 j B J hB hqB with ⟨C, hleg, hcostC, hrawC⟩
    refine ⟨C, hleg, le_trans hcostC hcostJ, ?_⟩
    have hpos : 0 < 2 ^ (k + m) := Nat.pow_pos (by omega)
    exact Nat.le_of_mul_le_mul_left (hrawC ▸ hmassJ) hpos
  refine ⟨?_, ?_, hconj3, ?_, ?_⟩
  · intro s T hs
    constructor
    · rintro ⟨C, hleg, hcostC, hT⟩
      exact PEqualNP.Outside.L_meta_32569_aux.viaCircuit_le_bound n s g T C hleg hcostC hT
    · intro hT
      exact PEqualNP.Outside.L_meta_32569_aux.conjunct1_back k m r e A h s T hs hT
  · intro s T hs
    refine ⟨?_, fun hqh hc => hconj2_back s T hqh hc⟩
    rintro ⟨C, hleg, hcostC, hT⟩
    exact PEqualNP.Outside.L_meta_32569_aux.conjunct2_forward k m r e A h s T hs C hleg hcostC hT
  · rintro s ⟨C, hleg, hcostC, hT⟩
    exact PEqualNP.Outside.L_meta_32569_aux.conjunct4_proof k m r e A h s C hleg hcostC hT
  · intro hqh
    let Jact : Finset (Fin m) := Finset.univ.filter (fun i => A i ≠ 0)
    have hcode : code (n + active) (2 ^ (2 * n)) := by
      refine ⟨k, LinearMap.id, Jact, Function.injective_id, by dsimp only [n, base, active, Jact]; omega, ?_⟩
      have hmass_act : mass k LinearMap.id Jact = 2 ^ (k + m) := by
        dsimp only [mass, weight]
        have hwt0 : ∀ u : Fin k → F,
            ((Finset.univ : Finset (Fin m)).filter (fun i => i ∉ Jact ∧ dotProduct (A i) u ≠ 0)).card = 0 := by
          intro u
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro i _ ⟨hni, hne⟩
          have hAi0 : A i = 0 := by
            by_contra hA
            exact hni (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)
          rw [hAi0, zero_dotProduct] at hne
          exact hne rfl
        simp_rw [hwt0, Nat.sub_zero]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, ZMod.card, smul_eq_mul, ← pow_add]
      rw [hmass_act, mul_comm]
    exact hconj2_back (n + active) (2 ^ (2 * n)) hqh hcode
