import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_33624_aux

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
          ms.Nodup →
          ∀ (p : Branch k t → Prop),
            (∃ idx ∈ ms, (∃! j : Fin (children idx).length, p ((children idx).get j)) ∧
              ∀ idx2 ∈ ms, idx2 ≠ idx → ∀ j : Fin (children idx2).length, ¬ p ((children idx2).get j)) →
            ∃! q : Fin (ms.flatMap children).length, p ((ms.flatMap children).get q) := by
        intro ms hnd p
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
                have hval : (⟨q.val, hql⟩ : Fin (children idx).length).val = j0.val :=
                  congrArg Fin.val (hj0u ⟨q.val, hql⟩ hq')
                exact Fin.ext hval
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
          · have hih := ihms hnd.2 ⟨idx, hmem, huniq, fun idx2 hi2 hne2 => hrest idx2 (List.mem_cons_of_mem a hi2) hne2⟩
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
                have hval : q.val = (children a).length + q0.val := by
                  have h1 := congrArg Fin.val heq; dsimp at h1; omega
                exact Fin.ext hval
      rcases hLpart z x with ⟨idx0, hidx0, hidx0u⟩
      apply hflat_bij (List.finRange L.length) (List.nodup_finRange L.length)
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

lemma l835_main :
∀ (k t : ℕ),
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
  let Z := Fin t → F
  ∀ C : Circ, legal (k+t) C →
    ∃ (N : ℕ) (r : Fin N → ℕ) (U : Fin N → Submodule F V) (a : Fin N → V)
      (D : Fin N → Circ) (tap : Fin N → Fin k → ℕ),
      let pos := fun (i : Fin N) (z : Z) (j : Fin k) =>
        if ((D i).wires (bits t z)).getD (tap i j) false then (1 : F) else 0
      0 < N ∧ (∀ i, Module.finrank F (U i) + r i = k ∧ legal t (D i) ∧
        cost (D i)+r i ≤ cost C ∧ (D i).output < t+(D i).size ∧
        ∀ j, tap i j < t+(D i).size) ∧
      (∀ (z : Z) (x : V), ∃! i : Fin N, x-pos i z ∈ U i) ∧
      ∀ (i : Fin N) (z : Z) (u : V), u ∈ U i →
        C.eval (bits k (pos i z+u) ++ bits t z) =
          Bool.xor ((D i).eval (bits t z)) (decide (dotProduct (a i) u = 1)) := by
  intro k t Circ F legal cost bits V Z C hC
  have hlegC : legalGates (k + t) C.gates := hC
  rcases build_branch_list k t C.gates hlegC with ⟨L, hLpos, hLval, hLpart⟩
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
      refine ⟨hBi.1, ?_, ?_, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
      · exact legalGates_snoc hBi.2.1 (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
      · have hc0 := costGates_snoc_zero (L.get i).gates ⟨.or, []⟩ (by simp)
        have := hBi.2.2.1
        change costGates ((L.get i).gates ++ [⟨.or, []⟩]) + (L.get i).r ≤
          costGates C.gates
        omega
      · intro j
        simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, List.length_singleton]
        have := hBi.2.2.2.1 j; omega
    · intro z x
      have hpeq : ∀ i : Fin L.length,
          (fun j : Fin k => if (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨(L.get i).gates ++ [⟨.or, []⟩], t + (L.get i).gates.length⟩ (bits t z)).getD ((L.get i).tap j) false then (1 : F) else 0) =
          (L.get i).pos z := by
        intro i; funext j
        have hBi := hLval (L.get i) (List.get_mem L i)
        change (if (wiresOf ((L.get i).gates ++ [⟨.or, []⟩]) (bitsOf t z)).getD ((L.get i).tap j) false then (1 : F) else 0) = _
        rw [wiresOf_append_getD_lt (L.get i).gates [⟨.or, []⟩] _
          (by rw [bitsOf_len]; exact hBi.2.2.2.1 j)]
        rfl
      have hconv : (fun i : Fin L.length => x - (fun j : Fin k => if (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨(L.get i).gates ++ [⟨.or, []⟩], t + (L.get i).gates.length⟩ (bits t z)).getD ((L.get i).tap j) false then (1 : F) else 0) ∈ (L.get i).U) =
          (fun i : Fin L.length => x - (L.get i).pos z ∈ (L.get i).U) := by
        funext i; rw [hpeq i]
      exact (congrArg (fun P => ∃! i : Fin L.length, P i) hconv).mpr (hLpart z x)
    · intro i z u _
      have hclen : ∀ w : V, (C.wires (bits k w ++ bits t z)).length = k + t + C.gates.length := by
        intro w
        have h := wiresOf_len C.gates (bits k w ++ bits t z)
        simp only [List.length_append, bits, List.length_ofFn] at h
        exact h
      have hlhs : ∀ w : V, C.eval (bits k w ++ bits t z) = false := by
        intro w
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by have := hclen w; omega)]
        rfl
      have hrhs : (PEqualNP.CircuitLowerBounds.Circuit.mk ((L.get i).gates ++ [⟨.or, []⟩]) (t + (L.get i).gates.length)).eval (bits t z) = false := by
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval
        change (wiresOf ((L.get i).gates ++ [⟨.or, []⟩]) (bitsOf t z)).getD (t + (L.get i).gates.length) false = false
        rw [wiresOf_snoc_last_eq (L.get i).gates ⟨.or, []⟩
          (bitsOf t z) (bitsOf_len t z)]
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
      rw [hlhs _, hrhs]
      simp


section Part844

open Classical

def signB (b : Bool) : ℤ := if b then (-1 : ℤ) else 1

lemma signB_xor (a b : Bool) : signB (Bool.xor a b) = signB a * signB b := by
  cases a <;> cases b <;> rfl

lemma bitsOf_append {k t : ℕ} (y : Fin k → F2) (z : Fin t → F2) :
    bitsOf k y ++ bitsOf t z = bitsOf (k + t) (Fin.append y z) := by
  apply List.ext_getElem
  · simp [bitsOf_len]
  · intro i h1 h2
    simp only [bitsOf, List.getElem_ofFn]
    by_cases hik : i < k
    · rw [List.getElem_append_left (by simp [hik])]
      simp only [List.getElem_ofFn]
      have hval : Fin.append y z ⟨i, by simp [bitsOf_len] at h2; exact h2⟩ = y ⟨i, hik⟩ := by
        have hcast : (⟨i, by simp [bitsOf_len] at h2; exact h2⟩ : Fin (k + t)) = Fin.castAdd t ⟨i, hik⟩ :=
          Fin.ext rfl
        rw [hcast, Fin.append_left]
      exact congrArg (fun v => decide (v = 1)) hval.symm
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_ofFn, List.getElem_ofFn]
      have hval : Fin.append y z ⟨i, by simp [bitsOf_len] at h2; exact h2⟩ = z ⟨i - k, by simp [bitsOf_len] at h2; omega⟩ := by
        have hcast : (⟨i, by simp [bitsOf_len] at h2; exact h2⟩ : Fin (k + t)) =
            Fin.natAdd k ⟨i - k, by simp [bitsOf_len] at h2; omega⟩ := by
          apply Fin.ext; dsimp; omega
        rw [hcast, Fin.append_right]
      exact congrArg (fun v => decide (v = 1)) hval.symm

lemma zmod2_vec_eq_of_dot {k : ℕ} (w : Fin k → F2) (h : ∀ u : Fin k → F2, dotProduct w u = 0) :
    w = 0 := by
  funext j
  have := h (Pi.single j 1)
  simpa [dotProduct_single] using this

def pairMap {k : ℕ} (U : Submodule F2 (Fin k → F2)) : (Fin k → F2) →ₗ[F2] (U →ₗ[F2] F2) :=
  { toFun := fun w =>
      { toFun := fun u => dotProduct w u.val
        map_add' := fun a b => dotProduct_add w a.val b.val
        map_smul' := fun c a => by simp [dotProduct_smul] }
    map_add' := fun a b => by ext u; exact add_dotProduct a b u.val
    map_smul' := fun c a => by ext u; simp [smul_dotProduct] }

def orthComp {k : ℕ} (U : Submodule F2 (Fin k → F2)) : Submodule F2 (Fin k → F2) :=
  LinearMap.ker (pairMap U)

lemma mem_orthComp {k : ℕ} (U : Submodule F2 (Fin k → F2)) (w : Fin k → F2) :
    w ∈ orthComp U ↔ ∀ u ∈ U, dotProduct w u = 0 := by
  simp only [orthComp, LinearMap.mem_ker, pairMap, LinearMap.ext_iff, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.zero_apply, Subtype.forall]

lemma pairMap_surjective {k : ℕ} (U : Submodule F2 (Fin k → F2)) :
    Function.Surjective (pairMap U) := by
  intro φ
  rcases Submodule.exists_isCompl U with ⟨V, hUV⟩
  let φ' : (Fin k → F2) →ₗ[F2] F2 := φ.comp (Submodule.projectionOnto U V hUV)
  let w : Fin k → F2 := fun j => φ' (Pi.single j 1)
  refine ⟨w, ?_⟩
  ext u
  have hu : u.val = ∑ j : Fin k, u.val j • Pi.single j (1 : F2) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : φ' u.val = φ u := by
    simp only [φ', LinearMap.comp_apply]
    rw [Submodule.projectionOnto_apply_left hUV u]
  rw [← h1]
  conv_rhs => rw [hu]
  rw [map_sum]
  simp only [pairMap, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, map_smul, smul_eq_mul, w]
  apply Finset.sum_congr rfl
  intro j _; exact mul_comm _ _

lemma finrank_orthComp {k : ℕ} (U : Submodule F2 (Fin k → F2)) :
    Module.finrank F2 (orthComp U) + Module.finrank F2 U = k := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (pairMap U)
  have hran : LinearMap.range (pairMap U) = ⊤ := LinearMap.range_eq_top.mpr (pairMap_surjective U)
  rw [hran, finrank_top] at hrk
  have hdual : Module.finrank F2 (U →ₗ[F2] F2) = Module.finrank F2 U :=
    Subspace.dual_finrank_eq
  have htop : Module.finrank F2 (Fin k → F2) = k := by simp
  rw [hdual, htop] at hrk
  change Module.finrank F2 U + Module.finrank F2 (orthComp U) = k at hrk
  omega

lemma card_submodule_eq_pow {k : ℕ} (U : Submodule F2 (Fin k → F2)) :
    Fintype.card U = 2 ^ Module.finrank F2 U := by
  let b := Module.finBasis F2 U
  have heq : U ≃ (Fin (Module.finrank F2 U) → F2) := b.equivFun.toEquiv
  rw [Fintype.card_congr heq, Fintype.card_fun, Fintype.card_fin, ZMod.card]

lemma sum_sign_submodule {k : ℕ} (U : Submodule F2 (Fin k → F2)) (w : Fin k → F2) :
    (∑ u : U, signB (decide (dotProduct w u.val = 1))) =
      if w ∈ orthComp U then (2 : ℤ) ^ Module.finrank F2 U else 0 := by
  by_cases hw : w ∈ orthComp U
  · simp only [hw, ↓reduceIte]
    have h0 : ∀ u : U, signB (decide (dotProduct w u.val = 1)) = 1 := by
      intro u
      rw [(mem_orthComp U w).mp hw u.val u.property]
      rfl
    simp_rw [h0]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_submodule_eq_pow U]
    push_cast; rfl
  · simp only [hw, ↓reduceIte]
    rw [mem_orthComp] at hw
    push Not at hw
    rcases hw with ⟨u0, hu0, hne⟩
    have hdot1 : dotProduct w u0 = 1 := by
      rcases zmod2_cases (dotProduct w u0) with h | h
      · exact absurd h hne
      · exact h
    let e : U ≃ U := Equiv.addRight ⟨u0, hu0⟩
    have hshift : (∑ u : U, signB (decide (dotProduct w u.val = 1))) =
        ∑ u : U, signB (decide (dotProduct w (e u).val = 1)) :=
      (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    have hneg : ∀ u : U, signB (decide (dotProduct w (e u).val = 1)) =
        - signB (decide (dotProduct w u.val = 1)) := by
      intro u
      change signB (decide (dotProduct w (u.val + u0) = 1)) = _
      rw [dotProduct_add, hdot1, zmod2_add_decide]
      cases decide (dotProduct w u.val = 1) <;> decide
    simp_rw [hneg, Finset.sum_neg_distrib] at hshift
    linarith

lemma sum_sign_univ {k : ℕ} (w : Fin k → F2) :
    (∑ x : Fin k → F2, signB (decide (dotProduct x w = 1))) =
      if w = 0 then (2 : ℤ) ^ k else 0 := by
  have heq : (∑ x : Fin k → F2, signB (decide (dotProduct x w = 1))) =
      ∑ u : (⊤ : Submodule F2 (Fin k → F2)), signB (decide (dotProduct w u.val = 1)) := by
    let e : (⊤ : Submodule F2 (Fin k → F2)) ≃ (Fin k → F2) :=
      { toFun := fun u => u.val
        invFun := fun x => ⟨x, Submodule.mem_top⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Fintype.sum_equiv e _ _ (fun u => by
      change signB (decide (dotProduct w u.val = 1)) = signB (decide (dotProduct u.val w = 1))
      rw [dotProduct_comm])).symm
  rw [heq, sum_sign_submodule ⊤ w]
  have htop : Module.finrank F2 (⊤ : Submodule F2 (Fin k → F2)) = k := by simp
  rw [htop]
  by_cases hw0 : w = 0
  · subst hw0
    have hm : (0 : Fin k → F2) ∈ orthComp (⊤ : Submodule F2 (Fin k → F2)) := by
      rw [mem_orthComp]; intro u _; simp
    simp [hm]
  · have hnm : w ∉ orthComp (⊤ : Submodule F2 (Fin k → F2)) := by
      rw [mem_orthComp]
      intro hall
      exact hw0 (zmod2_vec_eq_of_dot w (fun u => hall u Submodule.mem_top))
    simp [hw0, hnm]

lemma exists_proj_basis {k r : ℕ} (W : Submodule F2 (Fin k → F2)) (hr : Module.finrank F2 W = r) :
    ∃ (b ℓ : Fin r → (Fin k → F2)),
      (∀ i, b i ∈ W) ∧
      (∀ w ∈ W, ∑ i : Fin r, (dotProduct (ℓ i) w) • b i = w) := by
  let bas : Module.Basis (Fin r) F2 W := (Module.finBasis F2 W).reindex (finCongr hr)
  let b : Fin r → (Fin k → F2) := fun i => (bas i).val
  let Btr : (Fin k → F2) →ₗ[F2] (Fin r → F2) :=
    { toFun := fun v i => dotProduct (b i) v
      map_add' := fun x y => by funext i; exact dotProduct_add (b i) x y
      map_smul' := fun c x => by funext i; simp [dotProduct_smul] }
  have hker_eq : LinearMap.ker Btr = orthComp W := by
    ext v
    rw [LinearMap.mem_ker, mem_orthComp]
    constructor
    · intro hv u hu
      have hu_rep : (⟨u, hu⟩ : W) = ∑ i : Fin r, bas.repr ⟨u, hu⟩ i • bas i := (bas.sum_repr ⟨u, hu⟩).symm
      have hu_val : u = ∑ i : Fin r, bas.repr ⟨u, hu⟩ i • b i := by
        have h1 := congrArg W.subtype hu_rep
        simp only [map_sum, map_smul, Submodule.coe_subtype] at h1
        exact h1
      rw [hu_val, dotProduct_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [dotProduct_smul, dotProduct_comm, smul_eq_mul]
      have hvi : dotProduct (b i) v = 0 := congrFun hv i
      rw [hvi, mul_zero]
    · intro hv
      funext i
      change dotProduct (b i) v = 0
      rw [dotProduct_comm]
      exact hv (b i) (bas i).property
  have hsurj : Function.Surjective Btr := by
    have hrk := LinearMap.finrank_range_add_finrank_ker Btr
    rw [hker_eq] at hrk
    have horth := finrank_orthComp W
    have htop1 : Module.finrank F2 (Fin k → F2) = k := by simp
    have htop2 : Module.finrank F2 (Fin r → F2) = r := by simp
    have hran_dim : Module.finrank F2 (LinearMap.range Btr) = Module.finrank F2 (Fin r → F2) := by omega
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hran_dim)
  let ℓ : Fin r → (Fin k → F2) := fun i => (hsurj (Pi.single i 1)).choose
  have hℓ : ∀ i j : Fin r, dotProduct (b j) (ℓ i) = if j = i then 1 else 0 := by
    intro i j
    have hspec := (hsurj (Pi.single i 1)).choose_spec
    have := congrFun hspec j
    simpa [Btr, Pi.single_apply] using this
  refine ⟨b, ℓ, fun i => (bas i).property, fun w hw => ?_⟩
  have hw_rep : (⟨w, hw⟩ : W) = ∑ j : Fin r, bas.repr ⟨w, hw⟩ j • bas j := (bas.sum_repr ⟨w, hw⟩).symm
  have hw_val : w = ∑ j : Fin r, bas.repr ⟨w, hw⟩ j • b j := by
    have h1 := congrArg W.subtype hw_rep
    simp only [map_sum, map_smul, Submodule.coe_subtype] at h1
    exact h1
  have hcoeff : ∀ i : Fin r, dotProduct (ℓ i) w = bas.repr ⟨w, hw⟩ i := by
    intro i
    conv_lhs => rw [hw_val]
    rw [dotProduct_sum]
    have hterm : ∀ j : Fin r, dotProduct (ℓ i) (bas.repr ⟨w, hw⟩ j • b j) =
        if j = i then bas.repr ⟨w, hw⟩ j else 0 := by
      intro j
      rw [dotProduct_smul, dotProduct_comm, hℓ i j, smul_eq_mul]
      split_ifs <;> simp
    simp_rw [hterm]
    simp
  simp_rw [hcoeff]
  exact hw_val.symm

def shiftGate (k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (· + k)⟩

lemma shiftGates_eval (k m : ℕ) (gs : List Gate) (hleg : legalGates m gs)
    (x y : List Bool) (hx : x.length = k) (hy : y.length = m) :
    ∀ w < m + gs.length,
      (wiresOf (gs.map (shiftGate k)) (x ++ y)).getD (k + w) false = (wiresOf gs y).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w hw
    simp only [List.length_nil, Nat.add_zero] at hw
    simp only [List.map_nil, wiresOf, Circuit.wires, List.foldl_nil]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        show k + w - x.length = w by omega, ← List.getD_eq_getElem?_getD]
  | append_singleton gs g ih =>
    have hpre := legalGates_prefix hleg
    have hih := ih hpre.1
    intro w hw
    simp only [List.length_append, List.length_singleton] at hw
    have hmap : (gs ++ [g]).map (shiftGate k) = gs.map (shiftGate k) ++ [shiftGate k g] := by simp
    rw [hmap]
    by_cases hweq : w = m + gs.length
    · subst hweq
      have h1 : k + (m + gs.length) = (k + m) + (gs.map (shiftGate k)).length := by simp; omega
      rw [h1, wiresOf_snoc_last_eq _ (shiftGate k g) (x ++ y) (by simp [hx, hy]),
          wiresOf_snoc_last_eq gs g y hy]
      simp only [shiftGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [Function.comp_apply, Nat.add_comm]
      exact hih i (hpre.2.1 i hi)
    · rw [wiresOf_append_getD_lt (gs.map (shiftGate k)) [shiftGate k g] (x ++ y) (by simp [hx, hy]; omega),
          wiresOf_append_getD_lt gs [g] y (by rw [hy]; omega)]
      exact hih w (by omega)

lemma shiftGates_spec (k m : ℕ) (gs : List Gate) (hleg : legalGates m gs) :
    let gsS := gs.map (shiftGate k)
    legalGates (k + m) gsS ∧
    costGates gsS = costGates gs ∧
    gsS.length = gs.length ∧
    ∀ (x y : List Bool), x.length = k → y.length = m →
      ∀ w < m + gs.length,
        (wiresOf gsS (x ++ y)).getD (k + w) false = (wiresOf gs y).getD w false := by
  intro gsS
  have hlen : gsS.length = gs.length := by simp [gsS]
  have hcost : costGates gsS = costGates gs := by
    unfold costGates
    simp only [gsS, List.countP_map, Function.comp_def, shiftGate, List.length_map]
    congr 1
    funext x
    exact decide_eq_decide.mpr Iff.rfl
  have hlegS : legalGates (k + m) gsS := by
    refine ⟨?_, ?_⟩
    · intro j hj i hi
      rw [hlen] at hj
      have hget : gateAt ⟨gsS, 0⟩ j = shiftGate k (gateAt ⟨gs, 0⟩ j) := by
        simp only [gateAt, gsS, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]
      rw [hget] at hi
      simp only [shiftGate, List.mem_map] at hi
      rcases hi with ⟨i0, hi0, rfl⟩
      have := hleg.1 j hj i0 hi0
      omega
    · intro h hh
      rcases List.mem_map.mp hh with ⟨g, hg, rfl⟩
      simpa [shiftGate] using hleg.2 g hg
  exact ⟨hlegS, hcost, hlen, fun x y hx hy => shiftGates_eval k m gs hleg x y hx hy⟩

def addDotAux {k : ℕ} (n wZero : ℕ) (coeff : Fin k → F2) (wireOf : Fin k → ℕ) :
    (m : ℕ) → m ≤ k → List Gate → List Gate × ℕ
  | 0, _, gs => (gs, wZero)
  | m + 1, hm, gs =>
    let res := addDotAux n wZero coeff wireOf m (by omega) gs
    if coeff ⟨m, hm⟩ = 1 then
      (res.1 ++ [⟨.mod 2, [res.2, wireOf ⟨m, hm⟩]⟩, ⟨.not, [n + res.1.length]⟩],
        n + res.1.length + 1)
    else res

lemma addDotAux_spec {k : ℕ} (n wZero : ℕ) (coeff : Fin k → F2) (wireOf : Fin k → ℕ) :
    ∀ (m : ℕ) (hm : m ≤ k) (gs : List Gate),
      legalGates n gs →
      wZero < n + gs.length →
      (∀ j : Fin k, wireOf j < n + gs.length) →
      let res := addDotAux n wZero coeff wireOf m hm gs
      ∃ ext : List Gate,
        res.1 = gs ++ ext ∧
        legalGates n res.1 ∧
        costGates res.1 = costGates gs ∧
        res.2 < n + res.1.length ∧
        ∀ (x : List Bool), x.length = n → (wiresOf gs x).getD wZero false = false →
          (wiresOf res.1 x).getD res.2 false =
            decide ((∑ j : Fin k, if j.val < m then coeff j * (if (wiresOf gs x).getD (wireOf j) false then (1 : F2) else 0) else 0) = 1) := by
  intro m
  induction m with
  | zero =>
    intro _ gs hleg hwz _
    refine ⟨[], by simp [addDotAux], hleg, rfl, hwz, fun x _ hz => ?_⟩
    simp only [addDotAux, Nat.not_lt_zero, ↓reduceIte, Finset.sum_const_zero]
    have h0 : decide ((0 : F2) = 1) = false := rfl
    rw [h0]
    exact hz
  | succ m ih =>
    intro hm gs hleg hwz hw
    rcases ih (by omega) gs hleg hwz hw with ⟨ext1, h1eq, h1leg, h1cost, h1lt, h1sem⟩
    set gs1 := (addDotAux n wZero coeff wireOf m (by omega) gs).1
    set w1 := (addDotAux n wZero coeff wireOf m (by omega) gs).2
    have hsum_step : ∀ x : List Bool,
        (∑ j : Fin k, if j.val < m + 1 then coeff j * (if (wiresOf gs x).getD (wireOf j) false then (1 : F2) else 0) else 0) =
        (∑ j : Fin k, if j.val < m then coeff j * (if (wiresOf gs x).getD (wireOf j) false then (1 : F2) else 0) else 0) +
        coeff ⟨m, hm⟩ * (if (wiresOf gs x).getD (wireOf ⟨m, hm⟩) false then (1 : F2) else 0) := by
      intro x
      have hpt : ∀ j : Fin k,
          (if j.val < m + 1 then coeff j * (if (wiresOf gs x).getD (wireOf j) false then (1 : F2) else 0) else 0) =
          (if j.val < m then coeff j * (if (wiresOf gs x).getD (wireOf j) false then (1 : F2) else 0) else 0) +
          (if j = ⟨m, hm⟩ then coeff j * (if (wiresOf gs x).getD (wireOf j) false then (1 : F2) else 0) else 0) := by
        intro j
        by_cases hj : j = ⟨m, hm⟩
        · subst hj; simp
        · have hne : j.val ≠ m := fun h => hj (Fin.ext h)
          by_cases hlt : j.val < m
          · have hlt1 : j.val < m + 1 := by omega
            simp [hj, hlt, hlt1]
          · have hlt1 : ¬ j.val < m + 1 := by omega
            simp [hj, hlt, hlt1]
      simp_rw [hpt, Finset.sum_add_distrib]
      simp
    by_cases hc : coeff ⟨m, hm⟩ = 1
    · have hstep := addXor_step n gs1 w1 (wireOf ⟨m, hm⟩) h1leg h1lt
        (by rw [h1eq, List.length_append]; have := hw ⟨m, hm⟩; omega)
      refine ⟨ext1 ++ [⟨.mod 2, [w1, wireOf ⟨m, hm⟩]⟩, ⟨.not, [n + gs1.length]⟩], ?_, ?_, ?_, ?_, ?_⟩
      · simp [addDotAux, hc, gs1, w1, h1eq, List.append_assoc]
      · simpa [addDotAux, hc, gs1, w1] using hstep.1
      · simpa [addDotAux, hc, gs1, w1, h1cost] using hstep.2.1
      · simp only [addDotAux, hc, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]; omega
      · intro x hx hz
        simp only [addDotAux, hc, ↓reduceIte]
        change (wiresOf (gs1 ++ [⟨.mod 2, [w1, wireOf ⟨m, hm⟩]⟩, ⟨.not, [n + gs1.length]⟩]) x).getD (n + gs1.length + 1) false = _
        rw [hstep.2.2.2 x hx, h1sem x hx hz, hsum_step x, hc, one_mul, zmod2_add_decide,
            h1eq, wiresOf_append_getD_lt gs ext1 x (by rw [hx]; exact hw ⟨m, hm⟩), zmod2_bool_decide]
    · have hc0 : coeff ⟨m, hm⟩ = 0 := by
        rcases zmod2_cases (coeff ⟨m, hm⟩) with h | h
        · exact h
        · exact absurd h hc
      refine ⟨ext1, ?_, ?_, ?_, ?_, ?_⟩
      · simp [addDotAux, hc, gs1, h1eq]
      · simpa [addDotAux, hc, gs1] using h1leg
      · simpa [addDotAux, hc, gs1] using h1cost
      · simpa [addDotAux, hc, gs1, w1] using h1lt
      · intro x hx hz
        simp only [addDotAux, hc, ↓reduceIte]
        rw [hsum_step x, hc0, zero_mul, add_zero]
        exact h1sem x hx hz

lemma addDot_full {k : ℕ} (n wZero : ℕ) (coeff : Fin k → F2) (wireOf : Fin k → ℕ)
    (gs : List Gate) (hleg : legalGates n gs) (hwz : wZero < n + gs.length)
    (hw : ∀ j : Fin k, wireOf j < n + gs.length) :
    let res := addDotAux n wZero coeff wireOf k (le_refl k) gs
    ∃ ext : List Gate,
      res.1 = gs ++ ext ∧
      legalGates n res.1 ∧
      costGates res.1 = costGates gs ∧
      res.2 < n + res.1.length ∧
      ∀ (x : List Bool), x.length = n → (wiresOf gs x).getD wZero false = false →
        (wiresOf res.1 x).getD res.2 false =
          decide (dotProduct coeff (fun j => if (wiresOf gs x).getD (wireOf j) false then (1 : F2) else 0) = 1) := by
  rcases addDotAux_spec n wZero coeff wireOf k (le_refl k) gs hleg hwz hw with ⟨ext, heq, hleg', hcost', hlt', hsem'⟩
  refine ⟨ext, heq, hleg', hcost', hlt', fun x hx hz => ?_⟩
  rw [hsem' x hx hz]
  congr 2
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro j _; simp [j.isLt]

lemma build_quad_sum {k t r : ℕ} (wZero : ℕ)
    (b ℓ : Fin r → (Fin k → F2)) (a : Fin k → F2) (wXP : Fin k → ℕ) :
    ∀ (m : ℕ) (hm : m ≤ r) (gs : List Gate),
      legalGates (2 * k + t) gs →
      wZero < 2 * k + t + gs.length →
      (∀ j : Fin k, wXP j < 2 * k + t + gs.length) →
      ∃ (ext : List Gate) (wAcc : ℕ),
        let gs' := gs ++ ext
        legalGates (2 * k + t) gs' ∧
        costGates gs' = costGates gs + m ∧
        wAcc < 2 * k + t + gs'.length ∧
        ∀ (x y : Fin k → F2) (z : Fin t → F2) (p : Fin k → F2),
          let inp := bitsOf k x ++ bitsOf k y ++ bitsOf t z
          (wiresOf gs inp).getD wZero false = false →
          (∀ j : Fin k, (wiresOf gs inp).getD (wXP j) false = decide ((x + p) j = 1)) →
          (wiresOf gs' inp).getD wAcc false =
            decide ((∑ i : Fin r, if i.val < m then dotProduct (x + p) (b i) * dotProduct (ℓ i) (y - a) else 0) = 1) := by
  intro m
  induction m with
  | zero =>
    intro _ gs hleg hwz _
    refine ⟨[], wZero, by simpa using hleg, by simp, by simpa using hwz, ?_⟩
    intro x y z p inp hz _
    simp only [List.append_nil, Nat.not_lt_zero, ↓reduceIte, Finset.sum_const_zero]
    have h0 : decide ((0 : F2) = 1) = false := rfl
    rw [h0]
    exact hz
  | succ m ih =>
    intro hm gs hleg hwz hwXP
    rcases ih (by omega) gs hleg hwz hwXP with ⟨ext1, wAcc1, h1leg, h1cost, h1lt, h1sem⟩
    set gs1 := gs ++ ext1
    have hlen1 : gs.length ≤ gs1.length := by simp [gs1]
    rcases addDot_full (2 * k + t) wZero (b ⟨m, hm⟩) wXP gs1 h1leg (by omega)
      (fun j => by have := hwXP j; omega) with ⟨extL, hLeq, hLleg, hLcost, hLlt, hLsem⟩
    set gsL := gs1 ++ extL
    set wL := (addDotAux (2 * k + t) wZero (b ⟨m, hm⟩) wXP k (le_refl k) gs1).2
    rw [hLeq] at hLleg hLcost hLlt
    have hlenL : gs1.length ≤ gsL.length := by simp [gsL]
    let yWire : Fin k → ℕ := fun j => k + j.val
    rcases addDot_full (2 * k + t) wZero (ℓ ⟨m, hm⟩) yWire gsL hLleg (by omega)
      (fun j => by simp [yWire]; omega) with ⟨extR0, hR0eq, hR0leg, hR0cost, hR0lt, hR0sem⟩
    set gsR0 := gsL ++ extR0
    set wR0 := (addDotAux (2 * k + t) wZero (ℓ ⟨m, hm⟩) yWire k (le_refl k) gsL).2
    rw [hR0eq] at hR0leg hR0cost hR0lt
    have hlenR0 : gsL.length ≤ gsR0.length := by simp [gsR0]
    let flipR : Bool := decide (dotProduct (ℓ ⟨m, hm⟩) a = 1)
    let extR1 : List Gate := if flipR then [⟨.not, [wR0]⟩] else []
    let gsR := gsR0 ++ extR1
    let wR := if flipR then 2 * k + t + gsR0.length else wR0
    have hRleg : legalGates (2 * k + t) gsR := by
      cases hf : flipR
      · simp only [gsR, extR1, hf, Bool.false_eq_true, ↓reduceIte, List.append_nil]; exact hR0leg
      · simp only [gsR, extR1, hf, ↓reduceIte]
        exact legalGates_snoc hR0leg (fun i hi => by simp at hi; subst hi; exact hR0lt)
          ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    have hRcost : costGates gsR = costGates gsR0 := by
      cases hf : flipR
      · simp [gsR, extR1, hf]
      · simp only [gsR, extR1, hf, ↓reduceIte]
        exact costGates_snoc_zero gsR0 ⟨.not, [wR0]⟩ (by simp)
    have hRlt : wR < 2 * k + t + gsR.length := by
      cases hf : flipR
      · simp only [gsR, extR1, wR, hf, Bool.false_eq_true, ↓reduceIte, List.append_nil]; exact hR0lt
      · simp [gsR, extR1, wR, hf]
    have hlenR : gsR0.length ≤ gsR.length := by simp [gsR]
    let gsAnd := gsR ++ [⟨.and, [wL, wR]⟩]
    let wAnd := 2 * k + t + gsR.length
    have hAndLeg : legalGates (2 * k + t) gsAnd :=
      legalGates_snoc hRleg (fun i hi => by simp at hi; rcases hi with rfl | rfl; omega; exact hRlt)
        ⟨by simp, Or.inl rfl⟩
    have hAndCost : costGates gsAnd = costGates gsR + 1 :=
      costGates_snoc_one gsR ⟨.and, [wL, wR]⟩ ⟨Or.inl rfl, rfl⟩
    have hstep := addXor_step (2 * k + t) gsAnd wAcc1 wAnd hAndLeg
      (by simp only [gsAnd, List.length_append, List.length_singleton]; omega)
      (by simp [gsAnd, wAnd])
    let extTot := ext1 ++ extL ++ extR0 ++ extR1 ++ [⟨.and, [wL, wR]⟩] ++ [⟨.mod 2, [wAcc1, wAnd]⟩, ⟨.not, [2 * k + t + gsAnd.length]⟩]
    have hgs_eq : gs ++ extTot = gsAnd ++ [⟨.mod 2, [wAcc1, wAnd]⟩, ⟨.not, [2 * k + t + gsAnd.length]⟩] := by
      simp [extTot, gsAnd, gsR, gsR0, gsL, gs1, List.append_assoc]
    refine ⟨extTot, 2 * k + t + gsAnd.length + 1, ?_, ?_, ?_, ?_⟩
    · rw [hgs_eq]; exact hstep.1
    · rw [hgs_eq, hstep.2.1, hAndCost, hRcost, hR0cost, hLcost, h1cost]; omega
    · rw [hgs_eq, hstep.2.2.1]; omega
    · intro x y z p inp hz hxp
      have hinp_len : inp.length = 2 * k + t := by simp [inp, bitsOf_len]; omega
      have hz1 : (wiresOf gs1 inp).getD wZero false = false := by
        rw [wiresOf_append_getD_lt gs ext1 inp (by rw [hinp_len]; exact hwz)]; exact hz
      have hzL : (wiresOf gsL inp).getD wZero false = false := by
        rw [wiresOf_append_getD_lt gs1 extL inp (by rw [hinp_len]; omega)]; exact hz1
      rw [hgs_eq, hstep.2.2.2 inp hinp_len]
      have hacc1_val : (wiresOf gsAnd inp).getD wAcc1 false =
          decide ((∑ i : Fin r, if i.val < m then dotProduct (x + p) (b i) * dotProduct (ℓ i) (y - a) else 0) = 1) := by
        have heq1 : gsAnd = gs1 ++ (extL ++ extR0 ++ extR1 ++ [⟨.and, [wL, wR]⟩]) := by
          simp [gsAnd, gsR, gsR0, gsL, List.append_assoc]
        rw [heq1, wiresOf_append_getD_lt gs1 _ inp (by rw [hinp_len]; exact h1lt)]
        exact h1sem x y z p hz hxp
      have hL_val : (wiresOf gsR inp).getD wL false = decide (dotProduct (x + p) (b ⟨m, hm⟩) = 1) := by
        have heqL : gsR = gsL ++ (extR0 ++ extR1) := by simp [gsR, gsR0, List.append_assoc]
        rw [heqL, wiresOf_append_getD_lt gsL _ inp (by rw [hinp_len]; exact hLlt)]
        have hs := hLsem inp hinp_len hz1
        rw [hLeq] at hs; rw [hs]
        congr 2
        rw [dotProduct_comm]
        congr 1
        funext j
        rw [wiresOf_append_getD_lt gs ext1 inp (by rw [hinp_len]; exact hwXP j), hxp j, zmod2_decide_bool]
      have hR_val : (wiresOf gsR inp).getD wR false = decide (dotProduct (ℓ ⟨m, hm⟩) (y - a) = 1) := by
        have hR0_val : (wiresOf gsR0 inp).getD wR0 false = decide (dotProduct (ℓ ⟨m, hm⟩) y = 1) := by
          have hs := hR0sem inp hinp_len hzL
          rw [hR0eq] at hs; rw [hs]
          congr 2; congr 1; funext j
          have hwy : (wiresOf gsL inp).getD (yWire j) false = decide (y j = 1) := by
            rw [wiresOf_getD_lt gsL inp (by rw [hinp_len]; simp [yWire]; omega)]
            simp only [inp, yWire, List.append_assoc]
            rw [List.getD_eq_getElem?_getD,
                List.getElem?_append_right (by rw [bitsOf_len]; omega),
                bitsOf_len, Nat.add_sub_cancel_left,
                List.getElem?_append_left (by rw [bitsOf_len]; exact j.isLt)]
            exact bitsOf_getD k y j
          rw [hwy, zmod2_decide_bool]
        rw [zmod2_vec_sub_eq_add, dotProduct_add, zmod2_add_decide]
        cases hf : flipR
        · have hf0 : decide (dotProduct (ℓ ⟨m, hm⟩) a = 1) = false := hf
          simp only [gsR, extR1, wR, hf, Bool.false_eq_true, ↓reduceIte, List.append_nil, hR0_val, hf0, Bool.xor_false]
        · have hf1 : decide (dotProduct (ℓ ⟨m, hm⟩) a = 1) = true := hf
          simp only [gsR, extR1, wR, hf, ↓reduceIte]
          rw [wiresOf_snoc_last_eq gsR0 ⟨.not, [wR0]⟩ inp hinp_len]
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, hR0_val, hf1, Bool.xor_true]
      have hAnd_val : (wiresOf gsAnd inp).getD wAnd false =
          decide (dotProduct (x + p) (b ⟨m, hm⟩) * dotProduct (ℓ ⟨m, hm⟩) (y - a) = 1) := by
        rw [wiresOf_snoc_last_eq gsR ⟨.and, [wL, wR]⟩ inp hinp_len]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq,
          Bool.and_true, hL_val, hR_val, zmod2_mul_decide]
      rw [hacc1_val, hAnd_val, ← zmod2_add_decide]
      congr 2
      have hpt : ∀ i : Fin r,
          (if i.val < m + 1 then dotProduct (x + p) (b i) * dotProduct (ℓ i) (y - a) else 0) =
          (if i.val < m then dotProduct (x + p) (b i) * dotProduct (ℓ i) (y - a) else 0) +
          (if i = ⟨m, hm⟩ then dotProduct (x + p) (b i) * dotProduct (ℓ i) (y - a) else 0) := by
        intro i
        by_cases hi : i = ⟨m, hm⟩
        · subst hi; simp
        · have hne : i.val ≠ m := fun h => hi (Fin.ext h)
          by_cases hlt : i.val < m
          · have hlt1 : i.val < m + 1 := by omega
            simp [hi, hlt, hlt1]
          · have hlt1 : ¬ i.val < m + 1 := by omega
            simp [hi, hlt, hlt1]
      simp_rw [hpt, Finset.sum_add_distrib]
      simp

lemma build_xp_wires (k t : ℕ) (tap : Fin k → ℕ) :
    ∀ (m : ℕ) (hm : m ≤ k) (gs : List Gate),
      legalGates (2 * k + t) gs →
      (∀ j : Fin k, k + tap j < 2 * k + t + gs.length) →
      ∃ (ext : List Gate) (wXP : ℕ → ℕ),
        let gs' := gs ++ ext
        legalGates (2 * k + t) gs' ∧
        costGates gs' = costGates gs ∧
        (∀ j < m, wXP j < 2 * k + t + gs'.length) ∧
        ∀ (j : Fin k), j.val < m → ∀ (x y : Fin k → F2) (z : Fin t → F2) (p : Fin k → F2),
          let inp := bitsOf k x ++ bitsOf k y ++ bitsOf t z
          (wiresOf gs inp).getD (k + tap j) false = decide (p j = 1) →
          (wiresOf gs' inp).getD (wXP j.val) false = decide ((x + p) j = 1) := by
  intro m
  induction m with
  | zero =>
    intro _ gs hleg _
    exact ⟨[], fun _ => 0, by simpa using hleg, by simp, fun _ h => by omega, fun _ h => by omega⟩
  | succ m ih =>
    intro hm gs hleg htap
    rcases ih (by omega) gs hleg htap with ⟨ext1, wXP1, h1leg, h1cost, h1lt, h1sem⟩
    set gs1 := gs ++ ext1
    have hstep := addXor_step (2 * k + t) gs1 m (k + tap ⟨m, hm⟩) h1leg
      (by omega) (by simp only [gs1, List.length_append]; have := htap ⟨m, hm⟩; omega)
    let extTot := ext1 ++ [⟨.mod 2, [m, k + tap ⟨m, hm⟩]⟩, ⟨.not, [2 * k + t + gs1.length]⟩]
    have hgs_eq : gs ++ extTot = gs1 ++ [⟨.mod 2, [m, k + tap ⟨m, hm⟩]⟩, ⟨.not, [2 * k + t + gs1.length]⟩] := by
      simp [extTot, gs1, List.append_assoc]
    refine ⟨extTot, fun u => if u = m then 2 * k + t + gs1.length + 1 else wXP1 u, ?_, ?_, ?_, ?_⟩
    · rw [hgs_eq]; exact hstep.1
    · rw [hgs_eq, hstep.2.1, h1cost]
    · intro u hu
      rw [hgs_eq, hstep.2.2.1]
      by_cases hum : u = m
      · subst hum; simp only [↓reduceIte]; omega
      · simp only [hum, ↓reduceIte]; have := h1lt u (by omega); omega
    · intro j hj x y z p inp hpj
      have hinp_len : inp.length = 2 * k + t := by simp [inp, bitsOf_len]; omega
      rw [hgs_eq]
      by_cases hjm : j.val = m
      · simp only [hjm, ↓reduceIte]
        rw [hstep.2.2.2 inp hinp_len]
        have hx_val : (wiresOf gs1 inp).getD m false = decide (x j = 1) := by
          rw [wiresOf_getD_lt gs1 inp (by rw [hinp_len]; omega)]
          have hjeq : (⟨m, hm⟩ : Fin k) = j := Fin.ext hjm.symm
          rw [← hjeq]
          simp only [inp, List.append_assoc]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [bitsOf_len]; exact hm)]
          exact bitsOf_getD k x ⟨m, hm⟩
        have hp_val : (wiresOf gs1 inp).getD (k + tap ⟨m, hm⟩) false = decide (p j = 1) := by
          have hjeq : (⟨m, hm⟩ : Fin k) = j := Fin.ext hjm.symm
          rw [hjeq, wiresOf_append_getD_lt gs ext1 inp (by rw [hinp_len]; exact htap j)]
          exact hpj
        rw [hx_val, hp_val, Pi.add_apply, zmod2_add_decide]
      · simp only [hjm, ↓reduceIte]
        rw [wiresOf_append_getD_lt gs1 _ inp (by rw [hinp_len]; exact h1lt j.val (by omega))]
        exact h1sem j (by omega) x y z p hpj

end Part844


section Main844

open Classical

lemma main_844 :
∀ (k t : ℕ),
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
  let Z := Fin t → F
  let sign := fun (b : Bool) => if b then (-1 : ℤ) else 1
  let prof := fun (C : Circ) (y : V) (z : Z) =>
    ∑ x : V, sign (Bool.xor (C.eval (bits k x ++ bits k y ++ bits t z)) (decide (dotProduct x y = 1)))
  ∀ s : ℕ,
    let atom := fun (r : ℕ) (A : V → Z → ℤ) =>
      ∃ (W : Submodule F V) (a : V) (D : Circ) (tap : Fin k → ℕ),
        Module.finrank F W = r ∧ legal (k+t) D ∧ cost D + r ≤ s ∧
        D.output < k+t+D.size ∧ (∀ j, tap j < k+t+D.size) ∧
        ∀ (y : V) (z : Z),
          let inp := bits k y ++ bits t z
          let p := fun j : Fin k => if (D.wires inp).getD (tap j) false then (1 : F) else 0
          (y-a ∈ W → A y z = sign (Bool.xor (D.eval inp) (decide (dotProduct p y = 1)))) ∧
            (y-a ∉ W → A y z = 0)
    (∀ C : Circ, legal (2*k+t) C → cost C ≤ s →
      ∃ (N : ℕ) (r : Fin N → ℕ) (A : Fin N → V → Z → ℤ),
        (∀ i, atom (r i) (A i)) ∧ (∑ i, 2^(k-r i) : ℕ) = 2^k ∧
        ∀ y z, prof C y z = ∑ i, (2 : ℤ)^(k-r i) * A i y z) ∧
    (∀ (r : ℕ) (A : V → Z → ℤ), atom r A →
      ∃ C : Circ, legal (2*k+t) C ∧ cost C ≤ s ∧
        ∀ y z, prof C y z = (2 : ℤ)^k * A y z) := by
  intro k t Circ F legal cost bits V Z sign prof s atom
  constructor
  · intro C hC hcostC
    have hkt : 2 * k + t = k + (k + t) := by omega
    have hC' : legal (k + (k + t)) C := hkt ▸ hC
    rcases l835_main k (k + t) C hC' with ⟨N, r, U, a, D, tap, hNpos, hDprops, hpart, heval⟩
    let W : Fin N → Submodule F2 V := fun i => orthComp (U i)
    let posOf : Fin N → V → Z → V := fun i y z j =>
      if ((D i).wires (bits k y ++ bits t z)).getD (tap i j) false then (1 : F2) else 0
    let A : Fin N → V → Z → ℤ := fun i y z =>
      if y - a i ∈ W i then
        signB (Bool.xor ((D i).eval (bits k y ++ bits t z)) (decide (dotProduct (posOf i y z) y = 1)))
      else 0
    have hfinW : ∀ i : Fin N, Module.finrank F2 (W i) = r i := by
      intro i
      have h1 := finrank_orthComp (U i)
      have h2 : Module.finrank F2 (U i) + r i = k := (hDprops i).1
      exact Nat.add_right_cancel (h1.trans (h2.symm.trans (Nat.add_comm _ _)))
    have hfinU : ∀ i : Fin N, Module.finrank F2 (U i) = k - r i := by
      intro i
      have h2 : Module.finrank F2 (U i) + r i = k := (hDprops i).1
      omega
    have hpos_app : ∀ (i : Fin N) (y : V) (z : Z),
        (fun j : Fin k => if ((D i).wires (bits (k + t) (Fin.append y z))).getD (tap i j) false then (1 : F2) else 0) =
        posOf i y z := by
      intro i y z; funext j
      have hba : bits k y ++ bits t z = bits (k + t) (Fin.append y z) := bitsOf_append y z
      simp only [posOf, ← hba]
    let hpart_equiv : ∀ (y : V) (z : Z), ((i : Fin N) × U i) ≃ V := fun y z =>
      { toFun := fun p => posOf p.1 y z + p.2.val
        invFun := fun x =>
          have hex := hpart (Fin.append y z) x
          let i0 := hex.choose
          have hi0 : x - posOf i0 y z ∈ U i0 := by
            have hs : x - (fun j : Fin k => if ((D i0).wires (bits (k + t) (Fin.append y z))).getD (tap i0 j) false then (1 : F2) else 0) ∈ U i0 :=
              hex.choose_spec.1
            rwa [hpos_app i0 y z] at hs
          ⟨i0, ⟨x - posOf i0 y z, hi0⟩⟩
        left_inv := by
          rintro ⟨i, ⟨u, hu⟩⟩
          have hex := hpart (Fin.append y z) (posOf i y z + u)
          have hmem : (posOf i y z + u) - posOf i y z ∈ U i := by
            rw [zmod2_vec_sub_eq_add, add_comm (posOf i y z) u, add_assoc, zmod2_vec_add_self, add_zero]
            exact hu
          have hmem' : (posOf i y z + u) - (fun j : Fin k => if ((D i).wires (bits (k + t) (Fin.append y z))).getD (tap i j) false then (1 : F2) else 0) ∈ U i := by
            rwa [hpos_app i y z]
          have hi_eq : hex.choose = i := (hex.choose_spec.2 i hmem').symm
          have hsig : ∀ (i1 i2 : Fin N) (h : i1 = i2) (x1 : U i1) (x2 : U i2),
              x1.val = x2.val → (⟨i1, x1⟩ : (j : Fin N) × U j) = ⟨i2, x2⟩ := by
            rintro i1 _ rfl ⟨v1, h1⟩ ⟨v2, h2⟩ hv; dsimp at hv; subst hv; rfl
          dsimp only
          exact hsig _ _ hi_eq _ _ (by
            dsimp only
            rw [hi_eq, zmod2_vec_sub_eq_add, add_comm (posOf i y z) u, add_assoc, zmod2_vec_add_self, add_zero])
        right_inv := by
          intro x
          dsimp only
          rw [zmod2_vec_sub_eq_add, add_comm x, ← add_assoc, zmod2_vec_add_self, zero_add] }
    refine ⟨N, r, A, ?_, ?_, ?_⟩
    · intro i
      refine ⟨W i, a i, D i, tap i, hfinW i, (hDprops i).2.1, le_trans (hDprops i).2.2.1 hcostC,
        (hDprops i).2.2.2.1, (hDprops i).2.2.2.2, fun y z => ⟨fun hy => ?_, fun hy => ?_⟩⟩
      · simp only [A, hy, ↓reduceIte, sign, signB, posOf]
      · simp only [A, hy, ↓reduceIte]
    · have hcard := Fintype.card_congr (hpart_equiv 0 0)
      rw [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin, ZMod.card] at hcard
      rw [← hcard]
      apply Finset.sum_congr rfl
      intro i _
      rw [card_submodule_eq_pow (U i), hfinU i]
    · intro y z
      change (∑ x : V, signB (Bool.xor (C.eval (bits k x ++ bits k y ++ bits t z)) (decide (dotProduct x y = 1)))) = _
      rw [← Fintype.sum_equiv (hpart_equiv y z) _ _ (fun _ => rfl)]
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      have hterm : ∀ u : U i,
          signB (Bool.xor (C.eval (bits k (posOf i y z + u.val) ++ bits k y ++ bits t z))
            (decide (dotProduct (posOf i y z + u.val) y = 1))) =
          signB (Bool.xor ((D i).eval (bits k y ++ bits t z)) (decide (dotProduct (posOf i y z) y = 1))) *
            signB (decide (dotProduct (y - a i) u.val = 1)) := by
        intro u
        have hev : C.eval (bits k ((fun j : Fin k => if ((D i).wires (bits (k + t) (Fin.append y z))).getD (tap i j) false then (1 : F2) else 0) + u.val) ++ bits (k + t) (Fin.append y z)) =
            Bool.xor ((D i).eval (bits (k + t) (Fin.append y z))) (decide (dotProduct (a i) u.val = 1)) :=
          heval i (Fin.append y z) u.val u.property
        have hba : bits k y ++ bits t z = bits (k + t) (Fin.append y z) := bitsOf_append y z
        rw [hpos_app i y z] at hev
        have hbits : bits k (posOf i y z + u.val) ++ bits k y ++ bits t z =
            bits k (posOf i y z + u.val) ++ bits (k + t) (Fin.append y z) := by
          rw [List.append_assoc, hba]
        have hev' : C.eval (bits k (posOf i y z + u.val) ++ bits k y ++ bits t z) =
            Bool.xor ((D i).eval (bits k y ++ bits t z)) (decide (dotProduct (a i) u.val = 1)) := by
          rw [hbits, hba]; exact hev
        rw [hev', add_dotProduct, zmod2_add_decide, zmod2_vec_sub_eq_add, add_dotProduct,
            dotProduct_comm u.val y, zmod2_add_decide]
        cases (D i).eval (bits k y ++ bits t z) <;>
          cases decide (dotProduct (a i) u.val = 1) <;>
          cases decide (dotProduct (posOf i y z) y = 1) <;>
          cases decide (dotProduct y u.val = 1) <;> decide
      change (∑ u : U i, signB (Bool.xor (C.eval (bits k (posOf i y z + u.val) ++ bits k y ++ bits t z))
        (decide (dotProduct (posOf i y z + u.val) y = 1)))) = _
      rw [Finset.sum_congr rfl (fun u _ => hterm u), ← Finset.mul_sum]
      have hss := sum_sign_submodule (U i) (y - a i)
      change (∑ u : U i, signB (decide (dotProduct (y - a i) u.val = 1))) = _ at hss
      rw [hss, hfinU i]
      by_cases hy : y - a i ∈ W i
      · have hy' : y - a i ∈ orthComp (U i) := hy
        simp only [A, hy, hy', ↓reduceIte]
        ring
      · have hy' : y - a i ∉ orthComp (U i) := hy
        simp only [A, hy, hy', ↓reduceIte, mul_zero]
  · intro r A ⟨W, a, D, tap, hfinW, hlegD, hcostD, houtD, htapD, hA⟩
    rcases exists_proj_basis W hfinW with ⟨b, ℓ, hbW, hproj⟩
    have hshift := shiftGates_spec k (k + t) D.gates hlegD
    set gs0 := D.gates.map (shiftGate k)
    have hkt : k + (k + t) = 2 * k + t := by omega
    have hleg0 : legalGates (2 * k + t) gs0 := hkt ▸ hshift.1
    have hcost0 : costGates gs0 = costGates D.gates := hshift.2.1
    have hlen0 : gs0.length = D.gates.length := hshift.2.2.1
    let gs1 := gs0 ++ [⟨.or, []⟩]
    let wZero := 2 * k + t + gs0.length
    have hleg1 : legalGates (2 * k + t) gs1 :=
      legalGates_snoc hleg0 (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
    have hcost1 : costGates gs1 = costGates D.gates := by
      rw [costGates_snoc_zero gs0 ⟨.or, []⟩ (by simp), hcost0]
    have hwz1 : wZero < 2 * k + t + gs1.length := by simp [gs1, wZero]
    rcases build_xp_wires k t tap k (le_refl k) gs1 hleg1
      (fun j => by simp only [gs1, List.length_append, List.length_singleton, hlen0]; have := htapD j; simp [Circuit.size] at this; omega)
      with ⟨extXP, wXPnat, hleg2, hcost2, hwXPlt, hXPsem⟩
    set gs2 := gs1 ++ extXP
    let wXP : Fin k → ℕ := fun j => wXPnat j.val
    rcases addDot_full (2 * k + t) wZero a wXP gs2 hleg2
      (by simp only [gs2, List.length_append]; omega)
      (fun j => hwXPlt j.val j.isLt) with ⟨extA, hAeq, hleg3, hcost3, wAlt, hAsem⟩
    set gs3 := gs2 ++ extA
    set wLinA := (addDotAux (2 * k + t) wZero a wXP k (le_refl k) gs2).2
    rw [hAeq] at hleg3 hcost3 wAlt
    rcases build_quad_sum wZero b ℓ a wXP r (le_refl r) gs3 hleg3
      (by simp only [gs3, gs2, List.length_append]; omega)
      (fun j => by simp only [wXP, gs3, List.length_append]; have := hwXPlt j.val j.isLt; omega)
      with ⟨extQ, wAcc, hleg4, hcost4, wAcclt, hQsem⟩
    set gs4 := gs3 ++ extQ
    have hstep1 := addXor_step (2 * k + t) gs4 (k + D.output) wLinA hleg4
      (by simp only [gs4, gs3, gs2, gs1, List.length_append, List.length_singleton, hlen0]; simp [Circuit.size] at houtD; omega)
      (by simp only [gs4, List.length_append]; omega)
    set gs5 := gs4 ++ [⟨.mod 2, [k + D.output, wLinA]⟩, ⟨.not, [2 * k + t + gs4.length]⟩]
    set w5 := 2 * k + t + gs4.length + 1
    have hstep2 := addXor_step (2 * k + t) gs5 w5 wAcc hstep1.1
      (by rw [hstep1.2.2.1]; omega)
      (by rw [hstep1.2.2.1]; omega)
    set gs6 := gs5 ++ [⟨.mod 2, [w5, wAcc]⟩, ⟨.not, [2 * k + t + gs5.length]⟩]
    set wOut := 2 * k + t + gs5.length + 1
    let C : Circ := ⟨gs6, wOut⟩
    refine ⟨C, hstep2.1, ?_, ?_⟩
    · change costGates gs6 ≤ s
      rw [hstep2.2.1, hstep1.2.1, hcost4, hcost3, hcost2, hcost1]
      exact hcostD
    · intro y z
      let inpYZ := bits k y ++ bits t z
      let p : V := fun j => if (D.wires inpYZ).getD (tap j) false then (1 : F2) else 0
      let P : V → V := fun v => ∑ i : Fin r, (dotProduct (ℓ i) v) • b i
      have hCeval : ∀ x : V,
          C.eval (bits k x ++ bits k y ++ bits t z) =
            Bool.xor (D.eval inpYZ) (decide (dotProduct (x + p) (a + P (y - a)) = 1)) := by
        intro x
        set inp := bits k x ++ bits k y ++ bits t z
        have hinp_len : inp.length = 2 * k + t := by simp [inp, bits]; omega
        have hinpYZ_len : inpYZ.length = k + t := by simp [inpYZ, bits]
        have hshift_eval : ∀ w < k + t + D.gates.length,
            (wiresOf gs0 inp).getD (k + w) false = (wiresOf D.gates inpYZ).getD w false := by
          intro w hw
          have heq_in : inp = bits k x ++ inpYZ := by simp [inp, inpYZ, List.append_assoc]
          rw [heq_in]
          exact hshift.2.2.2 (bits k x) inpYZ (by simp [bits]) hinpYZ_len w hw
        have hz1 : (wiresOf gs1 inp).getD wZero false = false := by
          have := wiresOf_snoc_last_eq gs0 ⟨.or, []⟩ inp hinp_len
          simpa [gs1, wZero, GateOp.eval] using this
        have htap1 : ∀ j : Fin k, (wiresOf gs1 inp).getD (k + tap j) false = decide (p j = 1) := by
          intro j
          have htj : tap j < k + t + D.gates.length := by simpa [Circuit.size] using htapD j
          rw [wiresOf_append_getD_lt gs0 [⟨.or, []⟩] inp (by rw [hinp_len, hlen0]; omega),
              hshift_eval (tap j) htj]
          simp only [p, wiresOf]
          exact (zmod2_bool_decide _).symm
        have hxp2 : ∀ j : Fin k, (wiresOf gs2 inp).getD (wXP j) false = decide ((x + p) j = 1) := by
          intro j
          exact hXPsem j j.isLt x y z p (htap1 j)
        have hz2 : (wiresOf gs2 inp).getD wZero false = false := by
          rw [wiresOf_append_getD_lt gs1 extXP inp (by rw [hinp_len]; exact hwz1)]; exact hz1
        have hz3 : (wiresOf gs3 inp).getD wZero false = false := by
          rw [wiresOf_append_getD_lt gs2 extA inp (by rw [hinp_len]; simp only [gs2, List.length_append]; omega)]; exact hz2
        have hxp3 : ∀ j : Fin k, (wiresOf gs3 inp).getD (wXP j) false = decide ((x + p) j = 1) := by
          intro j
          rw [wiresOf_append_getD_lt gs2 extA inp (by rw [hinp_len]; exact hwXPlt j.val j.isLt)]
          exact hxp2 j
        have hD4 : (wiresOf gs4 inp).getD (k + D.output) false = D.eval inpYZ := by
          have hgs4_eq : gs4 = gs0 ++ ([⟨.or, []⟩] ++ extXP ++ extA ++ extQ) := by
            simp [gs4, gs3, gs2, gs1, List.append_assoc]
          have hdo : D.output < k + t + D.gates.length := by simpa [Circuit.size] using houtD
          rw [hgs4_eq, wiresOf_append_getD_lt gs0 _ inp (by rw [hinp_len, hlen0]; omega),
              hshift_eval D.output hdo]
          rfl
        have hLinA4 : (wiresOf gs4 inp).getD wLinA false = decide (dotProduct (x + p) a = 1) := by
          rw [wiresOf_append_getD_lt gs3 extQ inp (by rw [hinp_len]; exact wAlt)]
          have hs := hAsem inp hinp_len hz2
          rw [hAeq] at hs; rw [hs]
          congr 2; rw [dotProduct_comm]; congr 1; funext j
          rw [hxp2 j, zmod2_decide_bool]
        have hAcc5 : (wiresOf gs5 inp).getD wAcc false =
            decide (dotProduct (x + p) (P (y - a)) = 1) := by
          rw [wiresOf_append_getD_lt gs4 _ inp (by rw [hinp_len]; exact wAcclt)]
          have hq := hQsem x y z p hz3 hxp3
          change (wiresOf gs4 inp).getD wAcc false = _ at hq
          rw [hq]
          congr 2
          change (∑ i : Fin r, if i.val < r then dotProduct (x + p) (b i) * dotProduct (ℓ i) (y - a) else 0) =
            dotProduct (x + p) (∑ i : Fin r, (dotProduct (ℓ i) (y - a)) • b i)
          rw [dotProduct_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [dotProduct_smul, smul_eq_mul]
          simp only [i.isLt, ↓reduceIte]
          exact mul_comm _ _
        change (wiresOf gs6 inp).getD wOut false = _
        rw [hstep2.2.2.2 inp hinp_len, hstep1.2.2.2 inp hinp_len, hD4, hLinA4, hAcc5]
        rw [dotProduct_add, zmod2_add_decide]
        cases D.eval inpYZ <;> cases decide (dotProduct (x + p) a = 1) <;>
          cases decide (dotProduct (x + p) (P (y - a)) = 1) <;> decide
      change (∑ x : V, signB (Bool.xor (C.eval (bits k x ++ bits k y ++ bits t z)) (decide (dotProduct x y = 1)))) = _
      have hterm : ∀ x : V,
          signB (Bool.xor (C.eval (bits k x ++ bits k y ++ bits t z)) (decide (dotProduct x y = 1))) =
          signB (Bool.xor (D.eval inpYZ) (decide (dotProduct p (a + P (y - a)) = 1))) *
            signB (decide (dotProduct x (y - (a + P (y - a))) = 1)) := by
        intro x
        set q := a + P (y - a)
        have h1 : dotProduct (x + p) q = dotProduct x q + dotProduct p q := add_dotProduct x p q
        have h2 : dotProduct x (y - q) = dotProduct x y + dotProduct x q := by
          rw [zmod2_vec_sub_eq_add, dotProduct_add]
        rw [hCeval x, h1, h2, zmod2_add_decide, zmod2_add_decide]
        cases D.eval inpYZ <;> cases decide (dotProduct x q = 1) <;>
          cases decide (dotProduct p q = 1) <;> cases decide (dotProduct x y = 1) <;> rfl
      rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
      have hsu := sum_sign_univ (y - (a + P (y - a)))
      change (∑ x : V, signB (decide (dotProduct x (y - (a + P (y - a))) = 1))) = _ at hsu
      rw [hsu]
      have hPW : P (y - a) ∈ W := Submodule.sum_mem W (fun i _ => W.smul_mem _ (hbW i))
      by_cases hy : y - a ∈ W
      · have hPy : P (y - a) = y - a := hproj (y - a) hy
        have haP : a + P (y - a) = y := by
          rw [hPy, zmod2_vec_sub_eq_add, add_comm y a, ← add_assoc, zmod2_vec_add_self, zero_add]
        rw [haP, sub_self]
        simp only [↓reduceIte]
        rw [(hA y z).1 hy]
        simp only [sign, signB, inpYZ, p]
        ring
      · have hdiffne : y - (a + P (y - a)) ≠ 0 := by
          intro h0
          have heq : y - a = P (y - a) := by
            rw [zmod2_vec_sub_eq_add] at h0
            have h1 := congrArg (· + (a + P (y - a))) h0
            rw [add_assoc, zmod2_vec_add_self, add_zero, zero_add] at h1
            have h2 := congrArg (· + a) h1
            rw [add_comm a (P (y - a)), add_assoc, zmod2_vec_add_self, add_zero] at h2
            exact (zmod2_vec_sub_eq_add y a).trans h2
          exact hy (heq ▸ hPW)
        simp only [hdiffne, ↓reduceIte, mul_zero]
        rw [(hA y z).2 hy, mul_zero]

end Main844


section Part33624

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

private def b2f3 (b : Bool) : F2 := if b then 1 else 0

private lemma b2f3_false : b2f3 false = 0 := rfl
private lemma b2f3_true : b2f3 true = 1 := rfl
private lemma b2f3_decide (a : F2) : b2f3 (decide (a = 1)) = a := by
  rcases zmod2_cases a with rfl | rfl <;> rfl
private lemma b2f3_xor (a b : Bool) : b2f3 (Bool.xor a b) = b2f3 a + b2f3 b := by
  cases a <;> cases b <;> decide
private lemma b2f3_not (a : Bool) : b2f3 (!a) = 1 + b2f3 a := by
  cases a <;> decide
private lemma b2f3_and (a b : Bool) : b2f3 (a && b) = b2f3 a * b2f3 b := by
  cases a <;> cases b <;> decide
private lemma b2f3_or (a b : Bool) : b2f3 (a || b) = b2f3 a + b2f3 b + b2f3 a * b2f3 b := by
  cases a <;> cases b <;> decide
private lemma f2_add_self (a : F2) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide
private lemma f2_mul_self (a : F2) : a * a = a := by
  rcases zmod2_cases a with rfl | rfl <;> decide
private lemma f2_ne_zero_eq_one {a : F2} (h : a ≠ 0) : a = 1 := by
  rcases zmod2_cases a with rfl | rfl
  · exact absurd rfl h
  · rfl
private lemma f2_eq_iff_add_zero (a b : F2) : a = b ↔ a + b = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

private def sign3 (b : Bool) : ℤ := if b then (-1 : ℤ) else 1

private lemma sign3_eq_iff (b c : Bool) : sign3 b = sign3 c ↔ b = c := by
  cases b <;> cases c <;> decide

private lemma sum_weighted_eq_extreme {ι : Type*} [Fintype ι] (w a : ι → ℤ) (s : ℤ)
    (hw : ∀ i, 0 < w i) (ha : ∀ i, a i = -1 ∨ a i = 0 ∨ a i = 1) (hs : s = 1 ∨ s = -1)
    (heq : ∑ i : ι, w i * a i = (∑ i : ι, w i) * s) :
    ∀ i, a i = s := by
  rcases hs with rfl | rfl
  · have hle : ∀ i ∈ (Finset.univ : Finset ι), w i * a i ≤ w i := by
      intro i _
      have hwi := hw i
      rcases ha i with h | h | h <;> rw [h] <;> nlinarith
    have hsum : ∑ i ∈ (Finset.univ : Finset ι), w i * a i = ∑ i ∈ (Finset.univ : Finset ι), w i := by
      simpa using heq
    have hall := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
    intro i
    have hi := hall i (Finset.mem_univ i)
    have hwi := hw i
    rcases ha i with h | h | h <;> rw [h] at hi ⊢ <;> nlinarith
  · have hle : ∀ i ∈ (Finset.univ : Finset ι), -w i ≤ w i * a i := by
      intro i _
      have hwi := hw i
      rcases ha i with h | h | h <;> rw [h] <;> nlinarith
    have hsum : ∑ i ∈ (Finset.univ : Finset ι), -w i = ∑ i ∈ (Finset.univ : Finset ι), w i * a i := by
      rw [Finset.sum_neg_distrib, heq]; ring
    have hall := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
    intro i
    have hi := hall i (Finset.mem_univ i)
    have hwi := hw i
    rcases ha i with h | h | h <;> rw [h] at hi ⊢ <;> nlinarith

private def basisVec {k : ℕ} (i : Fin k) : Fin k → F2 := fun j => if j = i then (1 : F2) else 0

private def isKey {k : ℕ} (G : SimpleGraph (Fin k)) (z : Fin k → F2) : Prop :=
  z = 0 ∨ (∃ i, z = basisVec i) ∨ ∃ i j, G.Adj i j ∧ z = basisVec i + basisVec j

private lemma submodule_eq_top_of_key {k : ℕ} (G : SimpleGraph (Fin k))
    (W : Submodule F2 (Fin (k + 1) → F2)) (a : Fin (k + 1) → F2)
    (hmem : ∀ (v : F2) (z : Fin k → F2), isKey G z → Fin.cons v z - a ∈ W) :
    W = ⊤ := by
  have h0 : (0 : Fin (k + 1) → F2) - a ∈ W := by
    have h := hmem 0 0 (Or.inl rfl)
    have hcons : (Fin.cons (0 : F2) (0 : Fin k → F2) : Fin (k + 1) → F2) = 0 := by
      funext m; cases m using Fin.cases <;> rfl
    rwa [hcons] at h
  have ha : a ∈ W := by
    have h1 := W.neg_mem h0
    simpa using h1
  have hin : ∀ (v : F2) (z : Fin k → F2), isKey G z → Fin.cons v z ∈ W := by
    intro v z hz
    have h1 := W.add_mem (hmem v z hz) ha
    simpa [sub_add_cancel] using h1
  have hsing : ∀ m : Fin (k + 1), Pi.single m (1 : F2) ∈ W := by
    intro m
    cases m using Fin.cases with
    | zero =>
      have h1 := hin 1 0 (Or.inl rfl)
      have heq : (Fin.cons (1 : F2) (0 : Fin k → F2) : Fin (k + 1) → F2) = Pi.single (0 : Fin (k + 1)) (1 : F2) := by
        funext j; cases j using Fin.cases <;> simp [Pi.single_apply]
      rwa [heq] at h1
    | succ i =>
      have h1 := hin 0 (basisVec i) (Or.inr (Or.inl ⟨i, rfl⟩))
      have heq : (Fin.cons (0 : F2) (basisVec i) : Fin (k + 1) → F2) = Pi.single (i.succ : Fin (k + 1)) (1 : F2) := by
        funext j
        cases j using Fin.cases with
        | zero => simp [Pi.single_apply]
        | succ r => simp [basisVec, Pi.single_apply, Fin.succ_inj]
      rwa [heq] at h1
  rw [eq_top_iff]
  intro u _
  have hdec : u = ∑ m : Fin (k + 1), u m • Pi.single m (1 : F2) := by
    funext j
    simp [Pi.single_apply]
  rw [hdec]
  exact W.sum_mem fun m _ => W.smul_mem (u m) (hsing m)

private lemma atom_iff_perfect {k : ℕ} (G : SimpleGraph (Fin k)) (p : ℕ) (h : F2 → (Fin k → F2) → F2) :
    (∃ C : Circuit,
      ReadsBack (2 * (k + 1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
      costGates C.gates ≤ p ∧
      ∀ (x : Fin (k + 1) → F2) (v : F2) (z : Fin k → F2), isKey G z →
        C.eval (bitsOf (k + 1) x ++ bitsOf (k + 1) (Fin.cons v z)) =
          decide (dotProduct x (Fin.cons v z) + h v z = 1)) ↔
    (k + 1 ≤ p ∧ ∃ (D : Circuit) (tap : Fin (k + 1) → ℕ),
      ReadsBack (k + 1) D ∧
      (∀ g ∈ D.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
      costGates D.gates + (k + 1) ≤ p ∧
      D.output < k + 1 + D.size ∧
      (∀ j, tap j < k + 1 + D.size) ∧
      ∀ (v : F2) (z : Fin k → F2), isKey G z →
        let y : Fin (k + 1) → F2 := Fin.cons v z
        let inp := bitsOf (k + 1) y
        let pv : Fin (k + 1) → F2 := fun j => b2f3 ((D.wires inp).getD (tap j) false)
        b2f3 (D.eval inp) + dotProduct pv y = h v z) := by
  let K := k + 1
  have h844 := main_844 K 0 p
  constructor
  · rintro ⟨C, hrb, hleg, hcost, heval⟩
    have hleg' : ReadsBack (2 * K + 0) C ∧
        (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
          (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) :=
      ⟨by simpa [K] using hrb, hleg⟩
    obtain ⟨N, r, A, hatom, hsumr, hprof⟩ := h844.1 C hleg' hcost
    have hNpos : 0 < N := by
      by_contra hN0
      have h0 : N = 0 := by omega
      subst h0
      simp at hsumr
      exact absurd hsumr.symm (Nat.ne_of_gt (by positivity))
    let i0 : Fin N := ⟨0, hNpos⟩
    obtain ⟨W, a, D, tap, hrank, hlegD, hcostD, houtD, htapD, hA0⟩ := hatom i0
    have hA_val : ∀ (i : Fin N) (v : F2) (z : Fin k → F2), isKey G z →
        A i (Fin.cons v z) Fin.elim0 = sign3 (decide (h v z = 1)) := by
      intro i v z hz
      let y : Fin K → F2 := Fin.cons v z
      have hprof_val : (∑ x : Fin K → F2, sign3 (Bool.xor (C.eval (bitsOf K x ++ bitsOf K y ++ bitsOf 0 Fin.elim0))
          (decide (dotProduct x y = 1)))) = (2 : ℤ) ^ K * sign3 (decide (h v z = 1)) := by
        have hterm : ∀ x : Fin K → F2,
            sign3 (Bool.xor (C.eval (bitsOf K x ++ bitsOf K y ++ bitsOf 0 Fin.elim0)) (decide (dotProduct x y = 1))) =
              sign3 (decide (h v z = 1)) := by
          intro x
          have hnil : bitsOf 0 Fin.elim0 = [] := rfl
          rw [hnil, List.append_nil, heval x v z hz]
          rw [zmod2_add_decide]
          cases decide (dotProduct x y = 1) <;> cases decide (h v z = 1) <;> rfl
        simp_rw [hterm]
        simp [Finset.sum_const, Fintype.card_pi, Fintype.card_fin]
      have hprof_eq : ∑ j : Fin N, (2 : ℤ) ^ (K - r j) * A j y Fin.elim0 =
          (∑ j : Fin N, (2 : ℤ) ^ (K - r j)) * sign3 (decide (h v z = 1)) := by
        have hsumZ : (∑ j : Fin N, (2 : ℤ) ^ (K - r j)) = (2 : ℤ) ^ K := by
          exact_mod_cast hsumr
        rw [hsumZ, ← hprof_val]
        exact (hprof y Fin.elim0).symm
      have hA_range : ∀ j : Fin N, A j y Fin.elim0 = -1 ∨ A j y Fin.elim0 = 0 ∨ A j y Fin.elim0 = 1 := by
        intro j
        obtain ⟨Wj, aj, Dj, tapj, _, _, _, _, _, hAj⟩ := hatom j
        by_cases hmem : y - aj ∈ Wj
        · have h1 := (hAj y Fin.elim0).1 hmem
          rw [h1]
          dsimp only
          split_ifs <;> simp
        · exact Or.inr (Or.inl ((hAj y Fin.elim0).2 hmem))
      have hsign_cases : sign3 (decide (h v z = 1)) = 1 ∨ sign3 (decide (h v z = 1)) = -1 := by
        cases decide (h v z = 1) <;> simp [sign3]
      exact sum_weighted_eq_extreme (fun j => (2 : ℤ) ^ (K - r j)) (fun j => A j y Fin.elim0)
        (sign3 (decide (h v z = 1))) (fun j => by positivity) hA_range hsign_cases hprof_eq i
    have hmemW : ∀ (v : F2) (z : Fin k → F2), isKey G z → Fin.cons v z - a ∈ W := by
      intro v z hz
      by_contra hnot
      have h0 := (hA0 (Fin.cons v z) Fin.elim0).2 hnot
      have h1 := hA_val i0 v z hz
      rw [h0] at h1
      cases hdv : decide (h v z = 1) <;> (rw [hdv] at h1; dsimp only [sign3] at h1; omega)
    have hWtop : W = ⊤ := submodule_eq_top_of_key G W a hmemW
    have hrK : r i0 = K := by
      rw [← hrank, hWtop, finrank_top, Module.finrank_fin_fun]
    have hcostD' : costGates D.gates + (k + 1) ≤ p := by
      change costGates D.gates + r i0 ≤ p at hcostD
      rw [hrK] at hcostD
      exact hcostD
    refine ⟨by omega, D, tap, by simpa [K] using hlegD.1, hlegD.2, hcostD', by simpa [K] using houtD, by simpa [K] using htapD, ?_⟩
    intro v z hz
    let y : Fin K → F2 := Fin.cons v z
    have h1 := (hA0 y Fin.elim0).1 (hmemW v z hz)
    have h2 := hA_val i0 v z hz
    rw [h2] at h1
    have hnil : bitsOf 0 Fin.elim0 = [] := rfl
    change sign3 (decide (h v z = 1)) = sign3 (Bool.xor (D.eval (bitsOf K y ++ bitsOf 0 Fin.elim0))
      (decide (dotProduct (fun j => b2f3 ((D.wires (bitsOf K y ++ bitsOf 0 Fin.elim0)).getD (tap j) false)) y = 1))) at h1
    rw [hnil, List.append_nil] at h1
    have hbeq : decide (h v z = 1) = Bool.xor (D.eval (bitsOf K y))
        (decide (dotProduct (fun j => b2f3 ((D.wires (bitsOf K y)).getD (tap j) false)) y = 1)) :=
      (sign3_eq_iff _ _).mp h1
    have h3 := congrArg b2f3 hbeq
    rw [b2f3_decide, b2f3_xor, b2f3_decide] at h3
    exact h3.symm
  · rintro ⟨hkp, D, tap, hrbD, hlegD, hcostD, houtD, htapD, hvalD⟩
    let A : (Fin K → F2) → (Fin 0 → F2) → ℤ := fun y _ =>
      let inp := bitsOf K y
      let pv : Fin K → F2 := fun j => b2f3 ((D.wires inp).getD (tap j) false)
      sign3 (Bool.xor (D.eval inp) (decide (dotProduct pv y = 1)))
    have hatom : ∃ (W : Submodule F2 (Fin K → F2)) (a : Fin K → F2) (D' : Circuit) (tap' : Fin K → ℕ),
        Module.finrank F2 W = K ∧
        (ReadsBack (K + 0) D' ∧ ∀ g ∈ D'.gates, g.inputs.length ≤ 2 ∧
          (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
        costGates D'.gates + K ≤ p ∧ D'.output < K + 0 + D'.size ∧ (∀ j, tap' j < K + 0 + D'.size) ∧
        ∀ (y : Fin K → F2) (z0 : Fin 0 → F2),
          let inp := bitsOf K y ++ bitsOf 0 z0
          let pv : Fin K → F2 := fun j => if (D'.wires inp).getD (tap' j) false then (1 : F2) else 0
          (y - a ∈ W → A y z0 = sign3 (Bool.xor (D'.eval inp) (decide (dotProduct pv y = 1)))) ∧
            (y - a ∉ W → A y z0 = 0) := by
      refine ⟨⊤, 0, D, tap, by rw [finrank_top, Module.finrank_fin_fun], ⟨by simpa [K] using hrbD, hlegD⟩,
        hcostD, by simpa [K] using houtD, by simpa [K] using htapD, ?_⟩
      intro y z0
      have hnil : bitsOf 0 z0 = [] := rfl
      refine ⟨fun _ => by simp [A, hnil, b2f3], fun h => (h trivial).elim⟩
    obtain ⟨C, hlegC, hcostC, hprofC⟩ := h844.2 K A hatom
    refine ⟨C, by simpa [K] using hlegC.1, hlegC.2, hcostC, ?_⟩
    intro x v z hz
    let y : Fin K → F2 := Fin.cons v z
    have hA_eq : A y Fin.elim0 = sign3 (decide (h v z = 1)) := by
      dsimp only [A]
      have h1 := hvalD v z hz
      have h2 : Bool.xor (D.eval (bitsOf K y))
          (decide (dotProduct (fun j => b2f3 ((D.wires (bitsOf K y)).getD (tap j) false)) y = 1)) =
          decide (h v z = 1) := by
        have h3 := congrArg (fun u => decide (u = 1)) h1
        rw [zmod2_add_decide] at h3
        have h4 : decide (b2f3 (D.eval (bitsOf K y)) = 1) = D.eval (bitsOf K y) := by
          cases D.eval (bitsOf K y) <;> rfl
        rwa [h4] at h3
      rw [h2]
    have hprof_y : (∑ x' : Fin K → F2, sign3 (Bool.xor (C.eval (bitsOf K x' ++ bitsOf K y ++ bitsOf 0 Fin.elim0))
        (decide (dotProduct x' y = 1)))) = (2 : ℤ) ^ K * A y Fin.elim0 := hprofC y Fin.elim0
    rw [hA_eq] at hprof_y
    have hnil : bitsOf 0 Fin.elim0 = [] := rfl
    simp only [hnil, List.append_nil] at hprof_y
    have hsum_eq : ∑ x' : Fin K → F2, (1 : ℤ) * sign3 (Bool.xor (C.eval (bitsOf K x' ++ bitsOf K y))
        (decide (dotProduct x' y = 1))) =
        (∑ _x' : Fin K → F2, (1 : ℤ)) * sign3 (decide (h v z = 1)) := by
      have hcard : (∑ _x' : Fin K → F2, (1 : ℤ)) = (2 : ℤ) ^ K := by
        simp [Finset.sum_const, Fintype.card_pi, Fintype.card_fin]
      rw [hcard, ← hprof_y]
      simp only [one_mul]
    have hres := sum_weighted_eq_extreme (fun _ => (1 : ℤ))
      (fun x' => sign3 (Bool.xor (C.eval (bitsOf K x' ++ bitsOf K y)) (decide (dotProduct x' y = 1))))
      (sign3 (decide (h v z = 1))) (fun _ => by decide)
      (fun x' => by cases Bool.xor (C.eval (bitsOf K x' ++ bitsOf K y)) (decide (dotProduct x' y = 1)) <;> simp [sign3])
      (by cases decide (h v z = 1) <;> simp [sign3]) hsum_eq x
    have hbx := (sign3_eq_iff _ _).mp hres
    rw [zmod2_add_decide]
    clear h844 hatom hprofC hprof_y hsum_eq hres
    cases hce : C.eval (bitsOf K x ++ bitsOf K y) <;>
      cases hdp : decide (dotProduct x y = 1) <;>
      cases hhv : decide (h v z = 1) <;>
      simp only [hce, hdp, hhv] at hbx ⊢ <;> first | rfl | exact absurd hbx (by decide)

private def isAff3 {K : ℕ} (f : (Fin K → F2) → F2) : Prop :=
  ∃ (c : F2) (w : Fin K → F2), ∀ y, f y = c + dotProduct w y

private lemma isAff3_const {K : ℕ} (c : F2) : isAff3 (K := K) (fun _ => c) :=
  ⟨c, 0, fun y => by simp [dotProduct]⟩

private lemma isAff3_var {K : ℕ} (m : Fin K) : isAff3 (K := K) (fun y => y m) :=
  ⟨0, Pi.single m 1, fun y => by simp [dotProduct, Pi.single_apply]⟩

private lemma isAff3_add {K : ℕ} {f g : (Fin K → F2) → F2} (hf : isAff3 f) (hg : isAff3 g) :
    isAff3 (fun y => f y + g y) := by
  obtain ⟨cf, wf, hf⟩ := hf
  obtain ⟨cg, wg, hg⟩ := hg
  refine ⟨cf + cg, wf + wg, fun y => ?_⟩
  dsimp only; rw [hf y, hg y, add_dotProduct]; ring

private lemma isAff3_add_const {K : ℕ} {f : (Fin K → F2) → F2} (c : F2) (hf : isAff3 f) :
    isAff3 (fun y => c + f y) := isAff3_add (isAff3_const c) hf

private lemma isAff3_smul {K : ℕ} {f : (Fin K → F2) → F2} (a : F2) (hf : isAff3 f) :
    isAff3 (fun y => a * f y) := by
  obtain ⟨cf, wf, hf⟩ := hf
  refine ⟨a * cf, a • wf, fun y => ?_⟩
  dsimp only; rw [hf y, smul_dotProduct, smul_eq_mul]; ring

private lemma wires_at_gate_3 {K : ℕ} (D : Circuit) (hrb : ReadsBack K D) (y : Fin K → F2)
    (j : ℕ) (hj : j < D.gates.length) :
    (D.wires (bitsOf K y)).getD (K + j) false =
      (D.gates[j]).op.eval ((D.gates[j]).inputs.map fun a => (D.wires (bitsOf K y)).getD a false) := by
  have hlen : (bitsOf K y).length = K := bitsOf_len K y
  have hfold : ∀ (gs : List Gate) (init : List Bool) (idx : ℕ) (hidx : idx < gs.length),
      (∀ t (ht : t < gs.length), ∀ a ∈ (gs[t]'ht).inputs, a < init.length + t) →
      (wiresOf gs init).getD (init.length + idx) false =
        (gs[idx]).op.eval ((gs[idx]).inputs.map fun a => (wiresOf gs init).getD a false) := by
    intro gs
    induction gs with
    | nil => intro _ _ h; simp at h
    | cons g rest ih =>
      intro init idx hidx hrb_l
      cases idx with
      | zero =>
        simp only [wiresOf, Circuit.wires, List.foldl_cons, Nat.add_zero, List.getElem_cons_zero]
        let next := init ++ [g.op.eval (g.inputs.map fun a => init.getD a false)]
        have hlt : init.length < next.length := by simp [next]
        have hpre := wiresOf_getD_lt rest next hlt
        change (wiresOf rest next).getD init.length false = _
        rw [hpre]
        have hget : next.getD init.length false = g.op.eval (g.inputs.map fun a => init.getD a false) := by
          simp [next, List.getD_eq_getElem?_getD]
        rw [hget]
        congr 1
        apply List.map_congr_left
        intro a ha
        have halt : a < init.length := by
          have := hrb_l 0 (by simp) a ha; simpa using this
        have hpre2 := wiresOf_getD_lt rest next (lt_trans halt hlt)
        change init.getD a false = (wiresOf rest next).getD a false
        rw [hpre2]
        simp [next, List.getD_eq_getElem?_getD, List.getElem?_append_left halt]
      | succ idx' =>
        simp only [wiresOf, Circuit.wires, List.foldl_cons, List.getElem_cons_succ]
        let next := init ++ [g.op.eval (g.inputs.map fun a => init.getD a false)]
        have hidx' : idx' < rest.length := Nat.lt_of_succ_lt_succ hidx
        have hnext_len : next.length = init.length + 1 := by simp [next]
        have hrb_rest : ∀ t (ht : t < rest.length), ∀ a ∈ (rest[t]'ht).inputs, a < next.length + t := by
          intro t ht a ha
          have := hrb_l (t + 1) (by simp; omega) a (by simpa using ha)
          rw [hnext_len]; omega
        have hstep := ih next idx' hidx' hrb_rest
        have heq_idx : next.length + idx' = init.length + (idx' + 1) := by rw [hnext_len]; omega
        rw [heq_idx] at hstep
        exact hstep
  have hrb_l : ∀ t (ht : t < D.gates.length), ∀ a ∈ (D.gates[t]'ht).inputs, a < (bitsOf K y).length + t := by
    intro t ht a ha
    rw [hlen]
    have := hrb t ht a
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some] at this
    exact this ha
  have hres := hfold D.gates (bitsOf K y) j hj hrb_l
  rw [hlen] at hres
  exact hres

private noncomputable def isNL3 (g : Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

private lemma gate_eval_linear_of_not_nl (g : Gate)
    (hleg : g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
    (hnl : isNL3 g = false) :
    ∃ c0 c1 c2 : F2, ∀ vals : List Bool, vals.length = g.inputs.length →
      b2f3 (g.op.eval vals) = c0 + c1 * b2f3 (vals.getD 0 false) + c2 * b2f3 (vals.getD 1 false) := by
  obtain ⟨hlen, hop⟩ := hleg
  have hnot2 : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) := by
    intro h
    have : isNL3 g = true := by simp [isNL3, h]
    rw [this] at hnl; contradiction
  rcases g with ⟨op, inps⟩
  dsimp only at hlen hop hnot2 ⊢
  rcases hop with rfl | rfl | rfl | ⟨rfl, hlen1⟩
  · have hne2 : inps.length ≠ 2 := fun h2 => hnot2 ⟨Or.inl rfl, h2⟩
    have hlt2 : inps.length < 2 := by omega
    cases h0 : inps.length with
    | zero =>
      refine ⟨1, 0, 0, fun vals hv => ?_⟩
      cases vals with
      | nil => simp [GateOp.eval, b2f3]
      | cons _ _ => simp at hv
    | succ m =>
      have hm : m = 0 := by omega
      subst hm
      refine ⟨0, 1, 0, fun vals hv => ?_⟩
      rcases vals with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp at hv
      cases a <;> simp [GateOp.eval, b2f3]
  · have hne2 : inps.length ≠ 2 := fun h2 => hnot2 ⟨Or.inr rfl, h2⟩
    have hlt2 : inps.length < 2 := by omega
    cases h0 : inps.length with
    | zero =>
      refine ⟨0, 0, 0, fun vals hv => ?_⟩
      cases vals with
      | nil => simp [GateOp.eval, b2f3]
      | cons _ _ => simp at hv
    | succ m =>
      have hm : m = 0 := by omega
      subst hm
      refine ⟨0, 1, 0, fun vals hv => ?_⟩
      rcases vals with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp at hv
      cases a <;> simp [GateOp.eval, b2f3]
  · cases h0 : inps.length with
    | zero =>
      refine ⟨1, 0, 0, fun vals hv => ?_⟩
      cases vals with
      | nil => simp [GateOp.eval, b2f3]
      | cons _ _ => simp at hv
    | succ m =>
      cases m with
      | zero =>
        refine ⟨1, 1, 0, fun vals hv => ?_⟩
        rcases vals with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp at hv
        cases a <;> decide
      | succ m' =>
        have hm' : m' = 0 := by omega
        subst hm'
        refine ⟨1, 1, 1, fun vals hv => ?_⟩
        rcases vals with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp at hv
        cases a <;> cases b <;> decide
  · refine ⟨1, 1, 0, fun vals hv => ?_⟩
    rw [hlen1] at hv
    rcases vals with _ | ⟨a, _ | ⟨_, _⟩⟩ <;> simp at hv
    cases a <;> decide

private lemma circuit_wires_cost0 {K : ℕ} (D : Circuit) (hrb : ReadsBack K D)
    (hleg : ∀ g ∈ D.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
    (hcost0 : costGates D.gates = 0) :
    ∀ w : ℕ, isAff3 (K := K) (fun y => b2f3 ((D.wires (bitsOf K y)).getD w false)) := by
  have hall_lin : ∀ g ∈ D.gates, isNL3 g = false := by
    have h0 : D.gates.countP isNL3 = 0 := hcost0
    intro g hg
    by_contra hne
    have ht : isNL3 g = true := by cases h : isNL3 g <;> simp_all
    have hpos : 0 < D.gates.countP isNL3 := List.countP_pos_iff.mpr ⟨g, hg, ht⟩
    omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw_in : w < K
    · have heq : (fun y : Fin K → F2 => b2f3 ((D.wires (bitsOf K y)).getD w false)) = fun y => y ⟨w, hw_in⟩ := by
        funext y
        have hpre := wiresOf_getD_lt D.gates (bitsOf K y) (by rw [bitsOf_len]; exact hw_in)
        change b2f3 ((wiresOf D.gates (bitsOf K y)).getD w false) = _
        rw [hpre, bitsOf_getD K y ⟨w, hw_in⟩, b2f3_decide]
      rw [heq]
      exact isAff3_var ⟨w, hw_in⟩
    · by_cases hw_lt : w < K + D.gates.length
      · let j := w - K
        have hj : j < D.gates.length := by omega
        have hw_eq : w = K + j := by omega
        have hg_leg := hleg _ (List.getElem_mem hj)
        have hg_lin := hall_lin _ (List.getElem_mem hj)
        obtain ⟨c0, c1, c2, haff⟩ := gate_eval_linear_of_not_nl D.gates[j] hg_leg hg_lin
        have harg : ∀ idx : ℕ, isAff3 (K := K) (fun y =>
            b2f3 (((D.gates[j]).inputs.map fun a => (D.wires (bitsOf K y)).getD a false).getD idx false)) := by
          intro idx
          by_cases hidx : idx < (D.gates[j]).inputs.length
          · let a := (D.gates[j]).inputs[idx]
            have ha_lt : a < w := by
              have := hrb j hj a
              simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
              have := this (List.getElem_mem hidx); omega
            have heq : (fun y : Fin K → F2 =>
                b2f3 (((D.gates[j]).inputs.map fun u => (D.wires (bitsOf K y)).getD u false).getD idx false)) =
                fun y => b2f3 ((D.wires (bitsOf K y)).getD a false) := by
              funext y; simp [List.getD_eq_getElem?_getD, hidx, a]
            rw [heq]; exact ih a ha_lt
          · have heq : (fun y : Fin K → F2 =>
                b2f3 (((D.gates[j]).inputs.map fun u => (D.wires (bitsOf K y)).getD u false).getD idx false)) =
                fun _ => 0 := by
              funext y
              have hge : ((D.gates[j]).inputs.map fun u => (D.wires (bitsOf K y)).getD u false).length ≤ idx := by simp; omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
            rw [heq]; exact isAff3_const 0
        have heq : (fun y : Fin K → F2 => b2f3 ((D.wires (bitsOf K y)).getD w false)) =
            fun y => c0 + c1 * b2f3 (((D.gates[j]).inputs.map fun a => (D.wires (bitsOf K y)).getD a false).getD 0 false) +
                     c2 * b2f3 (((D.gates[j]).inputs.map fun a => (D.wires (bitsOf K y)).getD a false).getD 1 false) := by
          funext y
          rw [hw_eq, wires_at_gate_3 D hrb y j hj]
          exact haff _ (by simp)
        rw [heq]
        exact isAff3_add (isAff3_add_const c0 (isAff3_smul c1 (harg 0))) (isAff3_smul c2 (harg 1))
      · have heq : (fun y : Fin K → F2 => b2f3 ((D.wires (bitsOf K y)).getD w false)) = fun _ => 0 := by
          funext y
          have hge : (D.wires (bitsOf K y)).length ≤ w := by
            change (wiresOf D.gates (bitsOf K y)).length ≤ w
            rw [wiresOf_len, bitsOf_len]; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
        rw [heq]; exact isAff3_const 0

private lemma circuit_wires_cost1 {K : ℕ} (D : Circuit) (hrb : ReadsBack K D)
    (hleg : ∀ g ∈ D.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
    (hcost1 : costGates D.gates ≤ 1) :
    ∃ (u v : (Fin K → F2) → F2), isAff3 u ∧ isAff3 v ∧
      ∀ w : ℕ, ∃ (f : (Fin K → F2) → F2) (coef : F2), isAff3 f ∧
        ∀ y, b2f3 ((D.wires (bitsOf K y)).getD w false) = f y + coef * (u y * v y) := by
  by_cases h0 : costGates D.gates = 0
  · refine ⟨fun _ => 0, fun _ => 0, isAff3_const 0, isAff3_const 0, ?_⟩
    intro w
    refine ⟨fun y => b2f3 ((D.wires (bitsOf K y)).getD w false), 0, circuit_wires_cost0 D hrb hleg h0 w, ?_⟩
    intro y; simp
  · have hpos : 0 < D.gates.countP isNL3 := by
      change 0 < costGates D.gates; omega
    obtain ⟨g0, hg0_mem, hg0_nl⟩ := List.countP_pos_iff.mp hpos
    obtain ⟨jstar, hjstar, hgj⟩ := List.mem_iff_getElem.mp hg0_mem
    have huniq : ∀ j (hj : j < D.gates.length), isNL3 D.gates[j] = true → j = jstar := by
      intro j hj hnlj
      by_contra hne
      have hsub : D.gates.countP isNL3 ≥ 2 := by
        have hlen_f : ((List.range D.gates.length).filter fun t => isNL3 (D.gates.getD t ⟨.or, []⟩)).length =
            D.gates.countP isNL3 := by
          rw [List.countP_eq_length_filter]
          have hrg : D.gates = (List.range D.gates.length).map (fun t => D.gates.getD t ⟨.or, []⟩) := by
            apply List.ext_getElem
            · simp
            · intro t ht1 _; simp [List.getD_eq_getElem?_getD, ht1]
          conv_rhs => rw [hrg, List.filter_map, List.length_map]
          rfl
        rw [← hlen_f]
        let fl := (List.range D.gates.length).filter fun t => isNL3 (D.gates.getD t ⟨.or, []⟩)
        have hm1 : j ∈ fl := by
          simp only [fl, List.mem_filter, List.mem_range]
          exact ⟨hj, by simpa [List.getD_eq_getElem?_getD, hj] using hnlj⟩
        have hm2 : jstar ∈ fl := by
          simp only [fl, List.mem_filter, List.mem_range]
          exact ⟨hjstar, by simpa [List.getD_eq_getElem?_getD, hjstar, hgj] using hg0_nl⟩
        have hnd : fl.Nodup := (List.nodup_range).filter _
        have hsub2 : ({j, jstar} : Finset ℕ) ⊆ fl.toFinset := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
        have hc := Finset.card_le_card hsub2
        rw [Finset.card_pair hne, List.toFinset_card_of_nodup hnd] at hc
        exact hc
      change D.gates.countP isNL3 ≤ 1 at hcost1
      omega
    have hbefore : ∀ w < K + jstar, isAff3 (K := K) (fun y => b2f3 ((D.wires (bitsOf K y)).getD w false)) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw_lt
        by_cases hw_in : w < K
        · have heq : (fun y : Fin K → F2 => b2f3 ((D.wires (bitsOf K y)).getD w false)) = fun y => y ⟨w, hw_in⟩ := by
            funext y
            have hpre := wiresOf_getD_lt D.gates (bitsOf K y) (by rw [bitsOf_len]; exact hw_in)
            change b2f3 ((wiresOf D.gates (bitsOf K y)).getD w false) = _
            rw [hpre, bitsOf_getD K y ⟨w, hw_in⟩, b2f3_decide]
          rw [heq]; exact isAff3_var ⟨w, hw_in⟩
        · let j := w - K
          have hj : j < D.gates.length := by omega
          have hw_eq : w = K + j := by omega
          have hne : j ≠ jstar := by omega
          have hlin : isNL3 D.gates[j] = false := by
            cases h : isNL3 D.gates[j]
            · rfl
            · exact absurd (huniq j hj h) hne
          obtain ⟨c0, c1, c2, haff⟩ := gate_eval_linear_of_not_nl D.gates[j] (hleg _ (List.getElem_mem hj)) hlin
          have harg : ∀ idx : ℕ, isAff3 (K := K) (fun y =>
              b2f3 (((D.gates[j]).inputs.map fun a => (D.wires (bitsOf K y)).getD a false).getD idx false)) := by
            intro idx
            by_cases hidx : idx < (D.gates[j]).inputs.length
            · let a := (D.gates[j]).inputs[idx]
              have ha_lt : a < w := by
                have := hrb j hj a
                simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
                have := this (List.getElem_mem hidx); omega
              have heq : (fun y : Fin K → F2 =>
                  b2f3 (((D.gates[j]).inputs.map fun u => (D.wires (bitsOf K y)).getD u false).getD idx false)) =
                  fun y => b2f3 ((D.wires (bitsOf K y)).getD a false) := by
                funext y; simp [List.getD_eq_getElem?_getD, hidx, a]
              rw [heq]; exact ih a ha_lt (by omega)
            · have heq : (fun y : Fin K → F2 =>
                  b2f3 (((D.gates[j]).inputs.map fun u => (D.wires (bitsOf K y)).getD u false).getD idx false)) =
                  fun _ => 0 := by
                funext y
                have hge : ((D.gates[j]).inputs.map fun u => (D.wires (bitsOf K y)).getD u false).length ≤ idx := by simp; omega
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
              rw [heq]; exact isAff3_const 0
          have heq : (fun y : Fin K → F2 => b2f3 ((D.wires (bitsOf K y)).getD w false)) =
              fun y => c0 + c1 * b2f3 (((D.gates[j]).inputs.map fun a => (D.wires (bitsOf K y)).getD a false).getD 0 false) +
                       c2 * b2f3 (((D.gates[j]).inputs.map fun a => (D.wires (bitsOf K y)).getD a false).getD 1 false) := by
            funext y
            rw [hw_eq, wires_at_gate_3 D hrb y j hj]
            exact haff _ (by simp)
          rw [heq]
          exact isAff3_add (isAff3_add_const c0 (isAff3_smul c1 (harg 0))) (isAff3_smul c2 (harg 1))
    have hnl_star : (D.gates[jstar].op = .and ∨ D.gates[jstar].op = .or) ∧ D.gates[jstar].inputs.length = 2 := by
      have h1 : isNL3 D.gates[jstar] = true := by rwa [hgj]
      exact @of_decide_eq_true _ (Classical.propDecidable _) h1
    have hlen2 : D.gates[jstar].inputs.length = 2 := hnl_star.2
    let a0 := D.gates[jstar].inputs[0]'(by omega)
    let a1 := D.gates[jstar].inputs[1]'(by omega)
    have ha0_lt : a0 < K + jstar := by
      have := hrb jstar hjstar a0
      simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjstar, Option.getD_some] at this
      exact this (List.getElem_mem (by omega))
    have ha1_lt : a1 < K + jstar := by
      have := hrb jstar hjstar a1
      simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjstar, Option.getD_some] at this
      exact this (List.getElem_mem (by omega))
    let u : (Fin K → F2) → F2 := fun y => b2f3 ((D.wires (bitsOf K y)).getD a0 false)
    let v : (Fin K → F2) → F2 := fun y => b2f3 ((D.wires (bitsOf K y)).getD a1 false)
    have hu_aff : isAff3 u := hbefore a0 ha0_lt
    have hv_aff : isAff3 v := hbefore a1 ha1_lt
    refine ⟨u, v, hu_aff, hv_aff, ?_⟩
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hlt : w < K + jstar
      · exact ⟨fun y => b2f3 ((D.wires (bitsOf K y)).getD w false), 0, hbefore w hlt, fun y => by simp⟩
      · by_cases heq_star : w = K + jstar
        · have hlist_aux : ∀ l : List ℕ, (hl : l.length = 2) → l = [l[0]'(by omega), l[1]'(by omega)] := by
            intro l hl; rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;> simp at hl ⊢
          have hlist := hlist_aux _ hlen2
          rcases hnl_star.1 with hand | hor
          · refine ⟨fun _ => 0, 1, isAff3_const 0, fun y => ?_⟩
            rw [heq_star, wires_at_gate_3 D hrb y jstar hjstar]
            conv_lhs => rw [hlist, hand]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, b2f3_and]
            simp [u, v, a0, a1]
          · refine ⟨fun y => u y + v y, 1, isAff3_add hu_aff hv_aff, fun y => ?_⟩
            rw [heq_star, wires_at_gate_3 D hrb y jstar hjstar]
            conv_lhs => rw [hlist, hor]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, b2f3_or]
            simp [u, v, a0, a1]
        · by_cases hw_lt : w < K + D.gates.length
          · let j := w - K
            have hj : j < D.gates.length := by omega
            have hw_eq : w = K + j := by omega
            have hne : j ≠ jstar := by omega
            have hlin : isNL3 D.gates[j] = false := by
              cases h : isNL3 D.gates[j]
              · rfl
              · exact absurd (huniq j hj h) hne
            obtain ⟨c0, c1, c2, haff⟩ := gate_eval_linear_of_not_nl D.gates[j] (hleg _ (List.getElem_mem hj)) hlin
            have harg : ∀ idx : ℕ, ∃ (fi : (Fin K → F2) → F2) (ci : F2), isAff3 fi ∧
                ∀ y, b2f3 (((D.gates[j]).inputs.map fun a => (D.wires (bitsOf K y)).getD a false).getD idx false) =
                  fi y + ci * (u y * v y) := by
              intro idx
              by_cases hidx : idx < (D.gates[j]).inputs.length
              · let a := (D.gates[j]).inputs[idx]
                have ha_lt : a < w := by
                  have := hrb j hj a
                  simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
                  have := this (List.getElem_mem hidx); omega
                obtain ⟨fa, ca, hfa, hqa⟩ := ih a ha_lt
                refine ⟨fa, ca, hfa, fun y => ?_⟩
                simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hidx, Option.map_some, Option.getD_some]
                exact hqa y
              · refine ⟨fun _ => 0, 0, isAff3_const 0, fun y => ?_⟩
                have hge : ((D.gates[j]).inputs.map fun a => (D.wires (bitsOf K y)).getD a false).length ≤ idx := by simp; omega
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; simp [b2f3]
            obtain ⟨f0, q0, hf0, h0⟩ := harg 0
            obtain ⟨f1, q1, hf1, h1⟩ := harg 1
            refine ⟨fun y => c0 + c1 * f0 y + c2 * f1 y, c1 * q0 + c2 * q1,
              isAff3_add (isAff3_add_const c0 (isAff3_smul c1 hf0)) (isAff3_smul c2 hf1), fun y => ?_⟩
            rw [hw_eq, wires_at_gate_3 D hrb y j hj, haff _ (by simp), h0 y, h1 y]
            ring
          · refine ⟨fun _ => 0, 0, isAff3_const 0, fun y => ?_⟩
            have hge : (D.wires (bitsOf K y)).length ≤ w := by
              change (wiresOf D.gates (bitsOf K y)).length ≤ w
              rw [wiresOf_len, bitsOf_len]; omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; simp [b2f3]

private def buildXor3 (offset : ℕ) (gs : List Gate) (w1 w2 : ℕ) : List Gate × ℕ :=
  let base := offset + gs.length
  (gs ++ [⟨GateOp.mod 2, [w1, w2]⟩, ⟨GateOp.not, [base]⟩], base + 1)

private def buildXorList3 (offset : ℕ) (gs : List Gate) (ws : List ℕ) : List Gate × ℕ :=
  match ws with
  | [] => (gs ++ [⟨GateOp.or, []⟩], offset + gs.length)
  | [w] => (gs, w)
  | w :: rest =>
    let (gs1, acc) := buildXorList3 offset gs rest
    buildXor3 offset gs1 w acc

private def buildAff3 {K : ℕ} (gs : List Gate) (c : F2) (w : Fin K → F2) : List Gate × ℕ :=
  let ws := ((List.finRange K).filter (fun m => decide (w m = 1))).map (fun m => m.val)
  let (gs1, wire) := buildXorList3 K gs ws
  if c = 1 then (gs1 ++ [⟨GateOp.not, [wire]⟩], K + gs1.length) else (gs1, wire)

private def lbx3 (l : List Bool) : Bool := l.foldr Bool.xor false

private lemma b2f3_lbx3 (l : List Bool) : b2f3 (lbx3 l) = (l.map b2f3).sum := by
  induction l with
  | nil => simp [lbx3, b2f3]
  | cons a r ih => simp only [lbx3, List.foldr_cons, List.map_cons, List.sum_cons, b2f3_xor, ← ih]

private lemma legalGates_append_one {K : ℕ} {gs : List Gate} {g : Gate}
    (hv : legalGates K gs)
    (hf : g.inputs.length ≤ 2 ∧ (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
    (hb : ∀ a ∈ g.inputs, a < K + gs.length) :
    legalGates K (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro j hj a ha
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at ha
    by_cases hlt : j < gs.length
    · rw [List.getElem_append_left hlt] at ha
      have h1 := hv.1 j hlt a
      simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some] at h1
      exact h1 ha
    · have hjeq : j = gs.length := by simp at hj; omega
      subst hjeq
      simp at ha
      exact hb a ha
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hv.2 x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact hf

private lemma wiresOf_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresOf (gs ++ [g]) x = wiresOf gs x ++ [g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false)] := by
  rw [wiresOf_append]; rfl

private lemma getD_snoc_self {α : Type*} (l : List α) (v d : α) : (l ++ [v]).getD l.length d = v := by
  simp [List.getD_eq_getElem?_getD]

private lemma getD_snoc_lt {α : Type*} (l : List α) (v : α) (i : ℕ) (hi : i < l.length) (d : α) :
    (l ++ [v]).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma buildXor3_spec (K : ℕ) (gs : List Gate) (w1 w2 : ℕ)
    (hv : legalGates K gs) (h1 : w1 < K + gs.length) (h2 : w2 < K + gs.length) :
    let res := buildXor3 K gs w1 w2
    legalGates K res.1 ∧
    costGates res.1 = costGates gs ∧
    gs.length ≤ res.1.length ∧
    res.2 < K + res.1.length ∧
    (∀ x : List Bool, x.length = K →
      (∀ t < K + gs.length, (wiresOf res.1 x).getD t false = (wiresOf gs x).getD t false) ∧
      (wiresOf res.1 x).getD res.2 false = Bool.xor ((wiresOf gs x).getD w1 false) ((wiresOf gs x).getD w2 false)) := by
  dsimp only [buildXor3]
  let g1 : Gate := ⟨GateOp.mod 2, [w1, w2]⟩
  let g2 : Gate := ⟨GateOp.not, [K + gs.length]⟩
  have hv1 : legalGates K (gs ++ [g1]) :=
    legalGates_append_one hv ⟨by simp [g1], Or.inr (Or.inr (Or.inl rfl))⟩
      (by intro a ha; simp [g1] at ha; rcases ha with rfl | rfl <;> omega)
  have hv2 : legalGates K ((gs ++ [g1]) ++ [g2]) :=
    legalGates_append_one hv1 ⟨by simp [g2], Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
      (by intro a ha; simp [g2] at ha; subst ha; simp)
  have happ : gs ++ [g1, g2] = (gs ++ [g1]) ++ [g2] := by simp [List.append_assoc]
  rw [happ]
  have hc1 : isNL3 g1 = false := by simp [isNL3, g1]
  have hc2 : isNL3 g2 = false := by simp [isNL3, g2]
  refine ⟨hv2, ?_, by simp, by simp; omega, ?_⟩
  · unfold costGates
    change ((gs ++ [g1]) ++ [g2]).countP isNL3 = gs.countP isNL3
    rw [List.countP_append, List.countP_append, List.countP_cons, List.countP_cons, List.countP_nil, hc1, hc2]
    simp
  · intro x hx
    have hlen0 : (wiresOf gs x).length = K + gs.length := by rw [wiresOf_len, hx]
    have hlen1 : (wiresOf (gs ++ [g1]) x).length = K + gs.length + 1 := by rw [wiresOf_len, hx]; simp; omega
    refine ⟨?_, ?_⟩
    · intro t ht
      rw [wiresOf_snoc, getD_snoc_lt _ _ t (by omega), wiresOf_snoc, getD_snoc_lt _ _ t (by omega)]
    · rw [wiresOf_snoc]
      have hidx : K + gs.length + 1 = (wiresOf (gs ++ [g1]) x).length := by omega
      rw [hidx, getD_snoc_self]
      simp only [g2, List.map_cons, List.map_nil]
      rw [wiresOf_snoc]
      have hidx0 : K + gs.length = (wiresOf gs x).length := by omega
      rw [hidx0, getD_snoc_self]
      simp only [g1, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
      cases (wiresOf gs x).getD w1 false <;> cases (wiresOf gs x).getD w2 false <;> decide

private lemma buildXorList3_spec (K : ℕ) (ws : List ℕ) (gs : List Gate)
    (hv : legalGates K gs) (hws : ∀ a ∈ ws, a < K + gs.length) :
    let res := buildXorList3 K gs ws
    legalGates K res.1 ∧
    costGates res.1 = costGates gs ∧
    gs.length ≤ res.1.length ∧
    res.2 < K + res.1.length ∧
    (∀ x : List Bool, x.length = K →
      (∀ t < K + gs.length, (wiresOf res.1 x).getD t false = (wiresOf gs x).getD t false) ∧
      (wiresOf res.1 x).getD res.2 false = lbx3 (ws.map fun a => (wiresOf gs x).getD a false)) := by
  induction ws generalizing gs with
  | nil =>
    dsimp only [buildXorList3]
    let g0 : Gate := ⟨GateOp.or, []⟩
    have hv1 : legalGates K (gs ++ [g0]) :=
      legalGates_append_one hv ⟨by simp [g0], Or.inr (Or.inl rfl)⟩ (by simp [g0])
    have hc0 : isNL3 g0 = false := by simp [isNL3, g0]
    refine ⟨hv1, ?_, by simp, by simp, ?_⟩
    · unfold costGates
      change (gs ++ [g0]).countP isNL3 = gs.countP isNL3
      rw [List.countP_append, List.countP_cons, List.countP_nil, hc0]; simp
    · intro x hx
      refine ⟨fun t ht => by rw [wiresOf_snoc, getD_snoc_lt _ _ t (by rw [wiresOf_len, hx]; exact ht)], ?_⟩
      rw [wiresOf_snoc]
      have hidx : K + gs.length = (wiresOf gs x).length := by rw [wiresOf_len, hx]
      rw [hidx, getD_snoc_self]
      simp [g0, GateOp.eval, lbx3]
  | cons a rest ih =>
    cases rest with
    | nil =>
      dsimp only [buildXorList3]
      refine ⟨hv, rfl, le_rfl, hws a (by simp), fun x _ => ⟨fun _ _ => rfl, by simp [lbx3]⟩⟩
    | cons b rest' =>
      dsimp only [buildXorList3]
      obtain ⟨hv1, hcnt1, hlen1, hacc_lt, hw1⟩ := ih gs hv (fun u hu => hws u (List.mem_cons_of_mem a hu))
      set gs1 := (buildXorList3 K gs (b :: rest')).1
      set acc := (buildXorList3 K gs (b :: rest')).2
      have ha_lt0 : a < K + gs.length := hws a (by simp)
      obtain ⟨hv2, hcnt2, hlen2, hout_lt, hw2⟩ := buildXor3_spec K gs1 a acc hv1 (by omega) hacc_lt
      refine ⟨hv2, hcnt2.trans hcnt1, le_trans hlen1 hlen2, hout_lt, ?_⟩
      intro x hx
      obtain ⟨hpre1, hval1⟩ := hw1 x hx
      obtain ⟨hpre2, hval2⟩ := hw2 x hx
      refine ⟨fun t ht => by rw [hpre2 t (by omega), hpre1 t ht], ?_⟩
      rw [hval2, hpre1 a ha_lt0, hval1]
      simp [lbx3]

private lemma buildAff3_spec {K : ℕ} (gs : List Gate) (c : F2) (w : Fin K → F2) (hv : legalGates K gs) :
    let res := buildAff3 gs c w
    legalGates K res.1 ∧
    costGates res.1 = costGates gs ∧
    gs.length ≤ res.1.length ∧
    res.2 < K + res.1.length ∧
    (∀ y : Fin K → F2,
      (∀ t < K + gs.length, (wiresOf res.1 (bitsOf K y)).getD t false = (wiresOf gs (bitsOf K y)).getD t false) ∧
      b2f3 ((wiresOf res.1 (bitsOf K y)).getD res.2 false) = c + dotProduct w y) := by
  dsimp only [buildAff3]
  let ws := ((List.finRange K).filter (fun m => decide (w m = 1))).map (fun m => m.val)
  have hws_lt : ∀ a ∈ ws, a < K + gs.length := by
    intro a ha
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp ha
    omega
  obtain ⟨hv1, hcnt1, hlen1, hw1_lt, hwire1⟩ := buildXorList3_spec K ws gs hv hws_lt
  set gs1 := (buildXorList3 K gs ws).1
  set w1 := (buildXorList3 K gs ws).2
  have hdot_eval : ∀ y : Fin K → F2, b2f3 ((wiresOf gs1 (bitsOf K y)).getD w1 false) = dotProduct w y := by
    intro y
    rw [(hwire1 (bitsOf K y) (bitsOf_len K y)).2, b2f3_lbx3]
    have hmap : ws.map (fun a => (wiresOf gs (bitsOf K y)).getD a false) =
        ((List.finRange K).filter (fun m => decide (w m = 1))).map (fun m => decide (y m = 1)) := by
      simp only [ws, List.map_map]
      apply List.map_congr_left
      intro m _
      simp only [Function.comp_apply]
      rw [wiresOf_getD_lt gs (bitsOf K y) (by rw [bitsOf_len]; exact m.isLt), bitsOf_getD]
    rw [hmap, List.map_map]
    have hnd : ((List.finRange K).filter (fun m => decide (w m = 1))).Nodup := (List.nodup_finRange K).filter _
    rw [← List.sum_toFinset _ hnd]
    have hset : ((List.finRange K).filter (fun m => decide (w m = 1))).toFinset =
        Finset.univ.filter (fun m : Fin K => w m = 1) := by ext m; simp
    rw [hset]
    unfold dotProduct
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun m : Fin K => w m = 1)]
    have hzero : ∑ m ∈ Finset.univ.filter (fun m : Fin K => ¬ w m = 1), w m * y m = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      have h0 : w m = 0 := by rcases zmod2_cases (w m) with h | h; exact h; exact absurd h hm
      simp [h0]
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    simp [hm, b2f3_decide]
  by_cases hc : c = 1
  · simp only [hc, ↓reduceIte]
    let gn : Gate := ⟨GateOp.not, [w1]⟩
    have hv2 : legalGates K (gs1 ++ [gn]) :=
      legalGates_append_one hv1 ⟨by simp [gn], Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
        (by intro a ha; simp [gn] at ha; subst ha; exact hw1_lt)
    have hcn : isNL3 gn = false := by simp [isNL3, gn]
    refine ⟨hv2, ?_, by simp; omega, by simp, ?_⟩
    · change (gs1 ++ [gn]).countP isNL3 = gs.countP isNL3
      rw [List.countP_append, List.countP_cons, List.countP_nil, hcn]
      change gs1.countP isNL3 + 0 = gs.countP isNL3
      rw [add_zero]
      exact hcnt1
    · intro y
      have hxlen : (bitsOf K y).length = K := bitsOf_len K y
      refine ⟨?_, ?_⟩
      · intro t ht
        rw [wiresOf_snoc, getD_snoc_lt _ _ t (by rw [wiresOf_len, hxlen]; omega)]
        exact (hwire1 (bitsOf K y) hxlen).1 t ht
      · rw [wiresOf_snoc]
        have hidx : K + gs1.length = (wiresOf gs1 (bitsOf K y)).length := by rw [wiresOf_len, hxlen]
        rw [hidx, getD_snoc_self]
        simp only [gn, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2f3_not, hdot_eval y, hc]
  · have hc0 : c = 0 := by rcases zmod2_cases c with h | h; exact h; exact absurd h hc
    simp only [hc, ↓reduceIte]
    refine ⟨hv1, hcnt1, hlen1, hw1_lt, fun y => ⟨(hwire1 (bitsOf K y) (bitsOf_len K y)).1, by rw [hc0, zero_add, hdot_eval y]⟩⟩

private lemma build_taps_aff {K : ℕ} (f_c : Fin K → F2) (f_w : Fin K → Fin K → F2) (gs : List Gate)
    (hv : legalGates K gs) :
    ∀ m : ℕ, (hm : m ≤ K) →
      ∃ (gs' : List Gate) (tap : Fin m → ℕ),
        legalGates K gs' ∧ costGates gs' = costGates gs ∧ gs.length ≤ gs'.length ∧
        (∀ j : Fin m, tap j < K + gs'.length) ∧
        (∀ y : Fin K → F2,
          (∀ t < K + gs.length, (wiresOf gs' (bitsOf K y)).getD t false = (wiresOf gs (bitsOf K y)).getD t false) ∧
          (∀ j : Fin m, b2f3 ((wiresOf gs' (bitsOf K y)).getD (tap j) false) =
            f_c ⟨j.val, by omega⟩ + dotProduct (f_w ⟨j.val, by omega⟩) y)) := by
  intro m hm
  induction m with
  | zero =>
    refine ⟨gs, Fin.elim0, hv, rfl, le_rfl, fun j => j.elim0, fun _ => ⟨fun _ _ => rfl, fun j => j.elim0⟩⟩
  | succ m ih =>
    obtain ⟨gs1, tap1, hv1, hc1, hl1, ht1, hw1⟩ := ih (Nat.le_of_succ_le hm)
    let jnew : Fin K := ⟨m, hm⟩
    obtain ⟨hv2, hc2, hl2, hw2_lt, hw2⟩ := buildAff3_spec gs1 (f_c jnew) (f_w jnew) hv1
    set res := buildAff3 gs1 (f_c jnew) (f_w jnew)
    refine ⟨res.1, Fin.snoc tap1 res.2, hv2, hc2.trans hc1, le_trans hl1 hl2, ?_, ?_⟩
    · intro j
      cases j using Fin.lastCases with
      | last => simpa using hw2_lt
      | cast j0 => simp only [Fin.snoc_castSucc]; have := ht1 j0; omega
    · intro y
      refine ⟨fun t ht => by rw [(hw2 y).1 t (by omega), (hw1 y).1 t ht], ?_⟩
      intro j
      cases j using Fin.lastCases with
      | last => simpa [jnew] using (hw2 y).2
      | cast j0 =>
        simp only [Fin.snoc_castSucc, Fin.val_castSucc]
        rw [(hw2 y).1 (tap1 j0) (ht1 j0)]
        exact (hw1 y).2 j0

private lemma build_quad_circuit_cost0 {k : ℕ} (G : SimpleGraph (Fin k))
    (h : F2 → (Fin k → F2) → F2)
    (hlab : ∀ i j : Fin k, G.Adj i j →
      (h 0 0 + h 1 0) + (h 0 (basisVec i) + h 1 (basisVec i)) +
      (h 0 (basisVec j) + h 1 (basisVec j)) +
      (h 0 (basisVec i + basisVec j) + h 1 (basisVec i + basisVec j)) = 0) :
    ∃ (D : Circuit) (tap : Fin (k + 1) → ℕ),
      ReadsBack (k + 1) D ∧
      (∀ g ∈ D.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
      costGates D.gates = 0 ∧
      D.output < k + 1 + D.size ∧
      (∀ j, tap j < k + 1 + D.size) ∧
      ∀ (v : F2) (z : Fin k → F2), isKey G z →
        let y : Fin (k + 1) → F2 := Fin.cons v z
        let inp := bitsOf (k + 1) y
        let pv : Fin (k + 1) → F2 := fun j => b2f3 ((D.wires inp).getD (tap j) false)
        b2f3 (D.eval inp) + dotProduct pv y = h v z := by
  classical
  let K := k + 1
  let d : (Fin k → F2) → F2 := fun z => h 0 z + h 1 z
  let fc : F2 := h 0 0
  let fw : Fin K → F2 := Fin.cons 0 (fun i => h 0 0 + h 0 (basisVec i))
  let pc : Fin K → F2 := Fin.cons (d 0) (fun _ => 0)
  let pw : Fin K → Fin K → F2 := Fin.cons
    (Fin.cons 0 (fun i => d 0 + d (basisVec i)))
    (fun i => Fin.cons 0 (fun j =>
      if i.val < j.val ∧ G.Adj i j then
        h 0 0 + h 0 (basisVec i) + h 0 (basisVec j) + h 0 (basisVec i + basisVec j)
      else 0))
  have hv0 : legalGates K [] := ⟨fun _ hj => by simp at hj, by simp⟩
  obtain ⟨hv1, hc1, _, hout1, hw1⟩ := buildAff3_spec [] fc fw hv0
  set outRes := buildAff3 [] fc fw
  obtain ⟨gs2, tap, hv2, hc2, hl2, htap2, hw2⟩ := build_taps_aff pc pw outRes.1 hv1 K le_rfl
  let D : Circuit := ⟨gs2, outRes.2⟩
  refine ⟨D, tap, hv2.1, hv2.2, by rw [hc2, hc1]; rfl, by dsimp [D, Circuit.size]; omega, htap2, ?_⟩
  intro v z hz
  dsimp only
  let y : Fin K → F2 := Fin.cons v z
  have hout_eval : b2f3 (D.eval (bitsOf K y)) = fc + dotProduct fw y := by
    change b2f3 ((wiresOf gs2 (bitsOf K y)).getD outRes.2 false) = _
    rw [(hw2 y).1 outRes.2 hout1]
    exact (hw1 y).2
  have htap_eval : ∀ j : Fin K, b2f3 ((D.wires (bitsOf K y)).getD (tap j) false) = pc j + dotProduct (pw j) y := by
    intro j
    exact (hw2 y).2 j
  have hdot_y : dotProduct (fun j => b2f3 ((D.wires (bitsOf K y)).getD (tap j) false)) y =
      v * (d 0 + ∑ i : Fin k, (d 0 + d (basisVec i)) * z i) +
      ∑ i : Fin k, z i * ∑ j : Fin k,
        (if i.val < j.val ∧ G.Adj i j then
          h 0 0 + h 0 (basisVec i) + h 0 (basisVec j) + h 0 (basisVec i + basisVec j) else 0) * z j := by
    unfold dotProduct
    rw [Fin.sum_univ_succ]
    simp_rw [htap_eval]
    congr 1
    · simp only [K, y, pc, pw, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add]
      ring
    · apply Finset.sum_congr rfl
      intro i _
      simp only [K, y, pc, pw, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add]
      ring
  have hout_simp : fc + dotProduct fw y = h 0 0 + ∑ i : Fin k, (h 0 0 + h 0 (basisVec i)) * z i := by
    simp only [K, fc, fw, y, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add]
  change b2f3 (D.eval (bitsOf K y)) + dotProduct (fun j => b2f3 ((D.wires (bitsOf K y)).getD (tap j) false)) y = h v z
  rw [hout_eval, hout_simp, hdot_y]
  have hv_decomp : h v z = h 0 z + v * d z := by
    rcases zmod2_cases v with rfl | rfl
    · simp
    · simp only [d, one_mul]
      have := f2_add_self (h 0 z); linear_combination -this
  rw [hv_decomp]
  rcases hz with rfl | ⟨r, rfl⟩ | ⟨r, s, hadj, rfl⟩
  · simp [d]
  · have hlin : ∀ f : Fin k → F2, (∑ i : Fin k, f i * basisVec r i) = f r := by
      intro f
      rw [Finset.sum_eq_single r]
      · simp [basisVec]
      · intro i _ hir; simp [basisVec, hir]
      · intro hr; exact absurd (Finset.mem_univ r) hr
    have hq0 : ∀ i : Fin k, basisVec r i * ∑ j : Fin k,
        (if i.val < j.val ∧ G.Adj i j then
          h 0 0 + h 0 (basisVec i) + h 0 (basisVec j) + h 0 (basisVec i + basisVec j) else 0) * basisVec r j = 0 := by
      intro i
      rw [hlin]
      by_cases hir : i = r
      · subst hir; simp
      · simp [basisVec, hir]
    simp_rw [hq0, Finset.sum_const_zero, add_zero, hlin]
    have h1 := f2_add_self (h 0 0)
    have h2 := f2_add_self (d 0)
    linear_combination h1 + v * h2
  · have hne : r ≠ s := G.ne_of_adj hadj
    have hlin2 : ∀ f : Fin k → F2, (∑ i : Fin k, f i * (basisVec r + basisVec s) i) = f r + f s := by
      intro f
      have hadd : ∀ i, f i * (basisVec r + basisVec s) i = f i * basisVec r i + f i * basisVec s i := by
        intro i; simp [Pi.add_apply, mul_add]
      simp_rw [hadd, Finset.sum_add_distrib]
      have h1 : ∑ i : Fin k, f i * basisVec r i = f r := by
        rw [Finset.sum_eq_single r]
        · simp [basisVec]
        · intro i _ hir; simp [basisVec, hir]
        · intro hr; exact absurd (Finset.mem_univ r) hr
      have h2 : ∑ i : Fin k, f i * basisVec s i = f s := by
        rw [Finset.sum_eq_single s]
        · simp [basisVec]
        · intro i _ his; simp [basisVec, his]
        · intro hs; exact absurd (Finset.mem_univ s) hs
      rw [h1, h2]
    have hquad2 : (∑ i : Fin k, (basisVec r + basisVec s) i * ∑ j : Fin k,
        (if i.val < j.val ∧ G.Adj i j then
          h 0 0 + h 0 (basisVec i) + h 0 (basisVec j) + h 0 (basisVec i + basisVec j) else 0) *
          (basisVec r + basisVec s) j) =
        h 0 0 + h 0 (basisVec r) + h 0 (basisVec s) + h 0 (basisVec r + basisVec s) := by
      simp_rw [hlin2]
      have hsum_rs : ∀ g : Fin k → F2, (∑ i : Fin k, (basisVec r + basisVec s) i * g i) = g r + g s := by
        intro g
        have := hlin2 g
        simpa [mul_comm] using this
      rw [hsum_rs]
      by_cases hlt : r.val < s.val
      · have hnlt : ¬ s.val < r.val := by omega
        simp [hlt, hnlt, hadj]
      · have hgt : s.val < r.val := by
          have : r.val ≠ s.val := fun h => hne (Fin.ext h)
          omega
        have hadj' : G.Adj s r := hadj.symm
        simp [hlt, hgt, hadj', add_comm (basisVec s) (basisVec r)]
        ring
    rw [hlin2, hlin2, hquad2]
    have hl := hlab r s hadj
    change d 0 + d (basisVec r) + d (basisVec s) + d (basisVec r + basisVec s) = 0 at hl
    have h1 := f2_add_self (h 0 0)
    have h2 := f2_add_self (h 0 (basisVec r))
    have h3 := f2_add_self (h 0 (basisVec s))
    have h4 := f2_add_self (d 0)
    have h7 := f2_add_self (d (basisVec r + basisVec s))
    linear_combination 2 * h1 + h2 + h3 + v * (h4 + hl - h7)

private lemma build_cubic_circuit_cost1 {k : ℕ} (G : SimpleGraph (Fin k))
    (h : F2 → (Fin k → F2) → F2) (p q : Fin k → F2)
    (hlab : ∀ i j : Fin k, G.Adj i j →
      (h 0 0 + h 1 0) + (h 0 (basisVec i) + h 1 (basisVec i)) +
      (h 0 (basisVec j) + h 1 (basisVec j)) +
      (h 0 (basisVec i + basisVec j) + h 1 (basisVec i + basisVec j)) = p i * q j + p j * q i) :
    ∃ (D : Circuit) (tap : Fin (k + 1) → ℕ),
      ReadsBack (k + 1) D ∧
      (∀ g ∈ D.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
      costGates D.gates ≤ 1 ∧
      D.output < k + 1 + D.size ∧
      (∀ j, tap j < k + 1 + D.size) ∧
      ∀ (v : F2) (z : Fin k → F2), isKey G z →
        let y : Fin (k + 1) → F2 := Fin.cons v z
        let inp := bitsOf (k + 1) y
        let pv : Fin (k + 1) → F2 := fun j => b2f3 ((D.wires inp).getD (tap j) false)
        b2f3 (D.eval inp) + dotProduct pv y = h v z := by
  let K := k + 1
  let h' : F2 → (Fin k → F2) → F2 := fun v z => h v z + v * (dotProduct p z * dotProduct q z)
  have hlab' : ∀ i j : Fin k, G.Adj i j →
      (h' 0 0 + h' 1 0) + (h' 0 (basisVec i) + h' 1 (basisVec i)) +
      (h' 0 (basisVec j) + h' 1 (basisVec j)) +
      (h' 0 (basisVec i + basisVec j) + h' 1 (basisVec i + basisVec j)) = 0 := by
    intro i j hadj
    have hdp : ∀ (w : Fin k → F2) (r : Fin k), dotProduct w (basisVec r) = w r := by
      intro w r
      unfold dotProduct
      rw [Finset.sum_eq_single r]
      · simp [basisVec]
      · intro t _ htr; simp [basisVec, htr]
      · intro hr; exact absurd (Finset.mem_univ r) hr
    have hdp2 : ∀ (w : Fin k → F2), dotProduct w (basisVec i + basisVec j) = w i + w j := by
      intro w; rw [dotProduct_add, hdp, hdp]
    have h0 : ∀ w : Fin k → F2, dotProduct w 0 = 0 := fun w => by simp [dotProduct]
    simp only [h', h0, hdp, hdp2, zero_mul, one_mul, add_zero]
    have hl := hlab i j hadj
    have h1 := f2_add_self (p i * q i)
    have h2 := f2_add_self (p j * q j)
    have h3 := f2_add_self (p i * q j + p j * q i)
    linear_combination hl + h1 + h2 + h3
  obtain ⟨D0, tap0, hrb0, hleg0, hc0, hout0, htap0, hval0⟩ := build_quad_circuit_cost0 G h' hlab'
  have hv0 : legalGates K D0.gates := ⟨hrb0, hleg0⟩
  obtain ⟨hvu, hcu, hlu, hwu_lt, hwu⟩ := buildAff3_spec D0.gates 0 (Fin.cons 0 p) hv0
  set uRes := buildAff3 D0.gates 0 (Fin.cons 0 p)
  obtain ⟨hvv, hcv, hlv, hwv_lt, hwv⟩ := buildAff3_spec uRes.1 0 (Fin.cons 0 q) hvu
  set vRes := buildAff3 uRes.1 0 (Fin.cons 0 q)
  let gand : Gate := ⟨GateOp.and, [uRes.2, vRes.2]⟩
  set gs3 := vRes.1 ++ [gand]
  set wand := K + vRes.1.length
  have hgs3_len : gs3.length = vRes.1.length + 1 := by simp [gs3]
  have hwu_lt2 : uRes.2 < K + vRes.1.length := by omega
  have hv3 : legalGates K gs3 :=
    legalGates_append_one hvv ⟨by simp [gand], Or.inl rfl⟩
      (by intro a ha; simp [gand] at ha; rcases ha with rfl | rfl; exact hwu_lt2; exact hwv_lt)
  have hcand : isNL3 gand = true := by simp [isNL3, gand]
  have hc3 : costGates gs3 = 1 := by
    change (vRes.1 ++ [gand]).countP isNL3 = 1
    rw [List.countP_append, List.countP_cons, List.countP_nil, hcand]
    have hv0c : vRes.1.countP isNL3 = 0 := by
      change costGates vRes.1 = 0
      rw [hcv, hcu, hc0]
    simp [hv0c]
  have htap0_0_lt3 : tap0 0 < K + gs3.length := by
    have := htap0 0; dsimp [Circuit.size] at this; omega
  have hwand_lt3 : wand < K + gs3.length := by omega
  obtain ⟨hv4, hc4, hl4, hwx_lt, hwx⟩ := buildXor3_spec K gs3 (tap0 0) wand hv3 htap0_0_lt3 hwand_lt3
  set xorRes := buildXor3 K gs3 (tap0 0) wand
  let D : Circuit := ⟨xorRes.1, D0.output⟩
  let tap : Fin K → ℕ := fun j => if j = 0 then xorRes.2 else tap0 j
  have hlen_all : D0.gates.length ≤ xorRes.1.length := by omega
  refine ⟨D, tap, hv4.1, hv4.2, by rw [hc4, hc3], by dsimp [D, Circuit.size]; dsimp [Circuit.size] at hout0; omega, ?_, ?_⟩
  · intro j
    by_cases hj : j = 0
    · simp only [tap, hj, ↓reduceIte]; exact hwx_lt
    · simp only [tap, hj, ↓reduceIte]; have := htap0 j; dsimp [D, Circuit.size] at *; omega
  · intro v z hz
    let y : Fin K → F2 := Fin.cons v z
    have hpre_gs3 : ∀ t < K + D0.gates.length,
        (wiresOf gs3 (bitsOf K y)).getD t false = (D0.wires (bitsOf K y)).getD t false := by
      intro t ht
      rw [wiresOf_snoc, getD_snoc_lt _ _ t (by rw [wiresOf_len, bitsOf_len]; omega)]
      rw [(hwv y).1 t (by omega), (hwu y).1 t ht]; rfl
    have hpre_all : ∀ t < K + D0.gates.length,
        (D.wires (bitsOf K y)).getD t false = (D0.wires (bitsOf K y)).getD t false := by
      intro t ht
      change (wiresOf xorRes.1 (bitsOf K y)).getD t false = _
      rw [(hwx (bitsOf K y) (bitsOf_len K y)).1 t (by omega), hpre_gs3 t ht]
    have hwand_val : b2f3 ((wiresOf gs3 (bitsOf K y)).getD wand false) = dotProduct p z * dotProduct q z := by
      rw [wiresOf_snoc]
      have hidx : wand = (wiresOf vRes.1 (bitsOf K y)).length := by rw [wiresOf_len, bitsOf_len]
      rw [hidx, getD_snoc_self]
      simp only [gand, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, b2f3_and]
      rw [(hwv y).1 uRes.2 hwu_lt, (hwu y).2, (hwv y).2]
      simp [y, dotProduct, Fin.sum_univ_succ]
    have hout_eq : b2f3 (D.eval (bitsOf K y)) = b2f3 (D0.eval (bitsOf K y)) := by
      change b2f3 ((D.wires (bitsOf K y)).getD D0.output false) = _
      rw [hpre_all D0.output hout0]; rfl
    have htap0_eq : b2f3 ((D.wires (bitsOf K y)).getD (tap 0) false) =
        b2f3 ((D0.wires (bitsOf K y)).getD (tap0 0) false) + dotProduct p z * dotProduct q z := by
      simp only [tap, ↓reduceIte]
      change b2f3 ((wiresOf xorRes.1 (bitsOf K y)).getD xorRes.2 false) = _
      rw [(hwx (bitsOf K y) (bitsOf_len K y)).2, b2f3_xor, hpre_gs3 (tap0 0) (htap0 0), hwand_val]
    have htapi_eq : ∀ i : Fin k, b2f3 ((D.wires (bitsOf K y)).getD (tap i.succ) false) =
        b2f3 ((D0.wires (bitsOf K y)).getD (tap0 i.succ) false) := by
      intro i
      simp only [tap, Fin.succ_ne_zero, ↓reduceIte]
      rw [hpre_all (tap0 i.succ) (htap0 i.succ)]
    have hdot_eq : dotProduct (fun j => b2f3 ((D.wires (bitsOf K y)).getD (tap j) false)) y =
        dotProduct (fun j => b2f3 ((D0.wires (bitsOf K y)).getD (tap0 j) false)) y +
        v * (dotProduct p z * dotProduct q z) := by
      change (∑ j : Fin (k + 1), b2f3 ((D.wires (bitsOf K y)).getD (tap j) false) * y j) =
        (∑ j : Fin (k + 1), b2f3 ((D0.wires (bitsOf K y)).getD (tap0 j) false) * y j) +
        v * (dotProduct p z * dotProduct q z)
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ, htap0_eq]
      simp_rw [htapi_eq]
      simp only [y, Fin.cons_zero]
      ring
    change b2f3 (D.eval (bitsOf K y)) + dotProduct (fun j => b2f3 ((D.wires (bitsOf K y)).getD (tap j) false)) y = h v z
    rw [hout_eq, hdot_eq]
    have h0 := hval0 v z hz
    dsimp only [h'] at h0
    have hself := f2_add_self (v * (dotProduct p z * dotProduct q z))
    linear_combination h0 + hself

private lemma delta_quad_zero {k : ℕ} (f : (Fin (k + 1) → F2) → F2) (p : Fin (k + 1) → (Fin (k + 1) → F2) → F2)
    (hf : isAff3 f) (hp : ∀ m, isAff3 (p m)) (i j : Fin k) (hne : i ≠ j) :
    let qv : (Fin k → F2) → F2 := fun z =>
      (f (Fin.cons (0 : F2) z) + ∑ m : Fin (k + 1), (Fin.cons (0 : F2) z : Fin (k + 1) → F2) m * p m (Fin.cons (0 : F2) z)) +
      (f (Fin.cons (1 : F2) z) + ∑ m : Fin (k + 1), (Fin.cons (1 : F2) z : Fin (k + 1) → F2) m * p m (Fin.cons (1 : F2) z))
    qv 0 + qv (basisVec i) + qv (basisVec j) + qv (basisVec i + basisVec j) = 0 := by
  obtain ⟨cf, wf, hf⟩ := hf
  choose cp wp hp using hp
  dsimp only
  have hterm : ∀ z : Fin k → F2,
      (f (Fin.cons (0 : F2) z) + ∑ m : Fin (k + 1), (Fin.cons (0 : F2) z : Fin (k + 1) → F2) m * p m (Fin.cons (0 : F2) z)) +
      (f (Fin.cons (1 : F2) z) + ∑ m : Fin (k + 1), (Fin.cons (1 : F2) z : Fin (k + 1) → F2) m * p m (Fin.cons (1 : F2) z)) =
      (wf 0 + cp 0 + wp 0 0) + ∑ r : Fin k, (wp 0 r.succ + wp r.succ 0) * z r := by
    intro z
    rw [hf, hf]
    simp_rw [hp]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, dotProduct, zero_mul, mul_zero, one_mul, mul_one, zero_add]
    have hsum_diff :
        (∑ r : Fin k, z r * (cp r.succ + ∑ s : Fin k, wp r.succ s.succ * z s)) +
        (∑ r : Fin k, z r * (cp r.succ + (wp r.succ 0 + ∑ s : Fin k, wp r.succ s.succ * z s))) =
        ∑ r : Fin k, wp r.succ 0 * z r := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      have h1 := f2_add_self (z r * cp r.succ)
      have h2 := f2_add_self (z r * ∑ s : Fin k, wp r.succ s.succ * z s)
      linear_combination h1 + h2
    have hsum_combine :
        (∑ r : Fin k, wp 0 r.succ * z r) + (∑ r : Fin k, wp r.succ 0 * z r) =
        ∑ r : Fin k, (wp 0 r.succ + wp r.succ 0) * z r := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro r _; ring
    have hcf := f2_add_self cf
    have hwf := f2_add_self (∑ r : Fin k, wf r.succ * z r)
    linear_combination hcf + hwf + hsum_diff + hsum_combine
  simp_rw [hterm]
  have hlin : ∀ (c : F2) (w : Fin k → F2),
      (c + ∑ r : Fin k, w r * (0 : Fin k → F2) r) +
      (c + ∑ r : Fin k, w r * basisVec i r) +
      (c + ∑ r : Fin k, w r * basisVec j r) +
      (c + ∑ r : Fin k, w r * (basisVec i + basisVec j) r) = 0 := by
    intro c w
    have hsum_b : ∀ r0 : Fin k, (∑ r : Fin k, w r * basisVec r0 r) = w r0 := by
      intro r0
      rw [Finset.sum_eq_single r0]
      · simp [basisVec]
      · intro r _ hrr; simp [basisVec, hrr]
      · intro hr; exact absurd (Finset.mem_univ r0) hr
    have hsum_ij : (∑ r : Fin k, w r * (basisVec i + basisVec j) r) = w i + w j := by
      simp_rw [Pi.add_apply, mul_add, Finset.sum_add_distrib, hsum_b]
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, hsum_b, hsum_ij]
    have h1 := f2_add_self c
    have h2 := f2_add_self (w i)
    have h3 := f2_add_self (w j)
    linear_combination 2 * h1 + h2 + h3
  exact hlin _ _

private lemma delta_cubic_det {k : ℕ}
    (c1 c2 c3 a1 a2 a3 : F2) (w1 w2 w3 : Fin k → F2) :
    ∃ p q : Fin k → F2, ∀ i j : Fin k,
      let T : F2 → (Fin k → F2) → F2 := fun v z =>
        (c1 + a1 * v + dotProduct w1 z) *
        (c2 + a2 * v + dotProduct w2 z) *
        (c3 + a3 * v + dotProduct w3 z)
      let d : (Fin k → F2) → F2 := fun z => T 0 z + T 1 z
      d 0 + d (basisVec i) + d (basisVec j) + d (basisVec i + basisVec j) = p i * q j + p j * q i := by
  have hΔ : ∀ (i j : Fin k),
      let T : F2 → (Fin k → F2) → F2 := fun v z =>
        (c1 + a1 * v + dotProduct w1 z) *
        (c2 + a2 * v + dotProduct w2 z) *
        (c3 + a3 * v + dotProduct w3 z)
      let d : (Fin k → F2) → F2 := fun z => T 0 z + T 1 z
      d 0 + d (basisVec i) + d (basisVec j) + d (basisVec i + basisVec j) =
        a1 * (w2 i * w3 j + w2 j * w3 i) +
        a2 * (w1 i * w3 j + w1 j * w3 i) +
        a3 * (w1 i * w2 j + w1 j * w2 i) := by
    intro i j
    have hdp : ∀ (w : Fin k → F2) (r : Fin k), dotProduct w (basisVec r) = w r := by
      intro w r; unfold dotProduct
      rw [Finset.sum_eq_single r]
      · simp [basisVec]
      · intro t _ htr; simp [basisVec, htr]
      · intro hr; exact absurd (Finset.mem_univ r) hr
    have hdp2 : ∀ (w : Fin k → F2), dotProduct w (basisVec i + basisVec j) = w i + w j := by
      intro w; rw [dotProduct_add, hdp, hdp]
    have h0 : ∀ w : Fin k → F2, dotProduct w 0 = 0 := fun w => by simp [dotProduct]
    dsimp only
    simp only [h0, hdp, hdp2, mul_zero, mul_one, add_zero]
    generalize w1 i = x1; generalize w1 j = y1
    generalize w2 i = x2; generalize w2 j = y2
    generalize w3 i = x3; generalize w3 j = y3
    rcases zmod2_cases a1 with rfl | rfl <;>
    rcases zmod2_cases a2 with rfl | rfl <;>
    rcases zmod2_cases a3 with rfl | rfl <;>
    rcases zmod2_cases c1 with rfl | rfl <;>
    rcases zmod2_cases c2 with rfl | rfl <;>
    rcases zmod2_cases c3 with rfl | rfl <;>
    rcases zmod2_cases x1 with rfl | rfl <;>
    rcases zmod2_cases y1 with rfl | rfl <;>
    rcases zmod2_cases x2 with rfl | rfl <;>
    rcases zmod2_cases y2 with rfl | rfl <;>
    rcases zmod2_cases x3 with rfl | rfl <;>
    rcases zmod2_cases y3 with rfl | rfl <;> decide
  rcases zmod2_cases a1 with rfl | rfl <;>
  rcases zmod2_cases a2 with rfl | rfl <;>
  rcases zmod2_cases a3 with rfl | rfl
  · exact ⟨0, 0, fun i j => by have hd := hΔ i j; dsimp only at hd ⊢; rw [hd]; simp⟩
  · exact ⟨w1, w2, fun i j => by have hd := hΔ i j; dsimp only at hd ⊢; rw [hd]; simp⟩
  · exact ⟨w1, w3, fun i j => by have hd := hΔ i j; dsimp only at hd ⊢; rw [hd]; simp⟩
  · exact ⟨w1, w2 + w3, fun i j => by have hd := hΔ i j; dsimp only at hd ⊢; rw [hd]; simp [Pi.add_apply]; ring⟩
  · exact ⟨w2, w3, fun i j => by have hd := hΔ i j; dsimp only at hd ⊢; rw [hd]; simp⟩
  · exact ⟨w1 + w3, w2, fun i j => by have hd := hΔ i j; dsimp only at hd ⊢; rw [hd]; simp [Pi.add_apply]; ring⟩
  · exact ⟨w1 + w2, w3, fun i j => by have hd := hΔ i j; dsimp only at hd ⊢; rw [hd]; simp [Pi.add_apply]; ring⟩
  · refine ⟨w1 + w2, w1 + w3, fun i j => ?_⟩
    have hd := hΔ i j; dsimp only at hd ⊢; rw [hd]
    simp only [Pi.add_apply, one_mul]
    have h1 := f2_add_self (w1 i * w1 j)
    linear_combination -h1

private def pairToCol (a b : F2) : Fin 3 :=
  if a = 1 ∧ b = 0 then 0 else if a = 0 ∧ b = 1 then 1 else 2

private def colToPair (c : Fin 3) : F2 × F2 :=
  match c with
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (0, 1)
  | ⟨2, _⟩ => (1, 1)

private lemma pairToCol_ne_iff (a1 b1 a2 b2 : F2)
    (h1 : ¬ (a1 = 0 ∧ b1 = 0)) (h2 : ¬ (a2 = 0 ∧ b2 = 0)) :
    pairToCol a1 b1 ≠ pairToCol a2 b2 ↔ a1 * b2 + a2 * b1 = 1 := by
  rcases zmod2_cases a1 with rfl | rfl <;>
  rcases zmod2_cases b1 with rfl | rfl <;>
  rcases zmod2_cases a2 with rfl | rfl <;>
  rcases zmod2_cases b2 with rfl | rfl <;>
  simp_all [pairToCol] <;> decide

private lemma colToPair_det (c1 c2 : Fin 3) :
    (colToPair c1).1 * (colToPair c2).2 + (colToPair c2).1 * (colToPair c1).2 =
      if c1 ≠ c2 then (1 : F2) else 0 := by
  fin_cases c1 <;> fin_cases c2 <;> decide

private lemma main_33624 (k : ℕ) (G : SimpleGraph (Fin k)) :
    let F := ZMod 2
    let S := Fin k → F
    let V := Fin (k+1) → F
    let e := fun (i : Fin k) (j : Fin k) => if j = i then (1 : F) else 0
    let key := fun (z : S) => z = 0 ∨ (∃ i, z = e i) ∨ ∃ i j, G.Adj i j ∧ z = e i + e j
    let bits := fun (x : V) => List.ofFn (fun i => decide (x i = 1))
    let Circ := PEqualNP.CircuitLowerBounds.Circuit
    let fits := fun (p : ℕ) (C : Circ) =>
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*(k+1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
      C.gates.countP (fun g => @decide
        ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)) ≤ p
    let perfect := fun (p : ℕ) (h : F → S → F) => ∃ C : Circ, fits p C ∧
      ∀ (x : V) (v : F) (z : S), key z →
        let y : V := Fin.cons v z
        C.eval (bits x ++ bits y) = decide (dotProduct x y + h v z = 1)
    let hard := fun (v : F) (z : S) => if ((Finset.univ : Finset (Fin k)).filter
      (fun i => z i ≠ 0)).card = 2 then v else 0
    (∀ h : F → S → F,
      let d := fun (z : S) => h 0 z + h 1 z
      let label := fun i j => d 0 + d (e i) + d (e j) + d (e i + e j)
      let active := fun i => ∃ j, G.Adj i j ∧ label i j = 1
      (∀ p : ℕ, perfect p h → k+1 ≤ p) ∧
      (perfect (k+1) h ↔ ∀ i j, G.Adj i j → label i j = 0) ∧
      (perfect (k+2) h ↔ ∃ col : Fin k → Fin 3, ∀ i j, G.Adj i j → active i → active j →
        (col i ≠ col j ↔ label i j = 1))) ∧
    (perfect (k+2) hard ↔ ∃ col : Fin k → Fin 3, ∀ i j, G.Adj i j → col i ≠ col j) := by
  dsimp only
  have hmain : ∀ h : F2 → (Fin k → F2) → F2,
      let d := fun (z : Fin k → F2) => h 0 z + h 1 z
      let label := fun i j => d 0 + d (basisVec i) + d (basisVec j) + d (basisVec i + basisVec j)
      let active := fun i => ∃ j, G.Adj i j ∧ label i j = 1
      (∀ p : ℕ, (∃ C : Circuit,
        (ReadsBack (2*(k+1)) C ∧
          (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
            (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
          costGates C.gates ≤ p) ∧
        ∀ (x : Fin (k+1) → F2) (v : F2) (z : Fin k → F2), isKey G z →
          C.eval (bitsOf (k+1) x ++ bitsOf (k+1) (Fin.cons v z)) =
            decide (dotProduct x (Fin.cons v z) + h v z = 1)) → k+1 ≤ p) ∧
      ((∃ C : Circuit,
        (ReadsBack (2*(k+1)) C ∧
          (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
            (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
          costGates C.gates ≤ k+1) ∧
        ∀ (x : Fin (k+1) → F2) (v : F2) (z : Fin k → F2), isKey G z →
          C.eval (bitsOf (k+1) x ++ bitsOf (k+1) (Fin.cons v z)) =
            decide (dotProduct x (Fin.cons v z) + h v z = 1)) ↔
        ∀ i j, G.Adj i j → label i j = 0) ∧
      ((∃ C : Circuit,
        (ReadsBack (2*(k+1)) C ∧
          (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
            (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
          costGates C.gates ≤ k+2) ∧
        ∀ (x : Fin (k+1) → F2) (v : F2) (z : Fin k → F2), isKey G z →
          C.eval (bitsOf (k+1) x ++ bitsOf (k+1) (Fin.cons v z)) =
            decide (dotProduct x (Fin.cons v z) + h v z = 1)) ↔
        ∃ col : Fin k → Fin 3, ∀ i j, G.Adj i j → active i → active j →
          (col i ≠ col j ↔ label i j = 1)) := by
    intro h
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · intro p ⟨C, ⟨hrb, hleg, hcost⟩, hev⟩
      exact ((atom_iff_perfect G p h).mp ⟨C, hrb, hleg, hcost, hev⟩).1
    · constructor
      · rintro ⟨C, ⟨hrb, hleg, hcost⟩, hev⟩
        obtain ⟨_, D, tap, hrbD, hlegD, hcostD, _, _, hvalD⟩ :=
          (atom_iff_perfect G (k + 1) h).mp ⟨C, hrb, hleg, hcost, hev⟩
        have hc0 : costGates D.gates = 0 := by omega
        have hf_aff := circuit_wires_cost0 D hrbD hlegD hc0 D.output
        have hp_aff : ∀ m : Fin (k + 1), isAff3 (fun y => b2f3 ((D.wires (bitsOf (k + 1) y)).getD (tap m) false)) :=
          fun m => circuit_wires_cost0 D hrbD hlegD hc0 (tap m)
        intro i j hadj
        have h1 := delta_quad_zero (fun y => b2f3 (D.eval (bitsOf (k + 1) y)))
          (fun m y => b2f3 ((D.wires (bitsOf (k + 1) y)).getD (tap m) false)) hf_aff hp_aff i j (G.ne_of_adj hadj)
        have hmatch : ∀ z, isKey G z →
            h 0 z + h 1 z =
              (b2f3 (D.eval (bitsOf (k + 1) (Fin.cons (0 : F2) z))) +
                ∑ m : Fin (k + 1), (Fin.cons (0 : F2) z : Fin (k + 1) → F2) m * b2f3 ((D.wires (bitsOf (k + 1) (Fin.cons (0 : F2) z))).getD (tap m) false)) +
              (b2f3 (D.eval (bitsOf (k + 1) (Fin.cons (1 : F2) z))) +
                ∑ m : Fin (k + 1), (Fin.cons (1 : F2) z : Fin (k + 1) → F2) m * b2f3 ((D.wires (bitsOf (k + 1) (Fin.cons (1 : F2) z))).getD (tap m) false)) := by
          intro z hz
          have e0 := hvalD 0 z hz
          have e1 := hvalD 1 z hz
          dsimp only [dotProduct] at e0 e1
          rw [← e0, ← e1]
          congr 1 <;> congr 1 <;> apply Finset.sum_congr rfl <;> intro m _ <;> ring
        rw [hmatch 0 (Or.inl rfl), hmatch (basisVec i) (Or.inr (Or.inl ⟨i, rfl⟩)),
            hmatch (basisVec j) (Or.inr (Or.inl ⟨j, rfl⟩)),
            hmatch (basisVec i + basisVec j) (Or.inr (Or.inr ⟨i, j, hadj, rfl⟩))]
        exact h1
      · intro hlab
        obtain ⟨D, tap, hrbD, hlegD, hc0, houtD, htapD, hvalD⟩ := build_quad_circuit_cost0 G h hlab
        obtain ⟨C, hrb, hleg, hcost, hev⟩ := (atom_iff_perfect G (k + 1) h).mpr
          ⟨le_rfl, D, tap, hrbD, hlegD, by omega, houtD, htapD, hvalD⟩
        exact ⟨C, ⟨hrb, hleg, hcost⟩, hev⟩
    · constructor
      · rintro ⟨C, ⟨hrb, hleg, hcost⟩, hev⟩
        obtain ⟨_, D, tap, hrbD, hlegD, hcostD, _, _, hvalD⟩ :=
          (atom_iff_perfect G (k + 2) h).mp ⟨C, hrb, hleg, hcost, hev⟩
        have hc1 : costGates D.gates ≤ 1 := by omega
        obtain ⟨u, v, hu_aff, hv_aff, hwires⟩ := circuit_wires_cost1 D hrbD hlegD hc1
        obtain ⟨f0, b0, hf0, hD_out⟩ := hwires D.output
        choose pf af hpf hD_tap using fun m : Fin (k + 1) => hwires (tap m)
        obtain ⟨cu, wu, hu_eq⟩ := hu_aff
        obtain ⟨cv, wv, hv_eq⟩ := hv_aff
        obtain ⟨p, q, hdet⟩ := delta_cubic_det b0 cu cv (af 0) (wu 0) (wv 0)
          (fun r => af r.succ) (fun r => wu r.succ) (fun r => wv r.succ)
        have hlab_det : ∀ i j : Fin k, G.Adj i j →
            (h 0 0 + h 1 0) + (h 0 (basisVec i) + h 1 (basisVec i)) +
            (h 0 (basisVec j) + h 1 (basisVec j)) +
            (h 0 (basisVec i + basisVec j) + h 1 (basisVec i + basisVec j)) =
              p i * q j + p j * q i := by
          intro i j hadj
          have hq := delta_quad_zero f0 pf hf0 hpf i j (G.ne_of_adj hadj)
          have hmatch : ∀ z, isKey G z →
              h 0 z + h 1 z =
                ((f0 (Fin.cons (0 : F2) z) + ∑ m : Fin (k + 1), (Fin.cons (0 : F2) z : Fin (k + 1) → F2) m * pf m (Fin.cons (0 : F2) z)) +
                 (f0 (Fin.cons (1 : F2) z) + ∑ m : Fin (k + 1), (Fin.cons (1 : F2) z : Fin (k + 1) → F2) m * pf m (Fin.cons (1 : F2) z))) +
                (((b0 + af 0 * 0 + dotProduct (fun r => af r.succ) z) *
                  (cu + wu 0 * 0 + dotProduct (fun r => wu r.succ) z) *
                  (cv + wv 0 * 0 + dotProduct (fun r => wv r.succ) z)) +
                 ((b0 + af 0 * 1 + dotProduct (fun r => af r.succ) z) *
                  (cu + wu 0 * 1 + dotProduct (fun r => wu r.succ) z) *
                  (cv + wv 0 * 1 + dotProduct (fun r => wv r.succ) z))) := by
            intro z hz
            have heval_pt : ∀ t : F2,
                h t z = (f0 (Fin.cons t z) + ∑ m : Fin (k + 1), (Fin.cons t z : Fin (k + 1) → F2) m * pf m (Fin.cons t z)) +
                  (b0 + af 0 * t + dotProduct (fun r => af r.succ) z) *
                  (cu + wu 0 * t + dotProduct (fun r => wu r.succ) z) *
                  (cv + wv 0 * t + dotProduct (fun r => wv r.succ) z) := by
              intro t
              have ht := hvalD t z hz
              dsimp only at ht
              rw [← ht]
              change b2f3 ((D.wires (bitsOf (k + 1) (Fin.cons t z))).getD D.output false) +
                dotProduct (fun m => b2f3 ((D.wires (bitsOf (k + 1) (Fin.cons t z))).getD (tap m) false)) (Fin.cons t z) = _
              rw [hD_out (Fin.cons t z)]
              have hdt : dotProduct (fun m => b2f3 ((D.wires (bitsOf (k + 1) (Fin.cons t z))).getD (tap m) false)) (Fin.cons t z) =
                  (∑ m : Fin (k + 1), (Fin.cons t z : Fin (k + 1) → F2) m * pf m (Fin.cons t z)) +
                  (af 0 * t + dotProduct (fun r => af r.succ) z) * (u (Fin.cons t z) * v (Fin.cons t z)) := by
                unfold dotProduct
                simp_rw [hD_tap]
                have h1 : ∑ m : Fin (k + 1), (pf m (Fin.cons t z) + af m * (u (Fin.cons t z) * v (Fin.cons t z))) * (Fin.cons t z : Fin (k + 1) → F2) m =
                    (∑ m : Fin (k + 1), (Fin.cons t z : Fin (k + 1) → F2) m * pf m (Fin.cons t z)) +
                    (∑ m : Fin (k + 1), af m * (Fin.cons t z : Fin (k + 1) → F2) m) * (u (Fin.cons t z) * v (Fin.cons t z)) := by
                  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl; intro m _; ring
                have h2 : ∑ m : Fin (k + 1), af m * (Fin.cons t z : Fin (k + 1) → F2) m =
                    af 0 * t + dotProduct (fun r => af r.succ) z := by
                  rw [Fin.sum_univ_succ]
                  simp [dotProduct, Fin.cons_zero, Fin.cons_succ]
                rw [h1, h2]; rfl
              rw [hdt, hu_eq, hv_eq]
              simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
              ring
            rw [heval_pt 0, heval_pt 1]; ring
          rw [hmatch 0 (Or.inl rfl), hmatch (basisVec i) (Or.inr (Or.inl ⟨i, rfl⟩)),
              hmatch (basisVec j) (Or.inr (Or.inl ⟨j, rfl⟩)),
              hmatch (basisVec i + basisVec j) (Or.inr (Or.inr ⟨i, j, hadj, rfl⟩))]
          have hd := hdet i j
          dsimp only at hq hd
          linear_combination hq + hd
        refine ⟨fun i => pairToCol (p i) (q i), ?_⟩
        intro i j hadj hi hj
        have hnz_i : ¬ (p i = 0 ∧ q i = 0) := by
          rintro ⟨hp0, hq0⟩
          obtain ⟨r, hadjr, h1⟩ := hi
          have := hlab_det i r hadjr
          rw [hp0, hq0] at this; simp at this; rw [this] at h1; exact absurd h1 (by decide)
        have hnz_j : ¬ (p j = 0 ∧ q j = 0) := by
          rintro ⟨hp0, hq0⟩
          obtain ⟨r, hadjr, h1⟩ := hj
          have := hlab_det j r hadjr
          rw [hp0, hq0] at this; simp at this; rw [this] at h1; exact absurd h1 (by decide)
        rw [pairToCol_ne_iff (p i) (q i) (p j) (q j) hnz_i hnz_j, ← hlab_det i j hadj]
      · rintro ⟨col, hcol⟩
        classical
        let act : Fin k → Prop := fun i => ∃ j, G.Adj i j ∧
          (h 0 0 + h 1 0) + (h 0 (basisVec i) + h 1 (basisVec i)) +
          (h 0 (basisVec j) + h 1 (basisVec j)) +
          (h 0 (basisVec i + basisVec j) + h 1 (basisVec i + basisVec j)) = 1
        let p : Fin k → F2 := fun i => if act i then (colToPair (col i)).1 else 0
        let q : Fin k → F2 := fun i => if act i then (colToPair (col i)).2 else 0
        have hlab_eq : ∀ i j : Fin k, G.Adj i j →
            (h 0 0 + h 1 0) + (h 0 (basisVec i) + h 1 (basisVec i)) +
            (h 0 (basisVec j) + h 1 (basisVec j)) +
            (h 0 (basisVec i + basisVec j) + h 1 (basisVec i + basisVec j)) = p i * q j + p j * q i := by
          intro i j hadj
          by_cases hi : act i
          · by_cases hj : act j
            · simp only [p, q, hi, hj, ↓reduceIte, colToPair_det]
              have hiff := hcol i j hadj hi hj
              by_cases hne : col i ≠ col j
              · simp [hne, hiff.mp hne]
              · simp only [hne, ↓reduceIte]
                have hne1 : (h 0 0 + h 1 0) + (h 0 (basisVec i) + h 1 (basisVec i)) +
                    (h 0 (basisVec j) + h 1 (basisVec j)) +
                    (h 0 (basisVec i + basisVec j) + h 1 (basisVec i + basisVec j)) ≠ 1 :=
                  fun h1 => hne (hiff.mpr h1)
                rcases zmod2_cases ((h 0 0 + h 1 0) + (h 0 (basisVec i) + h 1 (basisVec i)) +
                    (h 0 (basisVec j) + h 1 (basisVec j)) +
                    (h 0 (basisVec i + basisVec j) + h 1 (basisVec i + basisVec j))) with h0 | h1
                · exact h0
                · exact absurd h1 hne1
            · simp only [p, q, hj, ↓reduceIte, mul_zero, zero_mul, add_zero]
              have hne1 : (h 0 0 + h 1 0) + (h 0 (basisVec i) + h 1 (basisVec i)) +
                  (h 0 (basisVec j) + h 1 (basisVec j)) +
                  (h 0 (basisVec i + basisVec j) + h 1 (basisVec i + basisVec j)) ≠ 1 := by
                intro h1
                apply hj
                refine ⟨i, hadj.symm, ?_⟩
                rw [add_comm (basisVec j) (basisVec i)]
                linear_combination h1
              rcases zmod2_cases ((h 0 0 + h 1 0) + (h 0 (basisVec i) + h 1 (basisVec i)) +
                  (h 0 (basisVec j) + h 1 (basisVec j)) +
                  (h 0 (basisVec i + basisVec j) + h 1 (basisVec i + basisVec j))) with h0 | h1
              · exact h0
              · exact absurd h1 hne1
          · simp only [p, q, hi, ↓reduceIte, mul_zero, zero_mul, add_zero]
            have hne1 : (h 0 0 + h 1 0) + (h 0 (basisVec i) + h 1 (basisVec i)) +
                (h 0 (basisVec j) + h 1 (basisVec j)) +
                (h 0 (basisVec i + basisVec j) + h 1 (basisVec i + basisVec j)) ≠ 1 :=
              fun h1 => hi ⟨j, hadj, h1⟩
            rcases zmod2_cases ((h 0 0 + h 1 0) + (h 0 (basisVec i) + h 1 (basisVec i)) +
                (h 0 (basisVec j) + h 1 (basisVec j)) +
                (h 0 (basisVec i + basisVec j) + h 1 (basisVec i + basisVec j))) with h0 | h1
            · exact h0
            · exact absurd h1 hne1
        obtain ⟨D, tap, hrbD, hlegD, hc1, houtD, htapD, hvalD⟩ := build_cubic_circuit_cost1 G h p q hlab_eq
        obtain ⟨C, hrb, hleg, hcost, hev⟩ := (atom_iff_perfect G (k + 2) h).mpr
          ⟨by omega, D, tap, hrbD, hlegD, by omega, houtD, htapD, hvalD⟩
        exact ⟨C, ⟨hrb, hleg, hcost⟩, hev⟩
  refine ⟨hmain, ?_⟩
  let hard : F2 → (Fin k → F2) → F2 := fun v z =>
    if ((Finset.univ : Finset (Fin k)).filter (fun i => z i ≠ 0)).card = 2 then v else 0
  have hhard_label : ∀ i j : Fin k, G.Adj i j →
      (hard 0 0 + hard 1 0) + (hard 0 (basisVec i) + hard 1 (basisVec i)) +
      (hard 0 (basisVec j) + hard 1 (basisVec j)) +
      (hard 0 (basisVec i + basisVec j) + hard 1 (basisVec i + basisVec j)) = 1 := by
    intro i j hadj
    have hne : i ≠ j := G.ne_of_adj hadj
    have hc0 : ((Finset.univ : Finset (Fin k)).filter (fun r => (0 : Fin k → F2) r ≠ 0)).card = 0 := by
      simp
    have hc1 : ∀ r0 : Fin k, ((Finset.univ : Finset (Fin k)).filter (fun r => basisVec r0 r ≠ 0)).card = 1 := by
      intro r0
      have hset : (Finset.univ : Finset (Fin k)).filter (fun r => basisVec r0 r ≠ 0) = {r0} := by
        apply Finset.ext
        intro r
        rw [Finset.mem_filter, Finset.mem_singleton]
        simp only [Finset.mem_univ, true_and, basisVec]
        by_cases h : r = r0
        · subst h; simp
        · simp [h]
      rw [hset, Finset.card_singleton]
    have hc2 : ((Finset.univ : Finset (Fin k)).filter (fun r => (basisVec i + basisVec j) r ≠ 0)).card = 2 := by
      have hset : (Finset.univ : Finset (Fin k)).filter (fun r => (basisVec i + basisVec j) r ≠ 0) = {i, j} := by
        apply Finset.ext
        intro r
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        simp only [Finset.mem_univ, true_and, Pi.add_apply, basisVec]
        by_cases hri : r = i
        · subst hri; simp [hne]
        · by_cases hrj : r = j
          · subst hrj; simp [hri]
          · simp [hri, hrj]
      rw [hset, Finset.card_pair hne]
    simp only [hard, hc0, hc1, hc2]
    decide
  refine (hmain hard).2.2.trans ?_
  dsimp only
  constructor
  · rintro ⟨col, hcol⟩
    refine ⟨col, fun i j hadj => ?_⟩
    have hi : ∃ r, G.Adj i r ∧
        (hard 0 0 + hard 1 0) + (hard 0 (basisVec i) + hard 1 (basisVec i)) +
        (hard 0 (basisVec r) + hard 1 (basisVec r)) +
        (hard 0 (basisVec i + basisVec r) + hard 1 (basisVec i + basisVec r)) = 1 :=
      ⟨j, hadj, hhard_label i j hadj⟩
    have hj : ∃ r, G.Adj j r ∧
        (hard 0 0 + hard 1 0) + (hard 0 (basisVec j) + hard 1 (basisVec j)) +
        (hard 0 (basisVec r) + hard 1 (basisVec r)) +
        (hard 0 (basisVec j + basisVec r) + hard 1 (basisVec j + basisVec r)) = 1 :=
      ⟨i, hadj.symm, hhard_label j i hadj.symm⟩
    exact (hcol i j hadj hi hj).mpr (hhard_label i j hadj)
  · rintro ⟨col, hcol⟩
    refine ⟨col, fun i j hadj _ _ => ?_⟩
    rw [hhard_label i j hadj]
    exact ⟨fun _ => rfl, fun _ => hcol i j hadj⟩

end Part33624

end PEqualNP.Outside.L_meta_33624_aux

theorem PEqualNP.Outside.L_meta_33624 : (∀ (k : ℕ) (G : SimpleGraph (Fin k)),
  let F := ZMod 2
  let S := Fin k → F
  let V := Fin (k+1) → F
  let e := fun (i : Fin k) (j : Fin k) => if j = i then (1 : F) else 0
  let key := fun (z : S) => z = 0 ∨ (∃ i, z = e i) ∨ ∃ i j, G.Adj i j ∧ z = e i + e j
  let bits := fun (x : V) => List.ofFn (fun i => decide (x i = 1))
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let fits := fun (p : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*(k+1)) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
    C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)) ≤ p
  let perfect := fun (p : ℕ) (h : F → S → F) => ∃ C : Circ, fits p C ∧
    ∀ (x : V) (v : F) (z : S), key z →
      let y : V := Fin.cons v z
      C.eval (bits x ++ bits y) = decide (dotProduct x y + h v z = 1)
  let hard := fun (v : F) (z : S) => if ((Finset.univ : Finset (Fin k)).filter
    (fun i => z i ≠ 0)).card = 2 then v else 0
  (∀ h : F → S → F,
    let d := fun (z : S) => h 0 z + h 1 z
    let label := fun i j => d 0 + d (e i) + d (e j) + d (e i + e j)
    let active := fun i => ∃ j, G.Adj i j ∧ label i j = 1
    (∀ p : ℕ, perfect p h → k+1 ≤ p) ∧
    (perfect (k+1) h ↔ ∀ i j, G.Adj i j → label i j = 0) ∧
    (perfect (k+2) h ↔ ∃ col : Fin k → Fin 3, ∀ i j, G.Adj i j → active i → active j →
      (col i ≠ col j ↔ label i j = 1))) ∧
  (perfect (k+2) hard ↔ ∃ col : Fin k → Fin 3, ∀ i j, G.Adj i j → col i ≠ col j)) := PEqualNP.Outside.L_meta_33624_aux.main_33624
