import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33649

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

abbrev Branch (k t : ℕ) :=
  ℕ × Submodule F2 (Fin k → F2) × List Gate × (Fin k → ℕ) × (ℕ → ℕ) × (ℕ → (Fin k → F2))

def branchPos {k t : ℕ} (B : Branch k t) (z : Fin t → F2) (j : Fin k) : F2 :=
  if (wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.1 j) false then 1 else 0

def ValidBranch {k t : ℕ} (gs : List Gate) (B : Branch k t) : Prop :=
  Module.finrank F2 B.2.1 + B.1 = k ∧
  legalGates t B.2.2.1 ∧
  costGates B.2.2.1 + B.1 ≤ costGates gs ∧
  (∀ j : Fin k, B.2.2.2.1 j < t + B.2.2.1.length) ∧
  (∀ w < k + t + gs.length, B.2.2.2.2.1 w < t + B.2.2.1.length) ∧
  (∀ w < k + t + gs.length, ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ B.2.1 →
    (wiresOf gs (bitsOf k ((branchPos B) z + u) ++ bitsOf t z)).getD w false =
      Bool.xor ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 w) false)
        (decide (dotProduct (B.2.2.2.2.2 w) u = 1)))

lemma branch_eval_add_gate {k t : ℕ} {gs : List Gate} {g : Gate} {B : Branch k t}
    (_hleg : legalGates (k + t) (gs ++ [g]))
    (hB : ValidBranch gs B)
    (gs' : List Gate) (ext : List Gate) (hgs' : gs' = B.2.2.1 ++ ext)
    (hleg' : legalGates t gs')
    (hcost' : costGates gs' + B.1 ≤ costGates (gs ++ [g]))
    (wNew : ℕ) (hwNew : wNew < t + gs'.length) (sNew : Fin k → F2)
    (hsemNew : ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ B.2.1 →
      g.op.eval (g.inputs.map fun i => (wiresOf gs (bitsOf k ((branchPos B) z + u) ++ bitsOf t z)).getD i false) =
        Bool.xor ((wiresOf gs' (bitsOf t z)).getD wNew false) (decide (dotProduct sNew u = 1))) :
    let B' : Branch k t :=
      ⟨B.1, B.2.1, gs', B.2.2.2.1,
        fun w => if w = k + t + gs.length then wNew else B.2.2.2.2.1 w,
        fun w => if w = k + t + gs.length then sNew else B.2.2.2.2.2 w⟩
    ValidBranch (gs ++ [g]) B' ∧
      ∀ z : Fin t → F2, (branchPos B') z = (branchPos B) z := by
  intro B'
  have hpos_eq : ∀ z : Fin t → F2, (branchPos B') z = (branchPos B) z := by
    intro z; funext j
    simp only [branchPos, B', hgs']
    rw [wiresOf_append_getD_lt B.2.2.1 ext (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.1 j)]
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
    have hlen_in : (bitsOf k ((branchPos B) z + u) ++ bitsOf t z).length = k + t := by
      simp [bitsOf_len]
    by_cases hweq : w = k + t + gs.length
    · subst hweq
      simp only [B', ↓reduceIte]
      have hidx : k + t + gs.length = (bitsOf k ((branchPos B) z + u) ++ bitsOf t z).length + gs.length := by omega
      rw [hidx, wiresOf_snoc_last]
      exact hsemNew z u hu
    · simp only [B', hweq, ↓reduceIte]
      rw [wiresOf_append_getD_lt gs [g] _ (by rw [hlen_in]; omega)]
      rw [hgs', wiresOf_append_getD_lt B.2.2.1 ext (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 w (by omega))]
      exact hB.2.2.2.2.2 w (by omega) z u hu

lemma step_single_branch {k t : ℕ} {gs : List Gate} {g : Gate} (B : Branch k t)
    (hleg : legalGates (k + t) (gs ++ [g])) (hB : ValidBranch gs B) :
    ∃ L : List (Branch k t),
      (∀ B' ∈ L, ValidBranch (gs ++ [g]) B') ∧
      ∀ (z : Fin t → F2) (x : Fin k → F2),
        (x - (branchPos B) z ∈ B.2.1 → ∃! idx : Fin L.length, x - (branchPos (L.get idx)) z ∈ (L.get idx).2.1) ∧
        (x - (branchPos B) z ∉ B.2.1 → ∀ idx : Fin L.length, x - (branchPos (L.get idx)) z ∉ (L.get idx).2.1) := by
  have hpre := legalGates_prefix hleg
  have hback := hpre.2.1
  have hshape := hpre.2.2
  have hcost_ge : costGates gs ≤ costGates (gs ++ [g]) := by
    rw [costGates_append]; omega
  have hwrap_one : ∀ (B' : Branch k t), ValidBranch (gs ++ [g]) B' → B'.2.1 = B.2.1 →
      (∀ z, (branchPos B') z = (branchPos B) z) →
      ∃ L : List (Branch k t),
        (∀ b ∈ L, ValidBranch (gs ++ [g]) b) ∧
        ∀ (z : Fin t → F2) (x : Fin k → F2),
          (x - (branchPos B) z ∈ B.2.1 → ∃! idx : Fin L.length, x - (branchPos (L.get idx)) z ∈ (L.get idx).2.1) ∧
          (x - (branchPos B) z ∉ B.2.1 → ∀ idx : Fin L.length, x - (branchPos (L.get idx)) z ∉ (L.get idx).2.1) := by
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
      let gs' := B.2.2.1 ++ [⟨.and, []⟩]
      have hleg' : legalGates t gs' :=
        legalGates_snoc hB.2.1 (by simp) ⟨by simp, Or.inl rfl⟩
      have hcost' : costGates gs' + B.1 ≤ costGates (gs ++ [g]) := by
        rw [costGates_snoc_zero B.2.2.1 _ (by simp)]; have := hB.2.2.1; omega
      have hres := branch_eval_add_gate hleg hB gs' [⟨.and, []⟩] rfl hleg' hcost'
        (t + B.2.2.1.length) (by simp [gs']) 0 (fun z u _ => by
          rw [hop, hg]
          have hidx : t + B.2.2.1.length = (bitsOf t z).length + B.2.2.1.length := by rw [bitsOf_len]
          rw [hidx, wiresOf_snoc_last]; simp [GateOp.eval])
      exact hwrap_one _ hres.1 rfl hres.2
    · rcases rest with _ | ⟨w1, rest2⟩
      ·
        have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        have hres := branch_eval_add_gate hleg hB B.2.2.1 [] (by simp) hB.2.1
          (by have := hB.2.2.1; omega) (B.2.2.2.2.1 w0) (hB.2.2.2.2.1 w0 hw0) (B.2.2.2.2.2 w0)
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
          by_cases hvan : (∀ u ∈ B.2.1, dotProduct (B.2.2.2.2.2 w0) u = 0) ∧
              (∀ u ∈ B.2.1, dotProduct (B.2.2.2.2.2 w1) u = 0)
          ·
            let gs' := B.2.2.1 ++ [⟨.and, [B.2.2.2.2.1 w0, B.2.2.2.2.1 w1]⟩]
            have hleg' : legalGates t gs' :=
              legalGates_snoc hB.2.1
                (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hB.2.2.2.2.1 w0 hw0; exact hB.2.2.2.2.1 w1 hw1)
                ⟨by simp, Or.inl rfl⟩
            have hcost' : costGates gs' + B.1 ≤ costGates (gs ++ [g]) := by
              rw [costGates_snoc_one B.2.2.1 _ ⟨Or.inl rfl, rfl⟩, hcost1]; have := hB.2.2.1; omega
            have hres := branch_eval_add_gate hleg hB gs' [⟨.and, [B.2.2.2.2.1 w0, B.2.2.2.2.1 w1]⟩] rfl hleg' hcost'
              (t + B.2.2.1.length) (by simp [gs']) 0 (fun z u hu => by
                rw [hop, hg]
                have hidx : t + B.2.2.1.length = (bitsOf t z).length + B.2.2.1.length := by rw [bitsOf_len]
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
                ∃ v0 ∈ B.2.1, dotProduct (B.2.2.2.2.2 wa) v0 = 1 := by
              by_cases h0 : ∀ u ∈ B.2.1, dotProduct (B.2.2.2.2.2 w0) u = 0
              · have h1 : ¬ ∀ u ∈ B.2.1, dotProduct (B.2.2.2.2.2 w1) u = 0 := fun h => hvan ⟨h0, h⟩
                push Not at h1
                rcases h1 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.2.2.2.2.2 w1) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.2.2.2.2.2 w1) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w1, w0, hw1, hw0, Or.inr ⟨rfl, rfl⟩, v0, hv0, hd1⟩
              · push Not at h0
                rcases h0 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.2.2.2.2.2 w0) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.2.2.2.2.2 w0) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w0, w1, hw0, hw1, Or.inl ⟨rfl, rfl⟩, v0, hv0, hd1⟩
            rcases hex with ⟨wa, wb, hwa, hwb, hwab, v0, hv0, hdot⟩
            let U' : Submodule F2 (Fin k → F2) := kerDot B.2.1 (B.2.2.2.2.2 wa)
            have hdim' : Module.finrank F2 U' + (B.1 + 1) = k := by
              have h1 : Module.finrank F2 U' + 1 = Module.finrank F2 B.2.1 :=
                finrank_ker_dot B.2.1 (B.2.2.2.2.2 wa) v0 hv0 hdot
              have h2 := hB.1
              omega
            have hbuild_child : ∀ (b : Bool), ∃ Bc : Branch k t,
                ValidBranch (gs ++ [g]) Bc ∧ Bc.2.1 = U' ∧
                ∀ z : Fin t → F2,
                  (branchPos Bc) z = (branchPos B) z +
                    (if Bool.xor b ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false) then (1 : F2) else 0) • v0 := by
              intro b
              let gs0 := if b then B.2.2.1 ++ [⟨.not, [B.2.2.2.2.1 wa]⟩] else B.2.2.1
              let cWire := if b then t + B.2.2.1.length else B.2.2.2.2.1 wa
              have hgs0_ext : ∃ e0, gs0 = B.2.2.1 ++ e0 := by
                cases b
                · exact ⟨[], by simp [gs0]⟩
                · exact ⟨[⟨.not, [B.2.2.2.2.1 wa]⟩], rfl⟩
              have hgs0_leg : legalGates t gs0 := by
                cases b
                · exact hB.2.1
                · exact legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 wa hwa)
                    ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
              have hgs0_cost : costGates gs0 = costGates B.2.2.1 := by
                cases b
                · rfl
                · exact costGates_snoc_zero B.2.2.1 _ (by simp)
              have hcWire_lt : cWire < t + gs0.length := by
                cases b
                · exact hB.2.2.2.2.1 wa hwa
                · simp [gs0, cWire]
              have hcWire_sem : ∀ z : Fin t → F2,
                  (wiresOf gs0 (bitsOf t z)).getD cWire false =
                    Bool.xor b ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false) := by
                intro z
                cases b
                · simp [gs0, cWire]
                · simp only [gs0, cWire, ↓reduceIte]
                  have hidx : t + B.2.2.1.length = (bitsOf t z).length + B.2.2.1.length := by rw [bitsOf_len]
                  rw [hidx, wiresOf_snoc_last]
                  simp [GateOp.eval]
              let tapOld : ℕ → ℕ := fun j => if hj : j < k then B.2.2.2.1 ⟨j, hj⟩ else 0
              let flagTap : ℕ → Bool := fun j => if hj : j < k then decide (v0 ⟨j, hj⟩ = 1) else false
              let resT := addXorMany t cWire flagTap tapOld k gs0
              have hresT := addXorMany_spec t cWire flagTap tapOld k gs0 hgs0_leg hcWire_lt
                (fun j hj => by
                  simp only [tapOld, hj, ↓reduceDIte]
                  rcases hgs0_ext with ⟨e0, he0⟩
                  rw [he0, List.length_append]
                  have := hB.2.2.2.1 ⟨j, hj⟩; omega)
              rcases hresT with ⟨extT, hTeq, hTleg, hTcost, hTlt, hTsem⟩
              let flagOff : ℕ → Bool := fun w => decide (dotProduct (B.2.2.2.2.2 w) v0 = 1)
              let resO := addXorMany t cWire flagOff B.2.2.2.2.1 (k + t + gs.length) resT.1
              have hresO := addXorMany_spec t cWire flagOff B.2.2.2.2.1 (k + t + gs.length) resT.1 hTleg
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
              have hgsF_cost : costGates gsF = costGates B.2.2.1 := by
                cases b
                · rw [show gsF = resO.1 ++ [⟨.or, []⟩] from rfl, costGates_snoc_zero _ _ (by simp), hOcost, hTcost, hgs0_cost]
                · simp only [gsF, ↓reduceIte]; rw [hOcost, hTcost, hgs0_cost]
              let tapF : Fin k → ℕ := fun j => resT.2 j.val
              let wNew := if b then resO.2 wb else t + resO.1.length
              let sNew : Fin k → F2 := if b then B.2.2.2.2.2 wb else 0
              let Bc : Branch k t :=
                ⟨B.1 + 1, U', gsF, tapF,
                  fun w => if w = k + t + gs.length then wNew else resO.2 w,
                  fun w => if w = k + t + gs.length then sNew else B.2.2.2.2.2 w⟩
              have hpos_c : ∀ z : Fin t → F2,
                  (branchPos Bc) z = (branchPos B) z +
                    (if Bool.xor b ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false) then (1 : F2) else 0) • v0 := by
                intro z; funext j
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                have htap_val : (wiresOf gsF (bitsOf t z)).getD (tapF j) false =
                    (wiresOf resT.1 (bitsOf t z)).getD (resT.2 j.val) false := by
                  rw [heF, hOeq, List.append_assoc,
                      wiresOf_append_getD_lt resT.1 _ (bitsOf t z) (by rw [bitsOf_len]; exact hTlt j.val j.isLt)]
                simp only [branchPos, Bc, htap_val]
                rw [hTsem j.val j.isLt (bitsOf t z) (bitsOf_len t z)]
                simp only [flagTap, tapOld, j.isLt, ↓reduceDIte, hcWire_sem z]
                rw [he0, wiresOf_append_getD_lt B.2.2.1 e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.1 j)]
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, branchPos]
                cases (wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.1 j) false <;>
                  cases Bool.xor b ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false) <;>
                  rcases zmod2_cases (v0 j) with h | h <;> simp [h] <;> decide
              have hsem_old : ∀ w < k + t + gs.length, ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ U' →
                  (wiresOf gs (bitsOf k ((branchPos Bc) z + u) ++ bitsOf t z)).getD w false =
                    Bool.xor ((wiresOf gsF (bitsOf t z)).getD (resO.2 w) false)
                      (decide (dotProduct (B.2.2.2.2.2 w) u = 1)) := by
                intro w hw z u hu
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                set cbit := Bool.xor b ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false)
                set cf : F2 := if cbit then 1 else 0
                have hu_in_B : cf • v0 + u ∈ B.2.1 := B.2.1.add_mem (B.2.1.smul_mem cf hv0) hu.1
                have hpos_rw : (branchPos Bc) z + u = (branchPos B) z + (cf • v0 + u) := by
                  rw [hpos_c z, add_assoc]
                rw [hpos_rw, hB.2.2.2.2.2 w hw z (cf • v0 + u) hu_in_B]
                have hwireO : (wiresOf gsF (bitsOf t z)).getD (resO.2 w) false =
                    if decide (dotProduct (B.2.2.2.2.2 w) v0 = 1) then
                      Bool.xor ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 w) false) cbit
                    else (wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 w) false := by
                  rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt w hw)]
                  rw [hOsem w hw (bitsOf t z) (bitsOf_len t z)]
                  rw [hTeq,
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 w hw; omega),
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                  rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.2.2.1 e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 w hw)]
                rw [hwireO, dotProduct_add, dotProduct_smul, zmod2_add_decide, smul_eq_mul, zmod2_mul_decide, zmod2_bool_decide]
                cases (wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 w) false <;>
                  cases cbit <;> cases decide (dotProduct (B.2.2.2.2.2 w) v0 = 1) <;>
                  cases decide (dotProduct (B.2.2.2.2.2 w) u = 1) <;> decide
              refine ⟨Bc, ⟨hdim', hgsF_leg, by change costGates gsF + (B.1 + 1) ≤ costGates (gs ++ [g]); rw [hgsF_cost, hcost1]; have := hB.2.2.1; omega, ?_, ?_, ?_⟩, rfl, hpos_c⟩
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
                have hlen_in : (bitsOf k ((branchPos Bc) z + u) ++ bitsOf t z).length = k + t := by simp [bitsOf_len]
                by_cases hweq : w = k + t + gs.length
                · subst hweq
                  simp only [Bc, ↓reduceIte]
                  rw [wiresOf_snoc_last_eq gs g _ hlen_in, hop, hg]
                  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                    id_eq, Bool.and_true]
                  have hwa_val : (wiresOf gs (bitsOf k ((branchPos Bc) z + u) ++ bitsOf t z)).getD wa false = b := by
                    have hu2 : dotProduct (B.2.2.2.2.2 wa) u = 0 := hu.2
                    rw [hsem_old wa hwa z u hu, hu2]
                    rcases hgsF_ext with ⟨eF, heF⟩
                    rcases hgs0_ext with ⟨e0, he0⟩
                    rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt wa hwa)]
                    rw [hOsem wa hwa (bitsOf t z) (bitsOf_len t z)]
                    simp only [flagOff, hdot]
                    rw [hTeq,
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 wa hwa; omega),
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                    rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.2.2.1 e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 wa hwa)]
                    cases b <;> cases (wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false <;> decide
                  have hcomm : ((wiresOf gs (bitsOf k ((branchPos Bc) z + u) ++ bitsOf t z)).getD w0 false &&
                      (wiresOf gs (bitsOf k ((branchPos Bc) z + u) ++ bitsOf t z)).getD w1 false) =
                      ((wiresOf gs (bitsOf k ((branchPos Bc) z + u) ++ bitsOf t z)).getD wa false &&
                       (wiresOf gs (bitsOf k ((branchPos Bc) z + u) ++ bitsOf t z)).getD wb false) := by
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
              have hmem_iff : ∀ (b : Bool) (Bc : Branch k t), Bc.2.1 = U' →
                  (branchPos Bc) z = (branchPos B) z + (if Bool.xor b ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false) then (1 : F2) else 0) • v0 →
                  (x - (branchPos Bc) z ∈ Bc.2.1 ↔
                    x - (branchPos B) z ∈ B.2.1 ∧
                      b = Bool.xor ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false)
                        (decide (dotProduct (B.2.2.2.2.2 wa) (x - (branchPos B) z) = 1))) := by
                intro b Bc hUc hpc
                set ow := (wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false
                set cb := Bool.xor b ow
                set cf : F2 := if cb then 1 else 0
                have hdiff : x - (branchPos Bc) z = (x - (branchPos B) z) + cf • v0 := by
                  rw [hpc, zmod2_vec_sub_eq_add, zmod2_vec_sub_eq_add, add_assoc]
                rw [hUc, hdiff, mem_kerDot]
                constructor
                · rintro ⟨h1, h2⟩
                  have h1' : x - (branchPos B) z ∈ B.2.1 := by
                    have := B.2.1.add_mem h1 (B.2.1.smul_mem cf hv0)
                    rw [add_assoc, zmod2_vec_add_self, add_zero] at this
                    exact this
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one] at h2
                  exact ⟨h1', (zmod2_xor_zero_iff b ow _).mp h2⟩
                · rintro ⟨h1, h2⟩
                  refine ⟨B.2.1.add_mem h1 (B.2.1.smul_mem cf hv0), ?_⟩
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one]
                  exact (zmod2_xor_zero_iff b ow _).mpr h2
              constructor
              · intro hx
                cases htarget : Bool.xor ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false)
                    (decide (dotProduct (B.2.2.2.2.2 wa) (x - (branchPos B) z) = 1))
                · refine ⟨⟨0, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff false B0 hU0 (hpos0 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exact Fin.ext hv
                    · exfalso
                      have hm : x - (branchPos B1) z ∈ B1.2.1 := by simpa [hv] using hidx
                      have := ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).2
                      rw [htarget] at this; simp at this
                · refine ⟨⟨1, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff true B1 hU1 (hpos1 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exfalso
                      have hm : x - (branchPos B0) z ∈ B0.2.1 := by simpa [hv] using hidx
                      have := ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).2
                      rw [htarget] at this; exact Bool.false_ne_true this
                    · exact Fin.ext hv
              · intro hnx idx hidx
                have hlt : idx.val < 2 := idx.isLt
                interval_cases hv : idx.val
                · have hm : x - (branchPos B0) z ∈ B0.2.1 := by simpa [hv] using hidx
                  exact hnx ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).1
                · have hm : x - (branchPos B1) z ∈ B1.2.1 := by simpa [hv] using hidx
                  exact hnx ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).1
        · exfalso; have := hshape.1; rw [hg] at this; simp at this
  ·
    rcases hg : g.inputs with _ | ⟨w0, rest⟩
    ·
      let gs' := B.2.2.1 ++ [⟨.or, []⟩]
      have hleg' : legalGates t gs' :=
        legalGates_snoc hB.2.1 (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
      have hcost' : costGates gs' + B.1 ≤ costGates (gs ++ [g]) := by
        rw [costGates_snoc_zero B.2.2.1 _ (by simp)]; have := hB.2.2.1; omega
      have hres := branch_eval_add_gate hleg hB gs' [⟨.or, []⟩] rfl hleg' hcost'
        (t + B.2.2.1.length) (by simp [gs']) 0 (fun z u _ => by
          rw [hop, hg]
          have hidx : t + B.2.2.1.length = (bitsOf t z).length + B.2.2.1.length := by rw [bitsOf_len]
          rw [hidx, wiresOf_snoc_last]; simp [GateOp.eval])
      exact hwrap_one _ hres.1 rfl hres.2
    · rcases rest with _ | ⟨w1, rest2⟩
      ·
        have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        have hres := branch_eval_add_gate hleg hB B.2.2.1 [] (by simp) hB.2.1
          (by have := hB.2.2.1; omega) (B.2.2.2.2.1 w0) (hB.2.2.2.2.1 w0 hw0) (B.2.2.2.2.2 w0)
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
          by_cases hvan : (∀ u ∈ B.2.1, dotProduct (B.2.2.2.2.2 w0) u = 0) ∧
              (∀ u ∈ B.2.1, dotProduct (B.2.2.2.2.2 w1) u = 0)
          · let gs' := B.2.2.1 ++ [⟨.or, [B.2.2.2.2.1 w0, B.2.2.2.2.1 w1]⟩]
            have hleg' : legalGates t gs' :=
              legalGates_snoc hB.2.1
                (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hB.2.2.2.2.1 w0 hw0; exact hB.2.2.2.2.1 w1 hw1)
                ⟨by simp, Or.inr (Or.inl rfl)⟩
            have hcost' : costGates gs' + B.1 ≤ costGates (gs ++ [g]) := by
              rw [costGates_snoc_one B.2.2.1 _ ⟨Or.inr rfl, rfl⟩, hcost1]; have := hB.2.2.1; omega
            have hres := branch_eval_add_gate hleg hB gs' [⟨.or, [B.2.2.2.2.1 w0, B.2.2.2.2.1 w1]⟩] rfl hleg' hcost'
              (t + B.2.2.1.length) (by simp [gs']) 0 (fun z u hu => by
                rw [hop, hg]
                have hidx : t + B.2.2.1.length = (bitsOf t z).length + B.2.2.1.length := by rw [bitsOf_len]
                rw [hidx, wiresOf_snoc_last]
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                  id_eq, Bool.or_false]
                rw [hB.2.2.2.2.2 w0 hw0 z u hu, hB.2.2.2.2.2 w1 hw1 z u hu,
                    hvan.1 u hu, hvan.2 u hu]
                simp)
            exact hwrap_one _ hres.1 rfl hres.2
          · have hex : ∃ (wa wb : ℕ), wa < k + t + gs.length ∧ wb < k + t + gs.length ∧
                ((wa = w0 ∧ wb = w1) ∨ (wa = w1 ∧ wb = w0)) ∧
                ∃ v0 ∈ B.2.1, dotProduct (B.2.2.2.2.2 wa) v0 = 1 := by
              by_cases h0 : ∀ u ∈ B.2.1, dotProduct (B.2.2.2.2.2 w0) u = 0
              · have h1 : ¬ ∀ u ∈ B.2.1, dotProduct (B.2.2.2.2.2 w1) u = 0 := fun h => hvan ⟨h0, h⟩
                push Not at h1
                rcases h1 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.2.2.2.2.2 w1) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.2.2.2.2.2 w1) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w1, w0, hw1, hw0, Or.inr ⟨rfl, rfl⟩, v0, hv0, hd1⟩
              · push Not at h0
                rcases h0 with ⟨v0, hv0, hne⟩
                have hd1 : dotProduct (B.2.2.2.2.2 w0) v0 = 1 := by
                  rcases zmod2_cases (dotProduct (B.2.2.2.2.2 w0) v0) with h | h
                  · exact absurd h hne
                  · exact h
                exact ⟨w0, w1, hw0, hw1, Or.inl ⟨rfl, rfl⟩, v0, hv0, hd1⟩
            rcases hex with ⟨wa, wb, hwa, hwb, hwab, v0, hv0, hdot⟩
            let U' : Submodule F2 (Fin k → F2) := kerDot B.2.1 (B.2.2.2.2.2 wa)
            have hdim' : Module.finrank F2 U' + (B.1 + 1) = k := by
              have h1 : Module.finrank F2 U' + 1 = Module.finrank F2 B.2.1 :=
                finrank_ker_dot B.2.1 (B.2.2.2.2.2 wa) v0 hv0 hdot
              have h2 := hB.1
              omega
            have hbuild_child : ∀ (b : Bool), ∃ Bc : Branch k t,
                ValidBranch (gs ++ [g]) Bc ∧ Bc.2.1 = U' ∧
                ∀ z : Fin t → F2,
                  (branchPos Bc) z = (branchPos B) z +
                    (if Bool.xor b ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false) then (1 : F2) else 0) • v0 := by
              intro b
              let gs0 := if b then B.2.2.1 ++ [⟨.not, [B.2.2.2.2.1 wa]⟩] else B.2.2.1
              let cWire := if b then t + B.2.2.1.length else B.2.2.2.2.1 wa
              have hgs0_ext : ∃ e0, gs0 = B.2.2.1 ++ e0 := by
                cases b
                · exact ⟨[], by simp [gs0]⟩
                · exact ⟨[⟨.not, [B.2.2.2.2.1 wa]⟩], rfl⟩
              have hgs0_leg : legalGates t gs0 := by
                cases b
                · exact hB.2.1
                · exact legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 wa hwa)
                    ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
              have hgs0_cost : costGates gs0 = costGates B.2.2.1 := by
                cases b
                · rfl
                · exact costGates_snoc_zero B.2.2.1 _ (by simp)
              have hcWire_lt : cWire < t + gs0.length := by
                cases b
                · exact hB.2.2.2.2.1 wa hwa
                · simp [gs0, cWire]
              have hcWire_sem : ∀ z : Fin t → F2,
                  (wiresOf gs0 (bitsOf t z)).getD cWire false =
                    Bool.xor b ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false) := by
                intro z
                cases b
                · simp [gs0, cWire]
                · simp only [gs0, cWire, ↓reduceIte]
                  have hidx : t + B.2.2.1.length = (bitsOf t z).length + B.2.2.1.length := by rw [bitsOf_len]
                  rw [hidx, wiresOf_snoc_last]
                  simp [GateOp.eval]
              let tapOld : ℕ → ℕ := fun j => if hj : j < k then B.2.2.2.1 ⟨j, hj⟩ else 0
              let flagTap : ℕ → Bool := fun j => if hj : j < k then decide (v0 ⟨j, hj⟩ = 1) else false
              let resT := addXorMany t cWire flagTap tapOld k gs0
              have hresT := addXorMany_spec t cWire flagTap tapOld k gs0 hgs0_leg hcWire_lt
                (fun j hj => by
                  simp only [tapOld, hj, ↓reduceDIte]
                  rcases hgs0_ext with ⟨e0, he0⟩
                  rw [he0, List.length_append]
                  have := hB.2.2.2.1 ⟨j, hj⟩; omega)
              rcases hresT with ⟨extT, hTeq, hTleg, hTcost, hTlt, hTsem⟩
              let flagOff : ℕ → Bool := fun w => decide (dotProduct (B.2.2.2.2.2 w) v0 = 1)
              let resO := addXorMany t cWire flagOff B.2.2.2.2.1 (k + t + gs.length) resT.1
              have hresO := addXorMany_spec t cWire flagOff B.2.2.2.2.1 (k + t + gs.length) resT.1 hTleg
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
              have hgsF_cost : costGates gsF = costGates B.2.2.1 := by
                cases b
                · simp only [gsF, Bool.false_eq_true, ↓reduceIte]; rw [hOcost, hTcost, hgs0_cost]
                · rw [show gsF = resO.1 ++ [⟨.and, []⟩] from rfl, costGates_snoc_zero _ _ (by simp), hOcost, hTcost, hgs0_cost]
              let tapF : Fin k → ℕ := fun j => resT.2 j.val
              let wNew := if b then t + resO.1.length else resO.2 wb
              let sNew : Fin k → F2 := if b then 0 else B.2.2.2.2.2 wb
              let Bc : Branch k t :=
                ⟨B.1 + 1, U', gsF, tapF,
                  fun w => if w = k + t + gs.length then wNew else resO.2 w,
                  fun w => if w = k + t + gs.length then sNew else B.2.2.2.2.2 w⟩
              have hpos_c : ∀ z : Fin t → F2,
                  (branchPos Bc) z = (branchPos B) z +
                    (if Bool.xor b ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false) then (1 : F2) else 0) • v0 := by
                intro z; funext j
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                have htap_val : (wiresOf gsF (bitsOf t z)).getD (tapF j) false =
                    (wiresOf resT.1 (bitsOf t z)).getD (resT.2 j.val) false := by
                  rw [heF, hOeq, List.append_assoc,
                      wiresOf_append_getD_lt resT.1 _ (bitsOf t z) (by rw [bitsOf_len]; exact hTlt j.val j.isLt)]
                simp only [branchPos, Bc, htap_val]
                rw [hTsem j.val j.isLt (bitsOf t z) (bitsOf_len t z)]
                simp only [flagTap, tapOld, j.isLt, ↓reduceDIte, hcWire_sem z]
                rw [he0, wiresOf_append_getD_lt B.2.2.1 e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.1 j)]
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, branchPos]
                cases (wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.1 j) false <;>
                  cases Bool.xor b ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false) <;>
                  rcases zmod2_cases (v0 j) with h | h <;> simp [h] <;> decide
              have hsem_old : ∀ w < k + t + gs.length, ∀ (z : Fin t → F2) (u : Fin k → F2), u ∈ U' →
                  (wiresOf gs (bitsOf k ((branchPos Bc) z + u) ++ bitsOf t z)).getD w false =
                    Bool.xor ((wiresOf gsF (bitsOf t z)).getD (resO.2 w) false)
                      (decide (dotProduct (B.2.2.2.2.2 w) u = 1)) := by
                intro w hw z u hu
                rcases hgsF_ext with ⟨eF, heF⟩
                rcases hgs0_ext with ⟨e0, he0⟩
                set cbit := Bool.xor b ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false)
                set cf : F2 := if cbit then 1 else 0
                have hu_in_B : cf • v0 + u ∈ B.2.1 := B.2.1.add_mem (B.2.1.smul_mem cf hv0) hu.1
                have hpos_rw : (branchPos Bc) z + u = (branchPos B) z + (cf • v0 + u) := by
                  rw [hpos_c z, add_assoc]
                rw [hpos_rw, hB.2.2.2.2.2 w hw z (cf • v0 + u) hu_in_B]
                have hwireO : (wiresOf gsF (bitsOf t z)).getD (resO.2 w) false =
                    if decide (dotProduct (B.2.2.2.2.2 w) v0 = 1) then
                      Bool.xor ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 w) false) cbit
                    else (wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 w) false := by
                  rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt w hw)]
                  rw [hOsem w hw (bitsOf t z) (bitsOf_len t z)]
                  rw [hTeq,
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 w hw; omega),
                      wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                  rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.2.2.1 e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 w hw)]
                rw [hwireO, dotProduct_add, dotProduct_smul, zmod2_add_decide, smul_eq_mul, zmod2_mul_decide, zmod2_bool_decide]
                cases (wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 w) false <;>
                  cases cbit <;> cases decide (dotProduct (B.2.2.2.2.2 w) v0 = 1) <;>
                  cases decide (dotProduct (B.2.2.2.2.2 w) u = 1) <;> decide
              refine ⟨Bc, ⟨hdim', hgsF_leg, by change costGates gsF + (B.1 + 1) ≤ costGates (gs ++ [g]); rw [hgsF_cost, hcost1]; have := hB.2.2.1; omega, ?_, ?_, ?_⟩, rfl, hpos_c⟩
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
                have hlen_in : (bitsOf k ((branchPos Bc) z + u) ++ bitsOf t z).length = k + t := by simp [bitsOf_len]
                by_cases hweq : w = k + t + gs.length
                · subst hweq
                  simp only [Bc, ↓reduceIte]
                  rw [wiresOf_snoc_last_eq gs g _ hlen_in, hop, hg]
                  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
                    id_eq, Bool.or_false]
                  have hwa_val : (wiresOf gs (bitsOf k ((branchPos Bc) z + u) ++ bitsOf t z)).getD wa false = b := by
                    have hu2 : dotProduct (B.2.2.2.2.2 wa) u = 0 := hu.2
                    rw [hsem_old wa hwa z u hu, hu2]
                    rcases hgsF_ext with ⟨eF, heF⟩
                    rcases hgs0_ext with ⟨e0, he0⟩
                    rw [heF, wiresOf_append_getD_lt resO.1 eF (bitsOf t z) (by rw [bitsOf_len]; exact hOlt wa hwa)]
                    rw [hOsem wa hwa (bitsOf t z) (bitsOf_len t z)]
                    simp only [flagOff, hdot]
                    rw [hTeq,
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len, he0, List.length_append]; have := hB.2.2.2.2.1 wa hwa; omega),
                        wiresOf_append_getD_lt gs0 extT (bitsOf t z) (by rw [bitsOf_len]; exact hcWire_lt)]
                    rw [hcWire_sem z, he0, wiresOf_append_getD_lt B.2.2.1 e0 (bitsOf t z) (by rw [bitsOf_len]; exact hB.2.2.2.2.1 wa hwa)]
                    cases b <;> cases (wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false <;> decide
                  have hcomm : ((wiresOf gs (bitsOf k ((branchPos Bc) z + u) ++ bitsOf t z)).getD w0 false ||
                      (wiresOf gs (bitsOf k ((branchPos Bc) z + u) ++ bitsOf t z)).getD w1 false) =
                      ((wiresOf gs (bitsOf k ((branchPos Bc) z + u) ++ bitsOf t z)).getD wa false ||
                       (wiresOf gs (bitsOf k ((branchPos Bc) z + u) ++ bitsOf t z)).getD wb false) := by
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
              have hmem_iff : ∀ (b : Bool) (Bc : Branch k t), Bc.2.1 = U' →
                  (branchPos Bc) z = (branchPos B) z + (if Bool.xor b ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false) then (1 : F2) else 0) • v0 →
                  (x - (branchPos Bc) z ∈ Bc.2.1 ↔
                    x - (branchPos B) z ∈ B.2.1 ∧
                      b = Bool.xor ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false)
                        (decide (dotProduct (B.2.2.2.2.2 wa) (x - (branchPos B) z) = 1))) := by
                intro b Bc hUc hpc
                set ow := (wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false
                set cb := Bool.xor b ow
                set cf : F2 := if cb then 1 else 0
                have hdiff : x - (branchPos Bc) z = (x - (branchPos B) z) + cf • v0 := by
                  rw [hpc, zmod2_vec_sub_eq_add, zmod2_vec_sub_eq_add, add_assoc]
                rw [hUc, hdiff, mem_kerDot]
                constructor
                · rintro ⟨h1, h2⟩
                  have h1' : x - (branchPos B) z ∈ B.2.1 := by
                    have := B.2.1.add_mem h1 (B.2.1.smul_mem cf hv0)
                    rw [add_assoc, zmod2_vec_add_self, add_zero] at this
                    exact this
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one] at h2
                  exact ⟨h1', (zmod2_xor_zero_iff b ow _).mp h2⟩
                · rintro ⟨h1, h2⟩
                  refine ⟨B.2.1.add_mem h1 (B.2.1.smul_mem cf hv0), ?_⟩
                  rw [dotProduct_add, dotProduct_smul, hdot, smul_eq_mul, mul_one]
                  exact (zmod2_xor_zero_iff b ow _).mpr h2
              constructor
              · intro hx
                cases htarget : Bool.xor ((wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 wa) false)
                    (decide (dotProduct (B.2.2.2.2.2 wa) (x - (branchPos B) z) = 1))
                · refine ⟨⟨0, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff false B0 hU0 (hpos0 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exact Fin.ext hv
                    · exfalso
                      have hm : x - (branchPos B1) z ∈ B1.2.1 := by simpa [hv] using hidx
                      have := ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).2
                      rw [htarget] at this; simp at this
                · refine ⟨⟨1, by simp⟩, ?_, ?_⟩
                  · exact (hmem_iff true B1 hU1 (hpos1 z)).mpr ⟨hx, htarget.symm⟩
                  · intro idx hidx
                    have hlt : idx.val < 2 := idx.isLt
                    interval_cases hv : idx.val
                    · exfalso
                      have hm : x - (branchPos B0) z ∈ B0.2.1 := by simpa [hv] using hidx
                      have := ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).2
                      rw [htarget] at this; exact Bool.false_ne_true this
                    · exact Fin.ext hv
              · intro hnx idx hidx
                have hlt : idx.val < 2 := idx.isLt
                interval_cases hv : idx.val
                · have hm : x - (branchPos B0) z ∈ B0.2.1 := by simpa [hv] using hidx
                  exact hnx ((hmem_iff false B0 hU0 (hpos0 z)).mp hm).1
                · have hm : x - (branchPos B1) z ∈ B1.2.1 := by simpa [hv] using hidx
                  exact hnx ((hmem_iff true B1 hU1 (hpos1 z)).mp hm).1
        · exfalso; have := hshape.1; rw [hg] at this; simp at this
  ·
    rcases hg : g.inputs with _ | ⟨w0, rest⟩
    ·
      let gs' := B.2.2.1 ++ [⟨.mod 2, []⟩]
      have hleg' : legalGates t gs' :=
        legalGates_snoc hB.2.1 (by simp) ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩
      have hcost' : costGates gs' + B.1 ≤ costGates (gs ++ [g]) := by
        rw [costGates_snoc_zero B.2.2.1 _ (by simp)]; have := hB.2.2.1; omega
      have hres := branch_eval_add_gate hleg hB gs' [⟨.mod 2, []⟩] rfl hleg' hcost'
        (t + B.2.2.1.length) (by simp [gs']) 0 (fun z u _ => by
          rw [hop, hg]
          have hidx : t + B.2.2.1.length = (bitsOf t z).length + B.2.2.1.length := by rw [bitsOf_len]
          rw [hidx, wiresOf_snoc_last]; simp [GateOp.eval])
      exact hwrap_one _ hres.1 rfl hres.2
    · rcases rest with _ | ⟨w1, rest2⟩
      ·
        have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        let gs' := B.2.2.1 ++ [⟨.not, [B.2.2.2.2.1 w0]⟩]
        have hleg' : legalGates t gs' :=
          legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 w0 hw0)
            ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
        have hcost' : costGates gs' + B.1 ≤ costGates (gs ++ [g]) := by
          rw [costGates_snoc_zero B.2.2.1 _ (by simp)]; have := hB.2.2.1; omega
        have hres := branch_eval_add_gate hleg hB gs' [⟨.not, [B.2.2.2.2.1 w0]⟩] rfl hleg' hcost'
          (t + B.2.2.1.length) (by simp [gs']) (B.2.2.2.2.2 w0) (fun z u hu => by
            rw [hop, hg]
            have hidx : t + B.2.2.1.length = (bitsOf t z).length + B.2.2.1.length := by rw [bitsOf_len]
            rw [hidx, wiresOf_snoc_last]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
            rw [hB.2.2.2.2.2 w0 hw0 z u hu]
            cases (wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 w0) false <;>
              cases decide (dotProduct (B.2.2.2.2.2 w0) u = 1) <;> decide)
        exact hwrap_one _ hres.1 rfl hres.2
      · rcases rest2 with _ | ⟨_, _⟩
        ·
          have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
          have hw1 : w1 < k + t + gs.length := hback w1 (by rw [hg]; simp)
          let gs' := B.2.2.1 ++ [⟨.mod 2, [B.2.2.2.2.1 w0, B.2.2.2.2.1 w1]⟩]
          have hleg' : legalGates t gs' :=
            legalGates_snoc hB.2.1
              (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hB.2.2.2.2.1 w0 hw0; exact hB.2.2.2.2.1 w1 hw1)
              ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩
          have hcost' : costGates gs' + B.1 ≤ costGates (gs ++ [g]) := by
            rw [costGates_snoc_zero B.2.2.1 _ (by simp)]; have := hB.2.2.1; omega
          have hres := branch_eval_add_gate hleg hB gs' [⟨.mod 2, [B.2.2.2.2.1 w0, B.2.2.2.2.1 w1]⟩] rfl hleg' hcost'
            (t + B.2.2.1.length) (by simp [gs']) (B.2.2.2.2.2 w0 + B.2.2.2.2.2 w1) (fun z u hu => by
              rw [hop, hg]
              have hidx : t + B.2.2.1.length = (bitsOf t z).length + B.2.2.1.length := by rw [bitsOf_len]
              rw [hidx, wiresOf_snoc_last]
              simp only [List.map_cons, List.map_nil, GateOp.eval]
              rw [hB.2.2.2.2.2 w0 hw0 z u hu, hB.2.2.2.2.2 w1 hw1 z u hu, add_dotProduct, zmod2_add_decide]
              cases (wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 w0) false <;>
                cases (wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 w1) false <;>
                cases decide (dotProduct (B.2.2.2.2.2 w0) u = 1) <;>
                cases decide (dotProduct (B.2.2.2.2.2 w1) u = 1) <;> decide)
          exact hwrap_one _ hres.1 rfl hres.2
        · exfalso; have := hshape.1; rw [hg] at this; simp at this
  ·
    rcases hg : g.inputs with _ | ⟨w0, rest⟩
    · simp [hg] at hlen1
    · rcases rest with _ | ⟨_, _⟩
      · have hw0 : w0 < k + t + gs.length := hback w0 (by rw [hg]; simp)
        let gs' := B.2.2.1 ++ [⟨.not, [B.2.2.2.2.1 w0]⟩]
        have hleg' : legalGates t gs' :=
          legalGates_snoc hB.2.1 (fun i hi => by simp at hi; subst hi; exact hB.2.2.2.2.1 w0 hw0)
            ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
        have hcost' : costGates gs' + B.1 ≤ costGates (gs ++ [g]) := by
          rw [costGates_snoc_zero B.2.2.1 _ (by simp)]; have := hB.2.2.1; omega
        have hres := branch_eval_add_gate hleg hB gs' [⟨.not, [B.2.2.2.2.1 w0]⟩] rfl hleg' hcost'
          (t + B.2.2.1.length) (by simp [gs']) (B.2.2.2.2.2 w0) (fun z u hu => by
            rw [hop, hg]
            have hidx : t + B.2.2.1.length = (bitsOf t z).length + B.2.2.1.length := by rw [bitsOf_len]
            rw [hidx, wiresOf_snoc_last]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
            rw [hB.2.2.2.2.2 w0 hw0 z u hu]
            cases (wiresOf B.2.2.1 (bitsOf t z)).getD (B.2.2.2.2.1 w0) false <;>
              cases decide (dotProduct (B.2.2.2.2.2 w0) u = 1) <;> decide)
        exact hwrap_one _ hres.1 rfl hres.2
      · simp [hg] at hlen1

lemma build_branch_list (k t : ℕ) (gs : List Gate) (hleg : legalGates (k + t) gs) :
    ∃ L : List (Branch k t),
      0 < L.length ∧
      (∀ B ∈ L, ValidBranch gs B) ∧
      ∀ (z : Fin t → F2) (x : Fin k → F2),
        ∃! idx : Fin L.length, x - (branchPos (L.get idx)) z ∈ (L.get idx).2.1 := by
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
    have hpos0 : ∀ z : Fin t → F2, (branchPos B0) z = 0 := by
      intro z; funext j
      simp only [branchPos, B0, Pi.zero_apply, hg0_val z]
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
          (x - (branchPos (L.get idx)) z ∈ (L.get idx).2.1 → ∃! j : Fin Lc.length, x - (branchPos (Lc.get j)) z ∈ (Lc.get j).2.1) ∧
          (x - (branchPos (L.get idx)) z ∉ (L.get idx).2.1 → ∀ j : Fin Lc.length, x - (branchPos (Lc.get j)) z ∉ (Lc.get j).2.1) :=
      fun idx => step_single_branch (L.get idx) hleg (hLval _ (List.get_mem L idx))
    let children : Fin L.length → List (Branch k t) := fun idx => (hstep_all idx).choose
    have hchildren_spec : ∀ idx : Fin L.length,
        (∀ B' ∈ children idx, ValidBranch (gs ++ [g]) B') ∧
        ∀ (z : Fin t → F2) (x : Fin k → F2),
          (x - (branchPos (L.get idx)) z ∈ (L.get idx).2.1 →
            ∃! j : Fin (children idx).length, x - (branchPos ((children idx).get j)) z ∈ ((children idx).get j).2.1) ∧
          (x - (branchPos (L.get idx)) z ∉ (L.get idx).2.1 →
            ∀ j : Fin (children idx).length, x - (branchPos ((children idx).get j)) z ∉ ((children idx).get j).2.1) :=
      fun idx => (hstep_all idx).choose_spec
    let L' : List (Branch k t) := (List.finRange L.length).flatMap children
    have hpart_L' : ∀ (z : Fin t → F2) (x : Fin k → F2),
        ∃! idx' : Fin L'.length, x - (branchPos (L'.get idx')) z ∈ (L'.get idx').2.1 := by
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
        (fun B => x - (branchPos B) z ∈ B.2.1)
      refine ⟨idx0, List.mem_finRange idx0, ((hchildren_spec idx0).2 z x).1 hidx0, ?_⟩
      intro idx2 _ hne2
      have hnot2 : x - (branchPos (L.get idx2)) z ∉ (L.get idx2).2.1 := fun hm => hne2 (hidx0u idx2 hm)
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
      fun i => (L.get i).1,
      fun i => (L.get i).2.1,
      fun i => (L.get i).2.2.2.2.2 C.output,
      fun i => ⟨(L.get i).2.2.1, (L.get i).2.2.2.2.1 C.output⟩,
      fun i => (L.get i).2.2.2.1,
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
      fun i => (L.get i).1,
      fun i => (L.get i).2.1,
      fun _ => 0,
      fun i => ⟨(L.get i).2.2.1 ++ [⟨.or, []⟩], t + (L.get i).2.2.1.length⟩,
      fun i => (L.get i).2.2.2.1,
      hLpos, ?_, ?_, ?_⟩
    · intro i
      have hBi := hLval (L.get i) (List.get_mem L i)
      refine ⟨hBi.1, ?_, ?_, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
      · exact legalGates_snoc hBi.2.1 (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
      · have hc0 := costGates_snoc_zero (L.get i).2.2.1 ⟨.or, []⟩ (by simp)
        have := hBi.2.2.1
        change costGates ((L.get i).2.2.1 ++ [⟨.or, []⟩]) + (L.get i).1 ≤
          costGates C.gates
        omega
      · intro j
        simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, List.length_singleton]
        have := hBi.2.2.2.1 j; omega
    · intro z x
      have hpeq : ∀ i : Fin L.length,
          (fun j : Fin k => if (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨(L.get i).2.2.1 ++ [⟨.or, []⟩], t + (L.get i).2.2.1.length⟩ (bits t z)).getD ((L.get i).2.2.2.1 j) false then (1 : F) else 0) =
          (branchPos (L.get i)) z := by
        intro i; funext j
        have hBi := hLval (L.get i) (List.get_mem L i)
        change (if (wiresOf ((L.get i).2.2.1 ++ [⟨.or, []⟩]) (bitsOf t z)).getD ((L.get i).2.2.2.1 j) false then (1 : F) else 0) = _
        rw [wiresOf_append_getD_lt (L.get i).2.2.1 [⟨.or, []⟩] _
          (by rw [bitsOf_len]; exact hBi.2.2.2.1 j)]
        rfl
      have hconv : (fun i : Fin L.length => x - (fun j : Fin k => if (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨(L.get i).2.2.1 ++ [⟨.or, []⟩], t + (L.get i).2.2.1.length⟩ (bits t z)).getD ((L.get i).2.2.2.1 j) false then (1 : F) else 0) ∈ (L.get i).2.1) =
          (fun i : Fin L.length => x - (branchPos (L.get i)) z ∈ (L.get i).2.1) := by
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
      have hrhs : (PEqualNP.CircuitLowerBounds.Circuit.mk ((L.get i).2.2.1 ++ [⟨.or, []⟩]) (t + (L.get i).2.2.1.length)).eval (bits t z) = false := by
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval
        change (wiresOf ((L.get i).2.2.1 ++ [⟨.or, []⟩]) (bitsOf t z)).getD (t + (L.get i).2.2.1.length) false = false
        rw [wiresOf_snoc_last_eq (L.get i).2.2.1 ⟨.or, []⟩
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

end Part844

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

section Main844

open Classical

lemma main_844_fwd :
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
    ∀ C : Circ, legal (2*k+t) C → cost C ≤ s →
      ∃ (N : ℕ) (r : Fin N → ℕ) (A : Fin N → V → Z → ℤ),
        (∀ i, atom (r i) (A i)) ∧ (∑ i, 2^(k-r i) : ℕ) = 2^k ∧
        ∀ y z, prof C y z = ∑ i, (2 : ℤ)^(k-r i) * A i y z := by
  intro k t Circ F legal cost bits V Z sign prof s atom C hC hcostC
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

end Main844

section Part33649

open Classical

def b2f (b : Bool) : F2 := if b then 1 else 0

lemma b2f_xor (a b : Bool) : b2f (Bool.xor a b) = b2f a + b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_and (a b : Bool) : b2f (a && b) = b2f a * b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_or (a b : Bool) : b2f (a || b) = b2f a + b2f b + b2f a * b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_not (a : Bool) : b2f (!a) = 1 + b2f a := by
  cases a <;> decide

lemma b2f_decide (x : F2) : b2f (decide (x = 1)) = x := by
  fin_cases x <;> rfl

lemma decide_b2f (b : Bool) : decide (b2f b = 1) = b := by
  cases b <;> decide

lemma zmod2_eq_of_add_eq_zero {a b : F2} (h : a + b = 0) : a = b := by
  fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (by decide)

lemma readsBack_mk_iff {n : ℕ} (C : Circuit) : ReadsBack n ⟨C.gates, 0⟩ ↔ ReadsBack n C :=
  Iff.rfl

lemma dotProduct_cons_eq {k : ℕ} (a : Fin (k + 1) → F2) (t : F2) (z : Fin k → F2) :
    dotProduct a (Fin.cons t z) = a 0 * t + dotProduct (Fin.tail a) z := by
  simp [dotProduct, Fin.sum_univ_succ, Fin.tail]

lemma sum_f2_real (f : F2 → ℝ) : (∑ x : F2, f x) = f 0 + f 1 :=
  Fin.sum_univ_two f

lemma err_indicator_eq_sign (c d db : Bool) :
    (if c = Bool.xor d db then (0 : ℝ) else 1) =
      (1 - (signB db : ℝ) * (signB (Bool.xor c d) : ℝ)) / 2 := by
  cases c <;> cases d <;> cases db <;> norm_num [signB]

lemma cost_eq_zero_wires {n : ℕ} (gs : List Gate) (hleg : legalGates n gs) (hcost : costGates gs = 0) :
    ∀ w < n + gs.length, ∃ (c : F2) (a : Fin n → F2),
      ∀ y : Fin n → F2,
        b2f ((wiresOf gs (bitsOf n y)).getD w false) = c + dotProduct a y := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w hw
    simp only [List.length_nil, Nat.add_zero] at hw
    refine ⟨0, Pi.single ⟨w, hw⟩ 1, fun y => ?_⟩
    simp only [wiresOf, Circuit.wires, List.foldl_nil, zero_add, single_dotProduct, one_mul]
    rw [bitsOf_getD n y ⟨w, hw⟩, b2f_decide]
  | append_singleton gs g ih =>
    have hpre := legalGates_prefix hleg
    have hnot : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) := by
      intro h1
      have hc := costGates_snoc_one gs g h1
      omega
    have hcost_gs : costGates gs = 0 := by
      have hc := costGates_snoc_zero gs g hnot
      omega
    have hih := ih hpre.1 hcost_gs
    intro w hw
    simp only [List.length_append, List.length_singleton] at hw
    by_cases hlt : w < n + gs.length
    · rcases hih w hlt with ⟨c, a, hca⟩
      refine ⟨c, a, fun y => ?_⟩
      rw [wiresOf_append_getD_lt gs [g] (bitsOf n y) (by rw [bitsOf_len]; exact hlt)]
      exact hca y
    · have hweq : w = n + gs.length := by omega
      subst hweq
      have hEval : ∀ y : Fin n → F2,
          b2f ((wiresOf (gs ++ [g]) (bitsOf n y)).getD (n + gs.length) false) =
            b2f (g.op.eval (g.inputs.map fun i => (wiresOf gs (bitsOf n y)).getD i false)) := by
        intro y
        rw [wiresOf_snoc_last_eq gs g (bitsOf n y) (bitsOf_len n y)]
      rcases hpre.2.2.2 with hop | hop | hop | ⟨hop, hlen1⟩
      · rcases hlist : g.inputs with _ | ⟨i0, _ | ⟨i1, rest⟩⟩
        · refine ⟨1, 0, fun y => ?_⟩
          rw [hEval y, hop, hlist]; simp [GateOp.eval, b2f]
        · have hi0 : i0 < n + gs.length := hpre.2.1 i0 (by simp [hlist])
          rcases hih i0 hi0 with ⟨c0, a0, h0⟩
          refine ⟨c0, a0, fun y => ?_⟩
          rw [hEval y, hop, hlist]
          simpa [GateOp.eval] using h0 y
        · exfalso
          have hlen := hpre.2.2.1
          rw [hlist] at hlen
          have hrest : rest = [] := by cases rest; rfl; simp at hlen
          subst hrest
          exact hnot ⟨Or.inl hop, by simp [hlist]⟩
      · rcases hlist : g.inputs with _ | ⟨i0, _ | ⟨i1, rest⟩⟩
        · refine ⟨0, 0, fun y => ?_⟩
          rw [hEval y, hop, hlist]; simp [GateOp.eval, b2f]
        · have hi0 : i0 < n + gs.length := hpre.2.1 i0 (by simp [hlist])
          rcases hih i0 hi0 with ⟨c0, a0, h0⟩
          refine ⟨c0, a0, fun y => ?_⟩
          rw [hEval y, hop, hlist]
          simpa [GateOp.eval] using h0 y
        · exfalso
          have hlen := hpre.2.2.1
          rw [hlist] at hlen
          have hrest : rest = [] := by cases rest; rfl; simp at hlen
          subst hrest
          exact hnot ⟨Or.inr hop, by simp [hlist]⟩
      · rcases hlist : g.inputs with _ | ⟨i0, _ | ⟨i1, rest⟩⟩
        · refine ⟨1, 0, fun y => ?_⟩
          rw [hEval y, hop, hlist]; simp [GateOp.eval, b2f]
        · have hi0 : i0 < n + gs.length := hpre.2.1 i0 (by simp [hlist])
          rcases hih i0 hi0 with ⟨c0, a0, h0⟩
          refine ⟨1 + c0, a0, fun y => ?_⟩
          rw [hEval y, hop, hlist]
          have hmod1 : ∀ b : Bool, b2f (GateOp.eval (.mod 2) [b]) = 1 + b2f b := by
            intro b; cases b <;> decide
          simp only [List.map_cons, List.map_nil, hmod1, h0 y]
          ring
        · have hlen := hpre.2.2.1
          rw [hlist] at hlen
          have hrest : rest = [] := by cases rest; rfl; simp at hlen
          subst hrest
          have hi0 : i0 < n + gs.length := hpre.2.1 i0 (by simp [hlist])
          have hi1 : i1 < n + gs.length := hpre.2.1 i1 (by simp [hlist])
          rcases hih i0 hi0 with ⟨c0, a0, h0⟩
          rcases hih i1 hi1 with ⟨c1, a1, h1⟩
          refine ⟨1 + c0 + c1, a0 + a1, fun y => ?_⟩
          rw [hEval y, hop, hlist]
          have hmod2 : ∀ b0 b1 : Bool, b2f (GateOp.eval (.mod 2) [b0, b1]) = 1 + b2f b0 + b2f b1 := by
            intro b0 b1; cases b0 <;> cases b1 <;> decide
          simp only [List.map_cons, List.map_nil, hmod2, h0 y, h1 y, add_dotProduct]
          ring
      · rcases hlist : g.inputs with _ | ⟨i0, rest⟩
        · simp [hlist] at hlen1
        · have hrest : rest = [] := by cases rest; rfl; simp [hlist] at hlen1
          subst hrest
          have hi0 : i0 < n + gs.length := hpre.2.1 i0 (by simp [hlist])
          rcases hih i0 hi0 with ⟨c0, a0, h0⟩
          refine ⟨1 + c0, a0, fun y => ?_⟩
          rw [hEval y, hop, hlist]
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2f_not, h0 y]
          ring

lemma cost_le_one_wires {n : ℕ} (gs : List Gate) (hleg : legalGates n gs) (hcost : costGates gs ≤ 1) :
    ∃ (cU cV : F2) (aU aV : Fin n → F2),
      ∀ w < n + gs.length, ∃ (c : F2) (a : Fin n → F2) (δ : F2),
        ∀ y : Fin n → F2,
          b2f ((wiresOf gs (bitsOf n y)).getD w false) =
            c + dotProduct a y + δ * (cU + dotProduct aU y) * (cV + dotProduct aV y) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨0, 0, 0, 0, fun w hw => ?_⟩
    simp only [List.length_nil, Nat.add_zero] at hw
    refine ⟨0, Pi.single ⟨w, hw⟩ 1, 0, fun y => ?_⟩
    simp only [wiresOf, Circuit.wires, List.foldl_nil, zero_add, zero_mul, add_zero,
      single_dotProduct, one_mul]
    rw [bitsOf_getD n y ⟨w, hw⟩, b2f_decide]
  | append_singleton gs g ih =>
    have hpre := legalGates_prefix hleg
    by_cases hnl : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2
    · have hcost_gs : costGates gs = 0 := by
        have hc := costGates_snoc_one gs g hnl
        omega
      have haff := cost_eq_zero_wires gs hpre.1 hcost_gs
      rcases hlist : g.inputs with _ | ⟨i0, _ | ⟨i1, rest⟩⟩
      · simp [hlist] at hnl
      · simp [hlist] at hnl
      · have hrest : rest = [] := by cases rest; rfl; simp [hlist] at hnl
        subst hrest
        have hi0 : i0 < n + gs.length := hpre.2.1 i0 (by simp [hlist])
        have hi1 : i1 < n + gs.length := hpre.2.1 i1 (by simp [hlist])
        rcases haff i0 hi0 with ⟨cU, aU, hU⟩
        rcases haff i1 hi1 with ⟨cV, aV, hV⟩
        refine ⟨cU, cV, aU, aV, fun w hw => ?_⟩
        simp only [List.length_append, List.length_singleton] at hw
        by_cases hlt : w < n + gs.length
        · rcases haff w hlt with ⟨c, a, hca⟩
          refine ⟨c, a, 0, fun y => ?_⟩
          rw [wiresOf_append_getD_lt gs [g] (bitsOf n y) (by rw [bitsOf_len]; exact hlt)]
          simpa using hca y
        · have hweq : w = n + gs.length := by omega
          subst hweq
          rcases hnl.1 with hop | hop
          · refine ⟨0, 0, 1, fun y => ?_⟩
            rw [wiresOf_snoc_last_eq gs g (bitsOf n y) (bitsOf_len n y), hop, hlist]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, b2f_and, hU y, hV y, zero_dotProduct, zero_add, one_mul]
          · refine ⟨cU + cV, aU + aV, 1, fun y => ?_⟩
            rw [wiresOf_snoc_last_eq gs g (bitsOf n y) (bitsOf_len n y), hop, hlist]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, b2f_or, hU y, hV y, add_dotProduct, one_mul]
            ring
    · have hcost_gs : costGates gs ≤ 1 := by
        have hc := costGates_snoc_zero gs g hnl
        omega
      rcases ih hpre.1 hcost_gs with ⟨cU, cV, aU, aV, hih⟩
      refine ⟨cU, cV, aU, aV, fun w hw => ?_⟩
      simp only [List.length_append, List.length_singleton] at hw
      by_cases hlt : w < n + gs.length
      · rcases hih w hlt with ⟨c, a, δ, hca⟩
        refine ⟨c, a, δ, fun y => ?_⟩
        rw [wiresOf_append_getD_lt gs [g] (bitsOf n y) (by rw [bitsOf_len]; exact hlt)]
        exact hca y
      · have hweq : w = n + gs.length := by omega
        subst hweq
        have hEval : ∀ y : Fin n → F2,
            b2f ((wiresOf (gs ++ [g]) (bitsOf n y)).getD (n + gs.length) false) =
              b2f (g.op.eval (g.inputs.map fun i => (wiresOf gs (bitsOf n y)).getD i false)) := by
          intro y
          rw [wiresOf_snoc_last_eq gs g (bitsOf n y) (bitsOf_len n y)]
        rcases hpre.2.2.2 with hop | hop | hop | ⟨hop, hlen1⟩
        · rcases hlist : g.inputs with _ | ⟨i0, _ | ⟨i1, rest⟩⟩
          · refine ⟨1, 0, 0, fun y => ?_⟩
            rw [hEval y, hop, hlist]; simp [GateOp.eval, b2f]
          · have hi0 : i0 < n + gs.length := hpre.2.1 i0 (by simp [hlist])
            rcases hih i0 hi0 with ⟨c0, a0, δ0, h0⟩
            refine ⟨c0, a0, δ0, fun y => ?_⟩
            rw [hEval y, hop, hlist]; simpa [GateOp.eval] using h0 y
          · exfalso
            have hlen := hpre.2.2.1; rw [hlist] at hlen
            have hrest : rest = [] := by cases rest; rfl; simp at hlen
            subst hrest; exact hnl ⟨Or.inl hop, by simp [hlist]⟩
        · rcases hlist : g.inputs with _ | ⟨i0, _ | ⟨i1, rest⟩⟩
          · refine ⟨0, 0, 0, fun y => ?_⟩
            rw [hEval y, hop, hlist]; simp [GateOp.eval, b2f]
          · have hi0 : i0 < n + gs.length := hpre.2.1 i0 (by simp [hlist])
            rcases hih i0 hi0 with ⟨c0, a0, δ0, h0⟩
            refine ⟨c0, a0, δ0, fun y => ?_⟩
            rw [hEval y, hop, hlist]; simpa [GateOp.eval] using h0 y
          · exfalso
            have hlen := hpre.2.2.1; rw [hlist] at hlen
            have hrest : rest = [] := by cases rest; rfl; simp at hlen
            subst hrest; exact hnl ⟨Or.inr hop, by simp [hlist]⟩
        · rcases hlist : g.inputs with _ | ⟨i0, _ | ⟨i1, rest⟩⟩
          · refine ⟨1, 0, 0, fun y => ?_⟩
            rw [hEval y, hop, hlist]; simp [GateOp.eval, b2f]
          · have hi0 : i0 < n + gs.length := hpre.2.1 i0 (by simp [hlist])
            rcases hih i0 hi0 with ⟨c0, a0, δ0, h0⟩
            refine ⟨1 + c0, a0, δ0, fun y => ?_⟩
            rw [hEval y, hop, hlist]
            have hmod1 : ∀ b : Bool, b2f (GateOp.eval (.mod 2) [b]) = 1 + b2f b := by
              intro b; cases b <;> decide
            simp only [List.map_cons, List.map_nil, hmod1, h0 y]
            ring
          · have hlen := hpre.2.2.1; rw [hlist] at hlen
            have hrest : rest = [] := by cases rest; rfl; simp at hlen
            subst hrest
            have hi0 : i0 < n + gs.length := hpre.2.1 i0 (by simp [hlist])
            have hi1 : i1 < n + gs.length := hpre.2.1 i1 (by simp [hlist])
            rcases hih i0 hi0 with ⟨c0, a0, δ0, h0⟩
            rcases hih i1 hi1 with ⟨c1, a1, δ1, h1⟩
            refine ⟨1 + c0 + c1, a0 + a1, δ0 + δ1, fun y => ?_⟩
            rw [hEval y, hop, hlist]
            have hmod2 : ∀ b0 b1 : Bool, b2f (GateOp.eval (.mod 2) [b0, b1]) = 1 + b2f b0 + b2f b1 := by
              intro b0 b1; cases b0 <;> cases b1 <;> decide
            simp only [List.map_cons, List.map_nil, hmod2, h0 y, h1 y, add_dotProduct]
            ring
        · rcases hlist : g.inputs with _ | ⟨i0, rest⟩
          · simp [hlist] at hlen1
          · have hrest : rest = [] := by cases rest; rfl; simp [hlist] at hlen1
            subst hrest
            have hi0 : i0 < n + gs.length := hpre.2.1 i0 (by simp [hlist])
            rcases hih i0 hi0 with ⟨c0, a0, δ0, h0⟩
            refine ⟨1 + c0, a0, δ0, fun y => ?_⟩
            rw [hEval y, hop, hlist]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2f_not, h0 y]
            ring

lemma sum_f2 (f : F2 → F2) : (∑ x : F2, f x) = f 0 + f 1 :=
  Fin.sum_univ_two f

lemma f2_two : (2 : F2) = 0 := rfl
lemma f2_four : (4 : F2) = 0 := rfl
lemma f2_eight : (8 : F2) = 0 := rfl

lemma sum_cube_mul2 (c1 a1 b1 d1 c2 a2 b2 d2 : F2) :
    (∑ t : F2, ∑ r : F2, ∑ s : F2,
      (c1 + a1 * t + b1 * r + d1 * s) * (c2 + a2 * t + b2 * r + d2 * s)) = 0 := by
  simp only [sum_f2]
  ring_nf
  simp only [f2_two, f2_four, f2_eight, mul_zero, add_zero]

lemma sum_cube_mul3 (c1 a1 b1 d1 c2 a2 b2 d2 c3 a3 b3 d3 : F2) :
    (∑ t : F2, ∑ r : F2, ∑ s : F2,
      (c1 + a1 * t + b1 * r + d1 * s) * (c2 + a2 * t + b2 * r + d2 * s) *
        (c3 + a3 * t + b3 * r + d3 * s)) =
      a1 * (b2 * d3 + d2 * b3) + a2 * (b1 * d3 + d1 * b3) + a3 * (b1 * d2 + d1 * b2) := by
  simp only [sum_f2]
  ring_nf
  simp only [f2_two, f2_four, f2_eight, mul_zero, add_zero, zero_add]

lemma sum_cube_lin (c1 a1 b1 d1 : F2) :
    (∑ t : F2, ∑ r : F2, ∑ s : F2, (c1 + a1 * t + b1 * r + d1 * s)) = 0 := by
  have h := sum_cube_mul2 c1 a1 b1 d1 1 0 0 0
  simpa using h

lemma dotProduct_cons_e {k : ℕ} (a : Fin (k + 1) → F2) (u0 v0 : Fin k) (t r s : F2) :
    dotProduct a (Fin.cons t (r • (fun j : Fin k => if j = u0 then (1 : F2) else 0) +
      s • (fun j : Fin k => if j = v0 then (1 : F2) else 0))) =
      a 0 * t + a u0.succ * r + a v0.succ * s := by
  rw [dotProduct_cons_eq, dotProduct_add, dotProduct_smul, dotProduct_smul]
  have h1 : dotProduct (Fin.tail a) (fun j : Fin k => if j = u0 then (1 : F2) else 0) = a u0.succ := by
    simp [dotProduct, Fin.tail]
  have h2 : dotProduct (Fin.tail a) (fun j : Fin k => if j = v0 then (1 : F2) else 0) = a v0.succ := by
    simp [dotProduct, Fin.tail]
  rw [h1, h2]
  simp only [smul_eq_mul]
  ring

lemma exists_pair_for_det3 {k : ℕ} (δ aU aV : Fin (k + 1) → F2) :
    ∃ p : (Fin k → F2) × (Fin k → F2), ∀ (u0 v0 : Fin k),
      p.1 u0 * p.2 v0 + p.1 v0 * p.2 u0 =
        δ 0 * (aU u0.succ * aV v0.succ + aU v0.succ * aV u0.succ) +
        aU 0 * (δ u0.succ * aV v0.succ + δ v0.succ * aV u0.succ) +
        aV 0 * (δ u0.succ * aU v0.succ + δ v0.succ * aU u0.succ) := by
  rcases zmod2_cases (δ 0) with h1 | h1
  · rcases zmod2_cases (aU 0) with h2 | h2
    · rcases zmod2_cases (aV 0) with h3 | h3
      · refine ⟨(0, 0), fun u0 v0 => ?_⟩
        simp [h1, h2, h3]
      · refine ⟨(fun j => δ j.succ, fun j => aU j.succ), fun u0 v0 => ?_⟩
        simp [h1, h2, h3]
    · refine ⟨(fun j => δ j.succ, fun j => aV j.succ + aV 0 * aU j.succ), fun u0 v0 => ?_⟩
      simp only [h1, h2, zero_mul, zero_add, one_mul]
      ring
  · refine ⟨(fun j => aU j.succ + aU 0 * δ j.succ, fun j => aV j.succ + aV 0 * δ j.succ), fun u0 v0 => ?_⟩
    simp only [h1, one_mul]
    have hself : aU 0 * aV 0 * (δ u0.succ * δ v0.succ + δ v0.succ * δ u0.succ) = 0 := by
      have : δ u0.succ * δ v0.succ + δ v0.succ * δ u0.succ = 0 := by
        rw [mul_comm (δ v0.succ)]
        rcases zmod2_cases (δ u0.succ * δ v0.succ) with h | h <;> rw [h] <;> decide
      rw [this, mul_zero]
    linear_combination hself

noncomputable def rhoF2 (q : F2 × F2) : ℝ := if q = (0, 0) then 0 else 1 / 3

lemma rhoF2_nonneg (q : F2 × F2) : 0 ≤ rhoF2 q := by
  unfold rhoF2; split_ifs <;> norm_num

lemma sum_rhoF2 : (∑ q : F2 × F2, rhoF2 q) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [sum_f2_real, rhoF2]
  norm_num

noncomputable def unifNZ {k : ℕ} (p : (Fin k → F2) × (Fin k → F2)) : ℝ :=
  ∏ j : Fin k, rhoF2 (p.1 j, p.2 j)

lemma unifNZ_nonneg {k : ℕ} (p : (Fin k → F2) × (Fin k → F2)) : 0 ≤ unifNZ p :=
  Finset.prod_nonneg (fun _j _ => rhoF2_nonneg _)

def prodFunEquiv (k : ℕ) : (Fin k → F2 × F2) ≃ (Fin k → F2) × (Fin k → F2) :=
  { toFun := fun f => (fun j => (f j).1, fun j => (f j).2)
    invFun := fun p j => (p.1 j, p.2 j)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma sum_unifNZ {k : ℕ} : (∑ p : (Fin k → F2) × (Fin k → F2), unifNZ p) = 1 := by
  rw [← Fintype.sum_equiv (prodFunEquiv k) _ _ (fun _ => rfl)]
  have hprod : (∑ f : Fin k → F2 × F2, unifNZ (prodFunEquiv k f)) =
      ∏ _j : Fin k, ∑ q : F2 × F2, rhoF2 q := by
    simpa [unifNZ, prodFunEquiv] using (Fintype.prod_sum (fun (_j : Fin k) (q : F2 × F2) => rhoF2 q)).symm
  rw [hprod]
  simp [sum_rhoF2]

noncomputable def fairDist {k : ℕ} (p : (Fin k → F2) × (Fin k → F2)) : ℝ :=
  (if p = (0, 0) then (1 / 4 : ℝ) else 0) + (3 / 4 : ℝ) * unifNZ p

lemma fairDist_nonneg {k : ℕ} (p : (Fin k → F2) × (Fin k → F2)) : 0 ≤ fairDist p := by
  unfold fairDist
  have h1 : (0 : ℝ) ≤ if p = (0, 0) then (1 / 4 : ℝ) else 0 := by split_ifs <;> norm_num
  have h2 : (0 : ℝ) ≤ (3 / 4 : ℝ) * unifNZ p := mul_nonneg (by norm_num) (unifNZ_nonneg p)
  linarith

lemma sum_fairDist {k : ℕ} : (∑ p : (Fin k → F2) × (Fin k → F2), fairDist p) = 1 := by
  unfold fairDist
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_unifNZ]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  norm_num

lemma sum_unifNZ_bad {k : ℕ} (u0 v0 : Fin k) (huv : u0 ≠ v0) (lab : F2) :
    (∑ p : (Fin k → F2) × (Fin k → F2),
      unifNZ p * (if p.1 u0 * p.2 v0 + p.1 v0 * p.2 u0 = lab then (0 : ℝ) else 1)) =
      if lab = 0 then (2 / 3 : ℝ) else 1 / 3 := by
  rw [← Fintype.sum_equiv (prodFunEquiv k) _ _ (fun _ => rfl)]
  let Rest := {j : Fin k // j ≠ u0 ∧ j ≠ v0}
  let eSplit : (Fin k → F2 × F2) ≃ ((F2 × F2) × (F2 × F2)) × (Rest → F2 × F2) :=
    { toFun := fun f => ((f u0, f v0), fun j => f j.val)
      invFun := fun ⟨⟨q1, q2⟩, g⟩ j =>
        if hj1 : j = u0 then q1 else if hj2 : j = v0 then q2 else g ⟨j, hj1, hj2⟩
      left_inv := fun f => by
        funext j
        by_cases hj1 : j = u0
        · subst hj1; simp
        · by_cases hj2 : j = v0
          · subst hj2; simp [hj1]
          · simp [hj1, hj2]
      right_inv := by
        rintro ⟨⟨q1, q2⟩, g⟩
        refine Prod.ext (Prod.ext (by simp) (by simp [huv.symm])) ?_
        funext ⟨j, hj1, hj2⟩
        simp [hj1, hj2] }
  have hprod_split : ∀ f : Fin k → F2 × F2,
      (∏ j : Fin k, rhoF2 (f j)) =
        rhoF2 (f u0) * rhoF2 (f v0) * ∏ j : Rest, rhoF2 (f j.val) := by
    intro f
    have h1 : (∏ j : Fin k, rhoF2 (f j)) =
        rhoF2 (f u0) * ∏ j ∈ Finset.univ.erase u0, rhoF2 (f j) :=
      (Finset.mul_prod_erase Finset.univ (fun j => rhoF2 (f j)) (Finset.mem_univ u0)).symm
    have hv_mem : v0 ∈ Finset.univ.erase u0 := Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v0⟩
    have h2 : (∏ j ∈ Finset.univ.erase u0, rhoF2 (f j)) =
        rhoF2 (f v0) * ∏ j ∈ (Finset.univ.erase u0).erase v0, rhoF2 (f j) :=
      (Finset.mul_prod_erase (Finset.univ.erase u0) (fun j => rhoF2 (f j)) hv_mem).symm
    rw [h1, h2, ← mul_assoc]
    congr 1
    refine Finset.prod_bij (fun j hj => ⟨j, (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1,
        (Finset.mem_erase.mp hj).1⟩) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · intro a1 _ a2 _ h; exact congrArg Subtype.val h
    · intro ⟨j, hj1, hj2⟩ _
      exact ⟨j, Finset.mem_erase.mpr ⟨hj2, Finset.mem_erase.mpr ⟨hj1, Finset.mem_univ j⟩⟩, rfl⟩
  have hsum_eq :
      (∑ f : Fin k → F2 × F2,
        unifNZ (prodFunEquiv k f) *
          (if (prodFunEquiv k f).1 u0 * (prodFunEquiv k f).2 v0 +
              (prodFunEquiv k f).1 v0 * (prodFunEquiv k f).2 u0 = lab then (0 : ℝ) else 1)) =
      ∑ x : ((F2 × F2) × (F2 × F2)) × (Rest → F2 × F2),
        (rhoF2 x.1.1 * rhoF2 x.1.2 *
          (if x.1.1.1 * x.1.2.2 + x.1.2.1 * x.1.1.2 = lab then (0 : ℝ) else 1)) *
        (∏ j : Rest, rhoF2 (x.2 j)) := by
    refine Fintype.sum_equiv eSplit _ _ (fun f => ?_)
    dsimp only [eSplit, Equiv.coe_fn_mk, unifNZ, prodFunEquiv]
    rw [hprod_split f, mul_assoc, mul_assoc, mul_comm (∏ j : Rest, rhoF2 (f j.val)),
      ← mul_assoc, ← mul_assoc]
    rfl
  rw [hsum_eq, Fintype.sum_prod_type]
  have hfactor : ∀ a : (F2 × F2) × (F2 × F2),
      (∑ b : Rest → F2 × F2,
        (rhoF2 a.1 * rhoF2 a.2 *
          (if a.1.1 * a.2.2 + a.2.1 * a.1.2 = lab then (0 : ℝ) else 1)) *
        (∏ j : Rest, rhoF2 (b j))) =
      (rhoF2 a.1 * rhoF2 a.2 *
        (if a.1.1 * a.2.2 + a.2.1 * a.1.2 = lab then (0 : ℝ) else 1)) *
      (∑ b : Rest → F2 × F2, ∏ j : Rest, rhoF2 (b j)) := fun a => (Finset.mul_sum _ _ _).symm
  simp_rw [hfactor]
  rw [← Finset.sum_mul]
  have hrest : (∑ g : Rest → F2 × F2, ∏ j : Rest, rhoF2 (g j)) = 1 := by
    have hps : (∑ g : Rest → F2 × F2, ∏ j : Rest, rhoF2 (g j)) =
        ∏ _j : Rest, ∑ q : F2 × F2, rhoF2 q :=
      (Fintype.prod_sum (fun (_j : Rest) (q : F2 × F2) => rhoF2 q)).symm
    rw [hps]
    simp [sum_rhoF2]
  rw [hrest, mul_one, Fintype.sum_prod_type]
  have h11 : (1 : F2) + 1 = 0 := rfl
  rcases zmod2_cases lab with rfl | rfl
  · simp only [Fintype.sum_prod_type, sum_f2_real, rhoF2, mul_zero, zero_mul, mul_one, one_mul,
      zero_add, add_zero, h11]
    norm_num
  · simp only [Fintype.sum_prod_type, sum_f2_real, rhoF2, mul_zero, zero_mul, mul_one, one_mul,
      zero_add, add_zero, h11]
    norm_num

lemma sum_fairDist_bad {k : ℕ} (u0 v0 : Fin k) (huv : u0 ≠ v0) (lab : F2) :
    (∑ p : (Fin k → F2) × (Fin k → F2),
      fairDist p * (if p.1 u0 * p.2 v0 + p.1 v0 * p.2 u0 = lab then (0 : ℝ) else 1)) = 1 / 2 := by
  unfold fairDist
  simp_rw [add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_unifNZ_bad u0 v0 huv lab]
  have h0 : (∑ p : (Fin k → F2) × (Fin k → F2),
      (if p = (0, 0) then (1 / 4 : ℝ) else 0) *
        (if p.1 u0 * p.2 v0 + p.1 v0 * p.2 u0 = lab then (0 : ℝ) else 1)) =
      if (0 : F2) = lab then 0 else 1 / 4 := by
    have hpt : ∀ p : (Fin k → F2) × (Fin k → F2),
        (if p = (0, 0) then (1 / 4 : ℝ) else 0) *
          (if p.1 u0 * p.2 v0 + p.1 v0 * p.2 u0 = lab then (0 : ℝ) else 1) =
        if p = (0, 0) then (if (0 : F2) = lab then 0 else 1 / 4) else 0 := by
      intro p
      by_cases hp : p = (0, 0)
      · subst hp; simp
      · simp [hp]
    simp_rw [hpt]
    simp
  rw [h0]
  rcases zmod2_cases lab with rfl | rfl <;> norm_num

noncomputable def errAtom {k : ℕ} (f : (Fin (k + 1) → F2) → ℤ) (y : Fin (k + 1) → F2) (b : F2) : ℝ :=
  (1 - (signB (decide (b = 1)) : ℝ) * (f y : ℝ)) / 2

lemma errAtom_nonneg_of_abs_le_one {k : ℕ} {f : (Fin (k + 1) → F2) → ℤ} {y : Fin (k + 1) → F2}
    (hf : f y = 0 ∨ f y = 1 ∨ f y = -1) (b : F2) : 0 ≤ errAtom f y b := by
  unfold errAtom
  have hs : signB (decide (b = 1)) = 1 ∨ signB (decide (b = 1)) = -1 := by
    cases decide (b = 1) <;> simp [signB]
  rcases hs with hs | hs <;> rcases hf with hf | hf | hf <;> rw [hs, hf] <;> norm_num

lemma errAtom_zero {k : ℕ} {f : (Fin (k + 1) → F2) → ℤ} {y : Fin (k + 1) → F2}
    (hf : f y = 0) (b : F2) : errAtom f y b = 1 / 2 := by
  unfold errAtom; rw [hf]; norm_num

lemma errAtom_sign {k : ℕ} {f : (Fin (k + 1) → F2) → ℤ} {y : Fin (k + 1) → F2}
    {c : Bool} (hf : f y = signB c) (b : F2) :
    errAtom f y b = if c = decide (b = 1) then 0 else 1 := by
  unfold errAtom
  rw [hf]
  cases c <;> cases decide (b = 1) <;> norm_num [signB]

lemma build_tail_ip (k : ℕ) :
    ∀ (m : ℕ) (_hm : m ≤ k) (gs : List Gate) (wAcc0 : ℕ),
      legalGates (2 * (k + 1)) gs →
      wAcc0 < 2 * (k + 1) + gs.length →
      ∃ (ext : List Gate) (wAcc : ℕ),
        let gs' := gs ++ ext
        legalGates (2 * (k + 1)) gs' ∧
        costGates gs' = costGates gs + m ∧
        wAcc < 2 * (k + 1) + gs'.length ∧
        ∀ (x y : Fin (k + 1) → F2),
          let inp := bitsOf (k + 1) x ++ bitsOf (k + 1) y
          (wiresOf gs' inp).getD wAcc false =
            Bool.xor ((wiresOf gs inp).getD wAcc0 false)
              (decide ((∑ l : Fin k, if l.val < m then x l.succ * y l.succ else 0) = 1)) := by
  intro m
  induction m with
  | zero =>
    intro _ gs wAcc0 hleg hw0
    refine ⟨[], wAcc0, by simpa using hleg, by simp, by simpa using hw0, fun x y => ?_⟩
    simp only [List.append_nil, Nat.not_lt_zero, ↓reduceIte, Finset.sum_const_zero]
    have h0 : decide ((0 : F2) = 1) = false := rfl
    rw [h0, Bool.xor_false]
  | succ m ih =>
    intro hm gs wAcc0 hleg hw0
    rcases ih (by omega) gs wAcc0 hleg hw0 with ⟨ext1, wAcc1, h1leg, h1cost, h1lt, h1sem⟩
    set gs1 := gs ++ ext1
    let idxX : ℕ := m + 1
    let idxY : ℕ := (k + 1) + (m + 1)
    let gsAnd := gs1 ++ [⟨.and, [idxX, idxY]⟩]
    let wAnd := 2 * (k + 1) + gs1.length
    have hAndLeg : legalGates (2 * (k + 1)) gsAnd :=
      legalGates_snoc h1leg (fun i hi => by simp at hi; rcases hi with rfl | rfl <;> omega)
        ⟨by simp, Or.inl rfl⟩
    have hAndCost : costGates gsAnd = costGates gs1 + 1 :=
      costGates_snoc_one gs1 ⟨.and, [idxX, idxY]⟩ ⟨Or.inl rfl, rfl⟩
    have hstep := addXor_step (2 * (k + 1)) gsAnd wAcc1 wAnd hAndLeg
      (by simp only [gsAnd, List.length_append, List.length_singleton]; omega)
      (by simp [gsAnd, wAnd])
    let extTot := ext1 ++ [⟨.and, [idxX, idxY]⟩] ++
      [⟨.mod 2, [wAcc1, wAnd]⟩, ⟨.not, [2 * (k + 1) + gsAnd.length]⟩]
    have hgs_eq : gs ++ extTot =
        gsAnd ++ [⟨.mod 2, [wAcc1, wAnd]⟩, ⟨.not, [2 * (k + 1) + gsAnd.length]⟩] := by
      simp [extTot, gsAnd, gs1, List.append_assoc]
    refine ⟨extTot, 2 * (k + 1) + gsAnd.length + 1, ?_, ?_, ?_, ?_⟩
    · rw [hgs_eq]; exact hstep.1
    · rw [hgs_eq, hstep.2.1, hAndCost, h1cost]; omega
    · rw [hgs_eq, hstep.2.2.1]; omega
    · intro x y inp
      have hinp_len : inp.length = 2 * (k + 1) := by simp [inp, bitsOf_len]; omega
      rw [hgs_eq, hstep.2.2.2 inp hinp_len]
      have hacc1 : (wiresOf gsAnd inp).getD wAcc1 false =
          Bool.xor ((wiresOf gs inp).getD wAcc0 false)
            (decide ((∑ l : Fin k, if l.val < m then x l.succ * y l.succ else 0) = 1)) := by
        rw [wiresOf_append_getD_lt gs1 [⟨.and, [idxX, idxY]⟩] inp (by rw [hinp_len]; exact h1lt)]
        exact h1sem x y
      have hAnd_val : (wiresOf gsAnd inp).getD wAnd false =
          decide (x (⟨m, hm⟩ : Fin k).succ * y (⟨m, hm⟩ : Fin k).succ = 1) := by
        rw [wiresOf_snoc_last_eq gs1 ⟨.and, [idxX, idxY]⟩ inp hinp_len]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
          id_eq, Bool.and_true]
        have hx : (wiresOf gs1 inp).getD idxX false = decide (x (⟨m, hm⟩ : Fin k).succ = 1) := by
          rw [wiresOf_getD_lt gs1 inp (by rw [hinp_len]; simp [idxX]; omega)]
          simp only [inp, idxX]
          rw [List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by rw [bitsOf_len]; omega)]
          exact bitsOf_getD (k + 1) x (⟨m, hm⟩ : Fin k).succ
        have hy : (wiresOf gs1 inp).getD idxY false = decide (y (⟨m, hm⟩ : Fin k).succ = 1) := by
          rw [wiresOf_getD_lt gs1 inp (by rw [hinp_len]; simp [idxY]; omega)]
          simp only [inp, idxY]
          rw [List.getD_eq_getElem?_getD,
              List.getElem?_append_right (by rw [bitsOf_len]; omega),
              bitsOf_len, Nat.add_sub_cancel_left]
          exact bitsOf_getD (k + 1) y (⟨m, hm⟩ : Fin k).succ
        rw [hx, hy, zmod2_mul_decide]
      rw [hacc1, hAnd_val, Bool.xor_assoc, ← zmod2_add_decide]
      congr 3
      have hpt : ∀ l : Fin k,
          (if l.val < m + 1 then x l.succ * y l.succ else 0) =
          (if l.val < m then x l.succ * y l.succ else 0) +
          (if l = ⟨m, hm⟩ then x l.succ * y l.succ else 0) := by
        intro l
        by_cases hl : l = ⟨m, hm⟩
        · subst hl; simp
        · have hne : l.val ≠ m := fun h => hl (Fin.ext h)
          by_cases hlt : l.val < m
          · have hlt1 : l.val < m + 1 := by omega
            simp [hl, hlt, hlt1]
          · have hlt1 : ¬ l.val < m + 1 := by omega
            simp [hl, hlt, hlt1]
      simp_rw [hpt, Finset.sum_add_distrib]
      simp

lemma exists_upper_circuit {k : ℕ} (p : (Fin k → F2) × (Fin k → F2)) :
    ∃ C : Circuit,
      legalGates (2 * (k + 1)) C.gates ∧
      costGates C.gates ≤ (k + 1) + 1 ∧
      ∀ (x y : Fin (k + 1) → F2),
        C.eval (bitsOf (k + 1) x ++ bitsOf (k + 1) y) =
          decide (dotProduct x y +
            y 0 * (dotProduct p.1 (Fin.tail y) * dotProduct p.2 (Fin.tail y) +
              ∑ l : Fin k, (p.1 l * p.2 l) * y l.succ) = 1) := by
  let n := k + 1
  let gs0 : List Gate := [⟨.or, []⟩]
  let wZero : ℕ := 2 * n
  have hleg_nil : legalGates (2 * n) [] :=
    ⟨fun _ hj => by simp at hj, fun _ h => by simp at h⟩
  have hleg0 : legalGates (2 * n) gs0 :=
    legalGates_snoc hleg_nil (by simp) ⟨by simp, Or.inr (Or.inl rfl)⟩
  have hcost0 : costGates gs0 = 0 := by simp [costGates, gs0]
  have hwz0 : wZero < 2 * n + gs0.length := by simp [gs0, wZero]
  let yWire : Fin k → ℕ := fun l => n + l.succ.val
  have hyWire_lt : ∀ l : Fin k, yWire l < 2 * n + gs0.length := by
    intro l; simp [yWire, gs0, n]; omega
  rcases addDot_full (2 * n) wZero p.1 yWire gs0 hleg0 hwz0 hyWire_lt with
    ⟨extA, hAeq, hlegA, hcostA, wAlt, hAsem⟩
  set gsA := gs0 ++ extA
  set wA := (addDotAux (2 * n) wZero p.1 yWire k (le_refl k) gs0).2
  rw [hAeq] at hlegA hcostA wAlt
  rcases addDot_full (2 * n) wZero p.2 yWire gsA hlegA
    (by simp only [gsA, List.length_append]; omega)
    (fun l => by simp only [gsA, List.length_append]; have := hyWire_lt l; omega) with
    ⟨extB, hBeq, hlegB, hcostB, wBlt, hBsem⟩
  set gsB := gsA ++ extB
  set wB := (addDotAux (2 * n) wZero p.2 yWire k (le_refl k) gsA).2
  rw [hBeq] at hlegB hcostB wBlt
  let gsAB := gsB ++ [⟨.and, [wA, wB]⟩]
  let wAB := 2 * n + gsB.length
  have hlegAB : legalGates (2 * n) gsAB :=
    legalGates_snoc hlegB (fun i hi => by
      simp at hi; rcases hi with rfl | rfl
      · simp only [gsB, List.length_append]; omega
      · exact wBlt) ⟨by simp, Or.inl rfl⟩
  have hcostAB : costGates gsAB = 1 := by
    rw [costGates_snoc_one gsB _ ⟨Or.inl rfl, rfl⟩, hcostB, hcostA, hcost0]
  rcases addDot_full (2 * n) wZero (fun l => p.1 l * p.2 l) yWire gsAB hlegAB
    (by simp only [gsAB, gsB, gsA, List.length_append, List.length_singleton]; omega)
    (fun l => by
      simp only [gsAB, gsB, gsA, List.length_append, List.length_singleton]
      have := hyWire_lt l; omega) with
    ⟨extD, hDeq, hlegD, hcostD, wDlt, hDsem⟩
  set gsD := gsAB ++ extD
  set wD := (addDotAux (2 * n) wZero (fun l => p.1 l * p.2 l) yWire k (le_refl k) gsAB).2
  rw [hDeq] at hlegD hcostD wDlt
  have hstep1 := addXor_step (2 * n) gsD 0 wD hlegD (by omega) wDlt
  set gsX1 := gsD ++ [⟨.mod 2, [0, wD]⟩, ⟨.not, [2 * n + gsD.length]⟩]
  let wX1 := 2 * n + gsD.length + 1
  have hstep2 := addXor_step (2 * n) gsX1 wX1 wAB hstep1.1
    (by rw [hstep1.2.2.1]; omega)
    (by rw [hstep1.2.2.1]; simp only [gsD, gsAB, List.length_append, List.length_singleton]; omega)
  set gsX2 := gsX1 ++ [⟨.mod 2, [wX1, wAB]⟩, ⟨.not, [2 * n + gsX1.length]⟩]
  let wX2 := 2 * n + gsX1.length + 1
  let gsT0 := gsX2 ++ [⟨.and, [n, wX2]⟩]
  let wT0 := 2 * n + gsX2.length
  have hlegT0 : legalGates (2 * n) gsT0 :=
    legalGates_snoc hstep2.1 (fun i hi => by
      simp at hi; rcases hi with rfl | rfl
      · omega
      · rw [hstep2.2.2.1]; omega) ⟨by simp, Or.inl rfl⟩
  have hcostT0 : costGates gsT0 = 2 := by
    rw [costGates_snoc_one gsX2 _ ⟨Or.inl rfl, rfl⟩, hstep2.2.1, hstep1.2.1, hcostD, hcostAB]
  rcases build_tail_ip k k (le_refl k) gsT0 wT0 hlegT0 (by simp [gsT0, wT0, n]) with
    ⟨extIP, wOut, hlegOut, hcostOut, _, hIPsem⟩
  refine ⟨⟨gsT0 ++ extIP, wOut⟩, hlegOut, ?_, ?_⟩
  · change costGates (gsT0 ++ extIP) ≤ n + 1
    rw [hcostOut, hcostT0]; omega
  · intro x y
    set inp := bitsOf n x ++ bitsOf n y
    have hinp_len : inp.length = 2 * n := by simp [inp, bitsOf_len]; omega
    have hz0 : (wiresOf gs0 inp).getD wZero false = false := by
      have h := wiresOf_snoc_last_eq [] ⟨.or, []⟩ inp hinp_len
      simpa [gs0, wZero, GateOp.eval] using h
    have hy_val : ∀ (gs : List Gate) (l : Fin k),
        (wiresOf gs inp).getD (yWire l) false = decide (y l.succ = 1) := by
      intro gs l
      rw [wiresOf_getD_lt gs inp (by rw [hinp_len]; simp [yWire, n]; omega)]
      simp only [inp, yWire]
      rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [bitsOf_len]; omega),
          bitsOf_len, Nat.add_sub_cancel_left]
      exact bitsOf_getD n y l.succ
    have hA_val : (wiresOf gsA inp).getD wA false = decide (dotProduct p.1 (Fin.tail y) = 1) := by
      have hs := hAsem inp hinp_len hz0
      rw [hAeq] at hs; rw [hs]
      congr 2; congr 1; funext l
      rw [hy_val gs0 l, zmod2_decide_bool]; rfl
    have hzA : (wiresOf gsA inp).getD wZero false = false := by
      rw [wiresOf_append_getD_lt gs0 extA inp (by rw [hinp_len]; exact hwz0)]; exact hz0
    have hB_val : (wiresOf gsB inp).getD wB false = decide (dotProduct p.2 (Fin.tail y) = 1) := by
      have hs := hBsem inp hinp_len hzA
      rw [hBeq] at hs; rw [hs]
      congr 2; congr 1; funext l
      rw [hy_val gsA l, zmod2_decide_bool]; rfl
    have hAB_val : (wiresOf gsAB inp).getD wAB false =
        decide (dotProduct p.1 (Fin.tail y) * dotProduct p.2 (Fin.tail y) = 1) := by
      rw [wiresOf_snoc_last_eq gsB ⟨.and, [wA, wB]⟩ inp hinp_len]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        id_eq, Bool.and_true]
      rw [wiresOf_append_getD_lt gsA extB inp (by rw [hinp_len]; exact wAlt),
          hA_val, hB_val, zmod2_mul_decide]
    have hzAB : (wiresOf gsAB inp).getD wZero false = false := by
      have heq : gsAB = gs0 ++ (extA ++ extB ++ [⟨.and, [wA, wB]⟩]) := by
        simp [gsAB, gsB, gsA, List.append_assoc]
      rw [heq, wiresOf_append_getD_lt gs0 _ inp (by rw [hinp_len]; exact hwz0)]; exact hz0
    have hD_val : (wiresOf gsD inp).getD wD false =
        decide ((∑ l : Fin k, (p.1 l * p.2 l) * y l.succ) = 1) := by
      have hs := hDsem inp hinp_len hzAB
      rw [hDeq] at hs; rw [hs]
      congr 2; unfold dotProduct
      apply Finset.sum_congr rfl; intro l _
      dsimp only
      rw [hy_val gsAB l, zmod2_decide_bool]
    have hx0_val : (wiresOf gsD inp).getD 0 false = decide (x 0 = 1) := by
      rw [wiresOf_getD_lt gsD inp (by rw [hinp_len]; omega)]
      simp only [inp]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [bitsOf_len]; omega)]
      exact bitsOf_getD n x 0
    have hX1_val : (wiresOf gsX1 inp).getD wX1 false =
        decide (x 0 + ∑ l : Fin k, (p.1 l * p.2 l) * y l.succ = 1) := by
      rw [hstep1.2.2.2 inp hinp_len, hx0_val, hD_val, ← zmod2_add_decide]
    have hAB_X1 : (wiresOf gsX1 inp).getD wAB false =
        decide (dotProduct p.1 (Fin.tail y) * dotProduct p.2 (Fin.tail y) = 1) := by
      have heq : gsX1 = gsAB ++ (extD ++ [⟨.mod 2, [0, wD]⟩, ⟨.not, [2 * n + gsD.length]⟩]) := by
        simp [gsX1, gsD, List.append_assoc]
      rw [heq, wiresOf_append_getD_lt gsAB _ inp (by rw [hinp_len]; simp [gsAB, wAB])]
      exact hAB_val
    have hX2_val : (wiresOf gsX2 inp).getD wX2 false =
        decide (x 0 + (dotProduct p.1 (Fin.tail y) * dotProduct p.2 (Fin.tail y) +
          ∑ l : Fin k, (p.1 l * p.2 l) * y l.succ) = 1) := by
      rw [hstep2.2.2.2 inp hinp_len, hX1_val, hAB_X1, ← zmod2_add_decide]
      congr 2; ring
    have hy0_val : (wiresOf gsX2 inp).getD n false = decide (y 0 = 1) := by
      rw [wiresOf_getD_lt gsX2 inp (by rw [hinp_len]; omega)]
      simp only [inp]
      rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [bitsOf_len]),
          bitsOf_len, Nat.sub_self]
      exact bitsOf_getD n y 0
    have hT0_val : (wiresOf gsT0 inp).getD wT0 false =
        decide (y 0 * (x 0 + (dotProduct p.1 (Fin.tail y) * dotProduct p.2 (Fin.tail y) +
          ∑ l : Fin k, (p.1 l * p.2 l) * y l.succ)) = 1) := by
      rw [wiresOf_snoc_last_eq gsX2 ⟨.and, [n, wX2]⟩ inp hinp_len]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        id_eq, Bool.and_true, hy0_val, hX2_val, zmod2_mul_decide]
    change (wiresOf (gsT0 ++ extIP) inp).getD wOut false = _
    rw [hIPsem x y, hT0_val, ← zmod2_add_decide]
    congr 2
    have hsum_k : (∑ l : Fin k, if l.val < k then x l.succ * y l.succ else 0) =
        ∑ l : Fin k, x l.succ * y l.succ := by
      apply Finset.sum_congr rfl; intro l _; simp [l.isLt]
    rw [hsum_k]
    simp only [dotProduct, Fin.sum_univ_succ, Fin.tail]
    ring

lemma proper_flat_atom_bound {k N m : ℕ}
    (Z : Fin N → Fin k → F2) (hNpos : 0 < N)
    (hZ : ∀ (a : Fin k → F2) (b : F2), a ≠ 0 →
      N ≤ 4 * ((Finset.univ : Finset (Fin N)).filter (fun j => dotProduct a (Z j) ≠ b)).card)
    (u v : Fin m → Fin k) (label : Fin m → F2) (huv : ∀ i, u i ≠ v i)
    (f : (Fin (k + 1) → F2) → ℤ)
    (W : Submodule F2 (Fin (k + 1) → F2)) (a : Fin (k + 1) → F2)
    (hfinW_lt : Module.finrank F2 W < k + 1)
    (hf_vals : ∀ y, f y = 0 ∨ f y = 1 ∨ f y = -1)
    (hf_out : ∀ y, y - a ∉ W → f y = 0) :
    ∃ w : ((Fin k → F2) × (Fin k → F2)) → ℝ,
      (∀ p, 0 ≤ w p) ∧ (∑ p, w p) = 1 ∧
      ∀ i : Fin m,
        (∑ p, w p * (if p.1 (u i) * p.2 (v i) + p.1 (v i) * p.2 (u i) = label i then (0 : ℝ) else 1)) ≤
        4 * (∑ j : Fin N, errAtom f (Fin.cons 0 (Z j)) 0) / N +
        ∑ t : F2, ∑ r : F2, ∑ s : F2,
          errAtom f (Fin.cons t (r • (fun j : Fin k => if j = u i then (1 : F2) else 0) +
            s • (fun j : Fin k => if j = v i then (1 : F2) else 0))) (t * r * s * label i) := by
  have herr_nonneg : ∀ y b, 0 ≤ errAtom f y b := fun y b => errAtom_nonneg_of_abs_le_one (hf_vals y) b
  have horth_pos : 0 < Module.finrank F2 (orthComp W) := by
    have := finrank_orthComp W
    omega
  have horth_ne : orthComp W ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at horth_pos
    omega
  rcases Submodule.exists_mem_ne_zero_of_ne_bot horth_ne with ⟨c, hcW, hcne⟩
  let d : F2 := dotProduct c a
  have hmiss_b : ∀ (y : Fin (k + 1) → F2) (b : F2), dotProduct c y ≠ d → errAtom f y b = 1 / 2 := by
    intro y b hne
    have hy : y - a ∉ W := by
      intro hmem
      have h0 : dotProduct c (y - a) = 0 := (mem_orthComp W c).mp hcW (y - a) hmem
      rw [zmod2_vec_sub_eq_add, dotProduct_add] at h0
      exact hne (zmod2_eq_of_add_eq_zero h0)
    exact errAtom_zero (hf_out y hy) b
  refine ⟨fairDist, fairDist_nonneg, sum_fairDist, fun i => ?_⟩
  rw [sum_fairDist_bad (u i) (v i) (huv i) (label i)]
  have hcube_nn : 0 ≤ ∑ t : F2, ∑ r : F2, ∑ s : F2,
      errAtom f (Fin.cons t (r • (fun j : Fin k => if j = u i then (1 : F2) else 0) +
        s • (fun j : Fin k => if j = v i then (1 : F2) else 0))) (t * r * s * label i) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => herr_nonneg _ _)))
  have hZ_nn : 0 ≤ 4 * (∑ j : Fin N, errAtom f (Fin.cons 0 (Z j)) 0) / N :=
    div_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => herr_nonneg _ _)))
      (Nat.cast_nonneg N)
  by_cases htail : Fin.tail c ≠ 0
  · have hcard := hZ (Fin.tail c) d htail
    let Sbad := (Finset.univ : Finset (Fin N)).filter (fun j => dotProduct (Fin.tail c) (Z j) ≠ d)
    have hsum_ge : (Sbad.card : ℝ) * (1 / 2 : ℝ) ≤
        ∑ j : Fin N, errAtom f (Fin.cons 0 (Z j)) 0 := by
      calc (Sbad.card : ℝ) * (1 / 2 : ℝ)
          = ∑ _j ∈ Sbad, (1 / 2 : ℝ) := by simp
        _ = ∑ j ∈ Sbad, errAtom f (Fin.cons 0 (Z j)) 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            have hne : dotProduct (Fin.tail c) (Z j) ≠ d := (Finset.mem_filter.mp hj).2
            have hdot : dotProduct c (Fin.cons 0 (Z j)) ≠ d := by
              rw [dotProduct_cons_eq]; simpa using hne
            exact (hmiss_b (Fin.cons 0 (Z j)) 0 hdot).symm
        _ ≤ ∑ j : Fin N, errAtom f (Fin.cons 0 (Z j)) 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => herr_nonneg _ _)
    have hNreal : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
    have hcard_r : (N : ℝ) ≤ 4 * (Sbad.card : ℝ) := by exact_mod_cast hcard
    have hpart1 : (1 / 2 : ℝ) ≤ 4 * (∑ j : Fin N, errAtom f (Fin.cons 0 (Z j)) 0) / N := by
      rw [le_div_iff₀ hNreal]; linarith
    linarith
  · push Not at htail
    have hc0 : c 0 = 1 := by
      rcases zmod2_cases (c 0) with h0 | h1
      · exfalso; apply hcne; funext j
        refine Fin.cases h0 (fun j' => ?_) j
        exact congrFun htail j'
      · exact h1
    have hdot_c : ∀ (t : F2) (z : Fin k → F2), dotProduct c (Fin.cons t z) = t := by
      intro t z
      rw [dotProduct_cons_eq, hc0, htail]; simp
    rcases zmod2_cases d with hd0 | hd1
    · have ht1 : (2 : ℝ) ≤ ∑ t : F2, ∑ r : F2, ∑ s : F2,
          errAtom f (Fin.cons t (r • (fun j : Fin k => if j = u i then (1 : F2) else 0) +
            s • (fun j : Fin k => if j = v i then (1 : F2) else 0))) (t * r * s * label i) := by
        have hval1 : ∀ r s : F2,
            errAtom f (Fin.cons 1 (r • (fun j : Fin k => if j = u i then (1 : F2) else 0) +
              s • (fun j : Fin k => if j = v i then (1 : F2) else 0))) (1 * r * s * label i) = 1 / 2 := by
          intro r s; apply hmiss_b; rw [hdot_c, hd0]; decide
        rw [sum_f2_real]
        have h0nn : 0 ≤ ∑ r : F2, ∑ s : F2,
            errAtom f (Fin.cons 0 (r • (fun j : Fin k => if j = u i then (1 : F2) else 0) +
              s • (fun j : Fin k => if j = v i then (1 : F2) else 0))) (0 * r * s * label i) :=
          Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => herr_nonneg _ _))
        have h1eq : (∑ r : F2, ∑ s : F2,
            errAtom f (Fin.cons 1 (r • (fun j : Fin k => if j = u i then (1 : F2) else 0) +
              s • (fun j : Fin k => if j = v i then (1 : F2) else 0))) (1 * r * s * label i)) = 2 := by
          simp_rw [hval1, sum_f2_real]; norm_num
        linarith
      linarith
    · have hval0 : ∀ j : Fin N, errAtom f (Fin.cons 0 (Z j)) 0 = 1 / 2 := by
        intro j; apply hmiss_b; rw [hdot_c, hd1]; decide
      have hNreal : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
      have hpart1 : 4 * (∑ j : Fin N, errAtom f (Fin.cons 0 (Z j)) 0) / N = 2 := by
        simp_rw [hval0]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [ne_of_gt hNreal]; ring
      linarith

lemma cube_sum_deg3 {k : ℕ} (u0 v0 : Fin k)
    (cOut cU cV δOut : F2) (aOut aU aV δT : Fin (k + 1) → F2)
    (cT : Fin (k + 1) → F2) (aT : Fin (k + 1) → Fin (k + 1) → F2) :
    let eU : Fin k → F2 := fun j => if j = u0 then 1 else 0
    let eV : Fin k → F2 := fun j => if j = v0 then 1 else 0
    let cube : F2 → F2 → F2 → (Fin (k + 1) → F2) := fun t r s => Fin.cons t (r • eU + s • eV)
    (∑ t : F2, ∑ r : F2, ∑ s : F2,
      ((cOut + dotProduct aOut (cube t r s)) +
        (∑ j : Fin (k + 1), (cT j + dotProduct (aT j) (cube t r s)) * cube t r s j) +
        (δOut + dotProduct δT (cube t r s)) * (cU + dotProduct aU (cube t r s)) *
          (cV + dotProduct aV (cube t r s)))) =
      δT 0 * (aU u0.succ * aV v0.succ + aU v0.succ * aV u0.succ) +
      aU 0 * (δT u0.succ * aV v0.succ + δT v0.succ * aV u0.succ) +
      aV 0 * (δT u0.succ * aU v0.succ + δT v0.succ * aU u0.succ) := by
  intro eU eV cube
  have hsplit3 : ∀ (f1 f2 f3 : F2 → F2 → F2 → F2),
      (∑ t : F2, ∑ r : F2, ∑ s : F2, (f1 t r s + f2 t r s + f3 t r s)) =
      (∑ t : F2, ∑ r : F2, ∑ s : F2, f1 t r s) +
      (∑ t : F2, ∑ r : F2, ∑ s : F2, f2 t r s) +
      (∑ t : F2, ∑ r : F2, ∑ s : F2, f3 t r s) := by
    intro f1 f2 f3
    simp only [Finset.sum_add_distrib]
  rw [hsplit3]
  have hlin0 : (∑ t : F2, ∑ r : F2, ∑ s : F2, (cOut + dotProduct aOut (cube t r s))) = 0 := by
    have hpt : ∀ t r s : F2, cOut + dotProduct aOut (cube t r s) =
        cOut + aOut 0 * t + aOut u0.succ * r + aOut v0.succ * s := by
      intro t r s; dsimp only [cube, eU, eV]; rw [dotProduct_cons_e]; ring
    simp_rw [hpt]; exact sum_cube_lin _ _ _ _
  have hquad0 : (∑ t : F2, ∑ r : F2, ∑ s : F2,
      ∑ j : Fin (k + 1), (cT j + dotProduct (aT j) (cube t r s)) * cube t r s j) = 0 := by
    conv_lhs =>
      arg 2; ext t
      arg 2; ext r
      rw [Finset.sum_comm]
    conv_lhs =>
      arg 2; ext t
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero; intro j _
    have hj_lin : ∃ a0 b0 d0 : F2, ∀ t r s : F2, cube t r s j = 0 + a0 * t + b0 * r + d0 * s := by
      refine Fin.cases ⟨1, 0, 0, fun t r s => by simp [cube]⟩ (fun j' => ?_) j
      refine ⟨0, if j' = u0 then 1 else 0, if j' = v0 then 1 else 0, fun t r s => ?_⟩
      simp only [cube, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eU, eV]
      split_ifs <;> ring
    rcases hj_lin with ⟨a0, b0, d0, hj_eq⟩
    have hpt : ∀ t r s : F2,
        (cT j + dotProduct (aT j) (cube t r s)) * cube t r s j =
        (cT j + aT j 0 * t + aT j u0.succ * r + aT j v0.succ * s) *
        (0 + a0 * t + b0 * r + d0 * s) := by
      intro t r s; rw [hj_eq]; dsimp only [cube, eU, eV]; rw [dotProduct_cons_e]; ring
    simp_rw [hpt]
    exact sum_cube_mul2 _ _ _ _ _ _ _ _
  have hcub : (∑ t : F2, ∑ r : F2, ∑ s : F2,
      (δOut + dotProduct δT (cube t r s)) * (cU + dotProduct aU (cube t r s)) *
        (cV + dotProduct aV (cube t r s))) =
      δT 0 * (aU u0.succ * aV v0.succ + aU v0.succ * aV u0.succ) +
      aU 0 * (δT u0.succ * aV v0.succ + δT v0.succ * aV u0.succ) +
      aV 0 * (δT u0.succ * aU v0.succ + δT v0.succ * aU u0.succ) := by
    have hpt : ∀ t r s : F2,
        (δOut + dotProduct δT (cube t r s)) * (cU + dotProduct aU (cube t r s)) *
          (cV + dotProduct aV (cube t r s)) =
        (δOut + δT 0 * t + δT u0.succ * r + δT v0.succ * s) *
        (cU + aU 0 * t + aU u0.succ * r + aU v0.succ * s) *
        (cV + aV 0 * t + aV u0.succ * r + aV v0.succ * s) := by
      intro t r s; dsimp only [cube, eU, eV]; simp only [dotProduct_cons_e]; ring
    simp_rw [hpt, sum_cube_mul3]
  rw [hlin0, hquad0, hcub, zero_add, zero_add]

lemma single_le_sum_cube (F : F2 → F2 → F2 → ℝ) (hnn : ∀ t r s, 0 ≤ F t r s) (t0 r0 s0 : F2) :
    F t0 r0 s0 ≤ ∑ t : F2, ∑ r : F2, ∑ s : F2, F t r s := by
  have h1 : F t0 r0 s0 ≤ ∑ s : F2, F t0 r0 s :=
    Finset.single_le_sum (fun s _ => hnn t0 r0 s) (Finset.mem_univ s0)
  have h2 : F t0 r0 s0 ≤ ∑ r : F2, ∑ s : F2, F t0 r s :=
    le_trans h1 (Finset.single_le_sum (fun r _ => Finset.sum_nonneg (fun s _ => hnn t0 r s)) (Finset.mem_univ r0))
  exact le_trans h2 (Finset.single_le_sum (fun t _ => Finset.sum_nonneg (fun r _ =>
    Finset.sum_nonneg (fun s _ => hnn t r s))) (Finset.mem_univ t0))

lemma full_flat_atom_bound {k N m : ℕ}
    (Z : Fin N → Fin k → F2)
    (u v : Fin m → Fin k) (label : Fin m → F2)
    (f : (Fin (k + 1) → F2) → ℤ)
    (D : Circuit) (tap : Fin (k + 1) → ℕ)
    (hlegD : legalGates (k + 1) D.gates) (hcostD1 : costGates D.gates ≤ 1)
    (hout_lt : D.output < (k + 1) + D.gates.length)
    (htap_lt : ∀ j : Fin (k + 1), tap j < (k + 1) + D.gates.length)
    (hf_eq : ∀ y : Fin (k + 1) → F2,
      f y = signB (Bool.xor (D.eval (bitsOf (k + 1) y))
        (decide (dotProduct (fun j : Fin (k + 1) =>
          b2f ((D.wires (bitsOf (k + 1) y)).getD (tap j) false)) y = 1)))) :
    ∃ w : ((Fin k → F2) × (Fin k → F2)) → ℝ,
      (∀ p, 0 ≤ w p) ∧ (∑ p, w p) = 1 ∧
      ∀ i : Fin m,
        (∑ p, w p * (if p.1 (u i) * p.2 (v i) + p.1 (v i) * p.2 (u i) = label i then (0 : ℝ) else 1)) ≤
        4 * (∑ j : Fin N, errAtom f (Fin.cons 0 (Z j)) 0) / N +
        ∑ t : F2, ∑ r : F2, ∑ s : F2,
          errAtom f (Fin.cons t (r • (fun j : Fin k => if j = u i then (1 : F2) else 0) +
            s • (fun j : Fin k => if j = v i then (1 : F2) else 0))) (t * r * s * label i) := by
  have herr_nonneg : ∀ y b, 0 ≤ errAtom f y b := by
    intro y b
    rw [errAtom_sign (hf_eq y)]
    split_ifs <;> norm_num
  rcases cost_le_one_wires D.gates hlegD hcostD1 with ⟨cU, cV, aU, aV, hwires⟩
  rcases hwires D.output hout_lt with ⟨cOut, aOut, δOut, hOut⟩
  choose cT aT δT hT using fun j : Fin (k + 1) => hwires (tap j) (htap_lt j)
  rcases exists_pair_for_det3 δT aU aV with ⟨p0, hp0⟩
  refine ⟨fun q => if q = p0 then 1 else 0, fun q => by dsimp only; split_ifs <;> norm_num, by simp, fun i => ?_⟩
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hZ_nn : 0 ≤ 4 * (∑ j : Fin N, errAtom f (Fin.cons 0 (Z j)) 0) / N :=
    div_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => herr_nonneg _ _)))
      (Nat.cast_nonneg N)
  have hcube_nn : 0 ≤ ∑ t : F2, ∑ r : F2, ∑ s : F2,
      errAtom f (Fin.cons t (r • (fun j : Fin k => if j = u i then (1 : F2) else 0) +
        s • (fun j : Fin k => if j = v i then (1 : F2) else 0))) (t * r * s * label i) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => herr_nonneg _ _)))
  by_cases hgood : p0.1 (u i) * p0.2 (v i) + p0.1 (v i) * p0.2 (u i) = label i
  · simp only [hgood, ↓reduceIte]; linarith
  · simp only [hgood, ↓reduceIte]
    let g : (Fin (k + 1) → F2) → F2 := fun y =>
      b2f (D.eval (bitsOf (k + 1) y)) +
        dotProduct (fun j : Fin (k + 1) => b2f ((D.wires (bitsOf (k + 1) y)).getD (tap j) false)) y
    have hA_g : ∀ y : Fin (k + 1) → F2, f y = signB (decide (g y = 1)) := by
      intro y
      rw [hf_eq y]
      congr 1
      dsimp only [g]
      rw [zmod2_add_decide, decide_b2f]
    let cube : F2 → F2 → F2 → (Fin (k + 1) → F2) := fun t r s =>
      Fin.cons t (r • (fun j : Fin k => if j = u i then (1 : F2) else 0) +
        s • (fun j : Fin k => if j = v i then (1 : F2) else 0))
    have hg_form : ∀ y : Fin (k + 1) → F2,
        g y = (cOut + dotProduct aOut y) +
          (∑ j : Fin (k + 1), (cT j + dotProduct (aT j) y) * y j) +
          (δOut + dotProduct δT y) * (cU + dotProduct aU y) * (cV + dotProduct aV y) := by
      intro y
      dsimp only [g]
      have h1 : b2f (D.eval (bitsOf (k + 1) y)) =
          cOut + dotProduct aOut y + δOut * (cU + dotProduct aU y) * (cV + dotProduct aV y) :=
        hOut y
      have h2 : ∀ j : Fin (k + 1), b2f ((D.wires (bitsOf (k + 1) y)).getD (tap j) false) * y j =
          (cT j + dotProduct (aT j) y) * y j +
          (δT j * y j) * (cU + dotProduct aU y) * (cV + dotProduct aV y) := by
        intro j
        change b2f ((wiresOf D.gates (bitsOf (k + 1) y)).getD (tap j) false) * y j = _
        rw [hT j y]; ring
      have hdot_y : dotProduct (fun j : Fin (k + 1) =>
            b2f ((D.wires (bitsOf (k + 1) y)).getD (tap j) false)) y =
          (∑ j : Fin (k + 1), (cT j + dotProduct (aT j) y) * y j) +
          (dotProduct δT y) * (cU + dotProduct aU y) * (cV + dotProduct aV y) := by
        change (∑ j : Fin (k + 1), b2f ((D.wires (bitsOf (k + 1) y)).getD (tap j) false) * y j) = _
        simp_rw [h2, Finset.sum_add_distrib, ← Finset.sum_mul]
        rfl
      rw [h1, hdot_y]
      ring
    have hsum_g : (∑ t : F2, ∑ r : F2, ∑ s : F2, g (cube t r s)) =
        p0.1 (u i) * p0.2 (v i) + p0.1 (v i) * p0.2 (u i) := by
      simp_rw [hg_form]
      rw [cube_sum_deg3 (u i) (v i) cOut cU cV δOut aOut aU aV δT cT aT, ← hp0 (u i) (v i)]
    have hsum_rhs : (∑ t : F2, ∑ r : F2, ∑ s : F2, t * r * s * label i) = label i := by
      simp only [sum_f2]; ring
    have hex : ∃ (t0 r0 s0 : F2), g (cube t0 r0 s0) ≠ t0 * r0 * s0 * label i := by
      by_contra hall
      push Not at hall
      have heq : (∑ t : F2, ∑ r : F2, ∑ s : F2, g (cube t r s)) =
          ∑ t : F2, ∑ r : F2, ∑ s : F2, t * r * s * label i := by
        apply Finset.sum_congr rfl; intro t _
        apply Finset.sum_congr rfl; intro r _
        apply Finset.sum_congr rfl; intro s _
        exact hall t r s
      rw [hsum_g, hsum_rhs] at heq
      exact hgood heq
    rcases hex with ⟨t0, r0, s0, hne⟩
    have herr1 : errAtom f (cube t0 r0 s0) (t0 * r0 * s0 * label i) = 1 := by
      rw [errAtom_sign (hA_g (cube t0 r0 s0))]
      have hdec : decide (g (cube t0 r0 s0) = 1) ≠ decide (t0 * r0 * s0 * label i = 1) := by
        intro h
        have := congrArg b2f h
        rw [b2f_decide, b2f_decide] at this
        exact hne this
      simp only [hdec, ↓reduceIte]
    have hcube_ge : (1 : ℝ) ≤ ∑ t : F2, ∑ r : F2, ∑ s : F2,
        errAtom f (Fin.cons t (r • (fun j : Fin k => if j = u i then (1 : F2) else 0) +
          s • (fun j : Fin k => if j = v i then (1 : F2) else 0))) (t * r * s * label i) := by
      have hle := single_le_sum_cube
        (fun t r s => errAtom f (Fin.cons t (r • (fun j : Fin k => if j = u i then (1 : F2) else 0) +
          s • (fun j : Fin k => if j = v i then (1 : F2) else 0))) (t * r * s * label i))
        (fun t r s => herr_nonneg _ _) t0 r0 s0
      rw [herr1] at hle
      exact hle
    exact le_trans hcube_ge (le_add_of_nonneg_left hZ_nn)

end Part33649

end PEqualNP.Outside.L_meta_33649

theorem PEqualNP.Outside.L_meta_33649 : (∀ k : ℕ,
  let n := k+1
  let F := ZMod 2
  let S := Fin k → F
  let V := Fin (k+1) → F
  let e := fun (i j : Fin k) => if j = i then (1 : F) else 0
  let bits := fun (x : V) => List.ofFn (fun i => decide (x i = 1))
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*n) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
    C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)) ≤ n+1
  let err := fun (C : Circ) (y : V) (b : F) =>
    (∑ x : V, if C.eval (bits x ++ bits y) = decide (dotProduct x y+b = 1)
      then (0 : ℝ) else 1) / Fintype.card V
  ∀ (N : ℕ) (Z : Fin N → S), 0 < N →
    (∀ (a : S) (b : F), a ≠ 0 →
      N ≤ 4*((Finset.univ : Finset (Fin N)).filter (fun j => dotProduct a (Z j) ≠ b)).card) →
    ∀ (m : ℕ) (u v : Fin m → Fin k) (label : Fin m → F), (∀ i, u i ≠ v i) →
      let loss := fun (C : Circ) (i : Fin m) =>
        4*(∑ j, err C (Fin.cons 0 (Z j)) 0) / N +
        ∑ t : F, ∑ r : F, ∑ s : F, err C (Fin.cons t (r • e (u i) + s • e (v i))) (t*r*s*label i)
      let bad := fun (p : S × S) (i : Fin m) =>
        if p.1 (u i)*p.2 (v i) + p.1 (v i)*p.2 (u i) = label i then (0 : ℝ) else 1
      (∀ C : Circ, legal C → ∃ w : S × S → ℝ,
        (∀ p, 0 ≤ w p) ∧ (∑ p, w p) = 1 ∧ ∀ i, (∑ p, w p * bad p i) ≤ loss C i) ∧
      ∀ p : S × S, ∃ C : Circ, legal C ∧ ∀ i, loss C i = bad p i) := by
  open PEqualNP.Outside.L_meta_33649 in
  intro k n F S V e bits Circ legal err N Z hNpos hZ m u v label huv loss bad
  have hcardV : (Fintype.card V : ℝ) = (2 : ℝ) ^ n := by
    simp only [V, F, n, Fintype.card_fun, Fintype.card_fin, ZMod.card]
    push_cast; rfl
  have hcardV_ne : (Fintype.card V : ℝ) ≠ 0 := by
    rw [hcardV]; positivity
  constructor
  · intro C hC
    have hlegC : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * n + 0) C ∧
        ∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
          (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)) :=
      ⟨by simpa using hC.1, hC.2.1⟩
    have hcostC : costGates C.gates ≤ n + 1 := hC.2.2
    rcases main_844_fwd n 0 (n + 1) C hlegC hcostC with ⟨M, r, A, hAtom, hWeight, hProf⟩
    let μ : Fin M → ℝ := fun α => (2 : ℝ) ^ (n - r α) / (2 : ℝ) ^ n
    have hμ_nonneg : ∀ α : Fin M, 0 ≤ μ α := fun α => by
      dsimp only [μ]; positivity
    have hμ_sum : (∑ α : Fin M, μ α) = 1 := by
      dsimp only [μ]
      rw [← Finset.sum_div]
      have hcast : (∑ α : Fin M, (2 : ℝ) ^ (n - r α)) = (2 : ℝ) ^ n := by
        exact_mod_cast hWeight
      rw [hcast, div_self (by positivity)]
    have herr_eq : ∀ (y : V) (b : F),
        err C y b = ∑ α : Fin M, μ α * errAtom (fun y' => A α y' ![]) y b := by
      intro y b
      have hprof_y := hProf y ![]
      have hbits0 : bitsOf 0 ![] = [] := rfl
      have hsum_x : (∑ x : V, if C.eval (bits x ++ bits y) = decide (dotProduct x y + b = 1) then (0 : ℝ) else 1) =
          ((Fintype.card V : ℝ) - (signB (decide (b = 1)) : ℝ) *
            ((∑ α : Fin M, (2 : ℤ) ^ (n - r α) * A α y ![] : ℤ) : ℝ)) / 2 := by
        have hpt : ∀ x : V,
            (if C.eval (bits x ++ bits y) = decide (dotProduct x y + b = 1) then (0 : ℝ) else 1) =
              (1 - (signB (decide (b = 1)) : ℝ) *
                (signB (Bool.xor (C.eval (bits x ++ bits y)) (decide (dotProduct x y = 1))) : ℝ)) / 2 := by
          intro x
          rw [zmod2_add_decide]
          exact err_indicator_eq_sign _ _ _
        simp_rw [hpt, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        congr 2; congr 1
        have hp_cast : ((∑ x : V, signB (Bool.xor (C.eval (bits x ++ bits y)) (decide (dotProduct x y = 1))) : ℤ) : ℝ) =
            ((∑ α : Fin M, (2 : ℤ) ^ (n - r α) * A α y ![] : ℤ) : ℝ) := by
          congr 1
          simpa [bits, bitsOf, signB, hbits0] using hprof_y
        simpa using hp_cast
      dsimp only [err]
      rw [hsum_x, div_div, mul_comm (2 : ℝ), ← div_div, sub_div, div_self hcardV_ne, hcardV]
      have hlin : (signB (decide (b = 1)) : ℝ) *
          (((∑ α : Fin M, (2 : ℤ) ^ (n - r α) * A α y ![] : ℤ) : ℝ)) / (2 : ℝ) ^ n =
          ∑ α : Fin M, μ α * ((signB (decide (b = 1)) : ℝ) * (A α y ![] : ℝ)) := by
        push_cast
        rw [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl; intro α _
        dsimp only [μ]; ring
      rw [hlin]
      have h1 : (1 : ℝ) = ∑ α : Fin M, μ α := hμ_sum.symm
      conv_lhs => rw [h1, ← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl; intro α _
      dsimp only [errAtom]; ring
    let lossAtom : (V → ℤ) → Fin m → ℝ := fun f i =>
      4 * (∑ j : Fin N, errAtom f (Fin.cons 0 (Z j)) 0) / N +
      ∑ t : F, ∑ r : F, ∑ s : F, errAtom f (Fin.cons t (r • e (u i) + s • e (v i))) (t * r * s * label i)
    have hloss_eq : ∀ i : Fin m, loss C i = ∑ α : Fin M, μ α * lossAtom (fun y => A α y ![]) i := by
      intro i
      dsimp only [loss, lossAtom]
      simp_rw [herr_eq]
      rw [Finset.sum_comm]
      have h1 : 4 * (∑ α : Fin M, ∑ j : Fin N, μ α * errAtom (fun y => A α y ![]) (Fin.cons 0 (Z j)) 0) / N =
          ∑ α : Fin M, μ α * (4 * (∑ j : Fin N, errAtom (fun y => A α y ![]) (Fin.cons 0 (Z j)) 0) / N) := by
        simp_rw [← Finset.mul_sum]
        rw [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl; intro α _; ring
      have h2 : (∑ t : F, ∑ r : F, ∑ s : F, ∑ α : Fin M,
            μ α * errAtom (fun y => A α y ![]) (Fin.cons t (r • e (u i) + s • e (v i))) (t * r * s * label i)) =
          ∑ α : Fin M, μ α * (∑ t : F, ∑ r : F, ∑ s : F,
            errAtom (fun y => A α y ![]) (Fin.cons t (r • e (u i) + s • e (v i))) (t * r * s * label i)) := by
        simp_rw [Finset.sum_comm (s := (Finset.univ : Finset F)) (t := (Finset.univ : Finset (Fin M)))]
        apply Finset.sum_congr rfl; intro α _
        simp_rw [← Finset.mul_sum]
      rw [h1, h2, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro α _; ring
    have hEach : ∀ α : Fin M, ∃ wα : S × S → ℝ,
        (∀ p, 0 ≤ wα p) ∧ (∑ p, wα p) = 1 ∧
        ∀ i : Fin m, (∑ p, wα p * bad p i) ≤ lossAtom (fun y => A α y ![]) i := by
      intro α
      rcases hAtom α with ⟨W, a, D, tap, hfinW, hlegD, hcostD, houtD, htapD, hA⟩
      have hf_vals : ∀ y : V, A α y ![] = 0 ∨ A α y ![] = 1 ∨ A α y ![] = -1 := by
        intro y
        by_cases hy : y - a ∈ W
        · have h := (hA y ![]).1 hy
          rw [h]
          have hsign : ∀ b : Bool, (if b = true then (-1 : ℤ) else 1) = 1 ∨ (if b = true then (-1 : ℤ) else 1) = -1 := by
            intro b; cases b <;> simp
          exact Or.inr (hsign _)
        · exact Or.inl ((hA y ![]).2 hy)
      have hfinW' : Module.finrank F2 W = r α := hfinW
      have hfinV : Module.finrank F2 V = n := by
        change Module.finrank F2 (Fin n → F2) = n
        simp
      have hr_le : r α ≤ n := by
        have h1 : Module.finrank F2 W ≤ Module.finrank F2 V := Submodule.finrank_le W
        omega
      by_cases hr_lt : r α < n
      · exact proper_flat_atom_bound Z hNpos hZ u v label huv (fun y => A α y ![]) W a
          (by rw [hfinW']; exact hr_lt) hf_vals (fun y hy => (hA y ![]).2 hy)
      · have hr_eq : r α = n := by omega
        have hW_top : W = ⊤ := by
          apply Submodule.eq_top_of_finrank_eq
          rw [hfinW', hr_eq, hfinV]
        have hcostD1 : costGates D.gates ≤ 1 := by
          have : costGates D.gates + r α ≤ n + 1 := hcostD
          omega
        have hlegD' : legalGates (k + 1) D.gates :=
          ⟨(readsBack_mk_iff D).mpr (by simpa using hlegD.1), hlegD.2⟩
        have hout_lt : D.output < (k + 1) + D.gates.length := by
          simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using houtD
        have htap_lt : ∀ j : Fin (k + 1), tap j < (k + 1) + D.gates.length := by
          intro j; simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using htapD j
        have hf_eq : ∀ y : Fin (k + 1) → F2,
            A α y ![] = signB (Bool.xor (D.eval (bitsOf (k + 1) y))
              (decide (dotProduct (fun j : Fin (k + 1) =>
                b2f ((D.wires (bitsOf (k + 1) y)).getD (tap j) false)) y = 1))) := by
          intro y
          have hy : y - a ∈ W := by rw [hW_top]; trivial
          have h := (hA y ![]).1 hy
          have hbits0 : bitsOf (k + 1) y ++ bitsOf 0 ![] = bitsOf (k + 1) y := by simp [bitsOf]
          simpa [signB, b2f, bitsOf, hbits0] using h
        exact full_flat_atom_bound Z u v label (fun y => A α y ![]) D tap hlegD' hcostD1
          hout_lt htap_lt hf_eq
    choose wα hwα_nn hwα_sum hwα_le using hEach
    refine ⟨fun p => ∑ α : Fin M, μ α * wα α p, ?_, ?_, ?_⟩
    · intro p
      exact Finset.sum_nonneg (fun α _ => mul_nonneg (hμ_nonneg α) (hwα_nn α p))
    · rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hwα_sum, mul_one]
      exact hμ_sum
    · intro i
      rw [hloss_eq i]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum; intro α _
      simp_rw [mul_assoc, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hwα_le α i) (hμ_nonneg α)
  · intro p
    rcases exists_upper_circuit p with ⟨C, hlegC, hcostC, hevalC⟩
    refine ⟨C, ⟨(readsBack_mk_iff C).mp hlegC.1, hlegC.2, hcostC⟩, fun i => ?_⟩
    have herr_of_g : ∀ (y : V) (b : F),
        err C y b =
          if y 0 * (dotProduct p.1 (Fin.tail y) * dotProduct p.2 (Fin.tail y) +
              ∑ l : Fin k, (p.1 l * p.2 l) * y l.succ) = b then 0 else 1 := by
      intro y b
      set gy : F := y 0 * (dotProduct p.1 (Fin.tail y) * dotProduct p.2 (Fin.tail y) +
        ∑ l : Fin k, (p.1 l * p.2 l) * y l.succ)
      dsimp only [err]
      have hpt : ∀ x : V,
          (if C.eval (bits x ++ bits y) = decide (dotProduct x y + b = 1) then (0 : ℝ) else 1) =
          if gy = b then 0 else 1 := by
        intro x
        have hev : C.eval (bits x ++ bits y) = decide (dotProduct x y + gy = 1) := hevalC x y
        rw [hev]
        by_cases hgb : gy = b
        · simp [hgb]
        · have hne : decide (dotProduct x y + gy = 1) ≠ decide (dotProduct x y + b = 1) := by
            intro h
            have hb := congrArg b2f h
            rw [b2f_decide, b2f_decide] at hb
            exact hgb (add_left_cancel hb)
          simp [hgb, hne]
      simp_rw [hpt]
      by_cases hgb : gy = b
      · simp [hgb]
      · simp only [hgb, ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
          div_self hcardV_ne]
    have hZ0 : ∀ j : Fin N, err C (Fin.cons 0 (Z j)) 0 = 0 := by
      intro j; rw [herr_of_g]; simp
    have hcube : ∀ (t r s : F),
        err C (Fin.cons t (r • e (u i) + s • e (v i))) (t * r * s * label i) =
          if t = 1 ∧ r = 1 ∧ s = 1 then bad p i else 0 := by
      intro t r s
      let y0 : V := Fin.cons t (r • e (u i) + s • e (v i))
      change err C y0 (t * r * s * label i) = _
      rw [herr_of_g]
      have htail : Fin.tail y0 = r • e (u i) + s • e (v i) := by funext l; rfl
      have hdot1 : dotProduct p.1 (r • e (u i) + s • e (v i)) = r * p.1 (u i) + s * p.1 (v i) := by
        rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
        have h1 : dotProduct p.1 (e (u i)) = p.1 (u i) := by simp [dotProduct, e]
        have h2 : dotProduct p.1 (e (v i)) = p.1 (v i) := by simp [dotProduct, e]
        rw [h1, h2]; simp only [smul_eq_mul]
      have hdot2 : dotProduct p.2 (r • e (u i) + s • e (v i)) = r * p.2 (u i) + s * p.2 (v i) := by
        rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
        have h1 : dotProduct p.2 (e (u i)) = p.2 (u i) := by simp [dotProduct, e]
        have h2 : dotProduct p.2 (e (v i)) = p.2 (v i) := by simp [dotProduct, e]
        rw [h1, h2]; simp only [smul_eq_mul]
      have hdiag : (∑ l : Fin k, (p.1 l * p.2 l) * y0 l.succ) =
          r * (p.1 (u i) * p.2 (u i)) + s * (p.1 (v i) * p.2 (v i)) := by
        simp only [y0, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, e]
        have hpt : ∀ l : Fin k,
            p.1 l * p.2 l * (r * (if l = u i then (1 : F) else 0) + s * (if l = v i then (1 : F) else 0)) =
            (if l = u i then r * (p.1 l * p.2 l) else 0) +
            (if l = v i then s * (p.1 l * p.2 l) else 0) := by
          intro l; split_ifs <;> ring
        simp_rw [hpt, Finset.sum_add_distrib]
        simp
      have hgy : y0 0 * (dotProduct p.1 (Fin.tail y0) * dotProduct p.2 (Fin.tail y0) +
            ∑ l : Fin k, (p.1 l * p.2 l) * y0 l.succ) =
          t * r * s * (p.1 (u i) * p.2 (v i) + p.1 (v i) * p.2 (u i)) := by
        have hy00 : y0 0 = t := rfl
        rw [hy00, htail, hdot1, hdot2, hdiag]
        have hr2 : r * r = r := by rcases zmod2_cases r with h | h <;> rw [h] <;> decide
        have hs2 : s * s = s := by rcases zmod2_cases s with h | h <;> rw [h] <;> decide
        have h2a : r * (p.1 (u i) * p.2 (u i)) + r * (p.1 (u i) * p.2 (u i)) = 0 := by
          rcases zmod2_cases (r * (p.1 (u i) * p.2 (u i))) with h | h <;> rw [h] <;> decide
        have h2b : s * (p.1 (v i) * p.2 (v i)) + s * (p.1 (v i) * p.2 (v i)) = 0 := by
          rcases zmod2_cases (s * (p.1 (v i) * p.2 (v i))) with h | h <;> rw [h] <;> decide
        linear_combination t * (p.1 (u i) * p.2 (u i)) * hr2 +
          t * (p.1 (v i) * p.2 (v i)) * hs2 + t * h2a + t * h2b
      rw [hgy]
      rcases zmod2_cases t with rfl | rfl <;>
        rcases zmod2_cases r with rfl | rfl <;>
        rcases zmod2_cases s with rfl | rfl <;>
        simp [bad]
    dsimp only [loss]
    simp_rw [hZ0, hcube]
    have hsum_cube : (∑ t : F2, ∑ r : F2, ∑ s : F2, if t = 1 ∧ r = 1 ∧ s = 1 then bad p i else 0) = bad p i := by
      simp only [sum_f2_real]
      simp
    have h0 : 4 * (∑ _j : Fin N, (0 : ℝ)) / N = 0 := by simp
    rw [h0, zero_add]
    exact hsum_cube


