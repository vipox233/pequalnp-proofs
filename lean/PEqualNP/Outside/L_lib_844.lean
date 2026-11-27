import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_844_aux

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

end PEqualNP.Outside.L_lib_844_aux

theorem PEqualNP.Outside.L_lib_844 :
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
        ∀ y z, prof C y z = (2 : ℤ)^k * A y z) :=
  PEqualNP.Outside.L_lib_844_aux.main_844
