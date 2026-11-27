import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29780_aux

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

end PEqualNP.Outside.L_meta_29780_aux

theorem PEqualNP.Outside.L_meta_29780 :
∀ (k s : ℕ),
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
  let E := Fin s → F
  let quad := fun (q : E → F) =>
    ∃ (b : F) (a : E) (M : Fin s → Fin s → F), ∀ v,
      q v = b + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j
  let raw := fun (g : V → F) (C : Circ) => (∑ x : V, ∑ y : V,
    if C.eval (bits k x ++ bits k y) = decide (dotProduct x y + g y = 1)
    then (1 : ℤ) else -1).natAbs
  s ≤ k → ∀ (g : V → F) (T : ℕ),
    let viaCircuit := ∃ C : Circ, legal (2*k) C ∧ cost C ≤ s ∧ T ≤ raw g C
    let viaFlat := ∃ (B : E →ₗ[F] V) (a : V) (q : E → F), Function.Injective B ∧ quad q ∧
      T ≤ 2^k * (∑ v : E, if g (a+B v) = q v then (1 : ℤ) else -1).natAbs
    (viaFlat → viaCircuit) ∧ (2^(k+s) < 2*T → (viaCircuit ↔ viaFlat)) ∧
      (viaCircuit → T ≤ 2^(k+s)) := by
  intro k s Circ F legal cost bits V E quad raw _ g T viaCircuit viaFlat
  have hflat : viaFlat → viaCircuit := by
    rintro ⟨B, a, q, hB, hq, hT⟩
    exact PEqualNP.Outside.L_meta_29780_aux.viaFlat_to_viaCircuit k s g T B a q hB hq hT
  refine ⟨hflat, ?_, ?_⟩
  · intro hbig
    refine ⟨?_, hflat⟩
    rintro ⟨C, hleg, hcost, hT⟩
    exact PEqualNP.Outside.L_meta_29780_aux.viaCircuit_to_viaFlat k s g T hbig C hleg hcost hT
  · rintro ⟨C, hleg, hcost, hT⟩
    exact PEqualNP.Outside.L_meta_29780_aux.viaCircuit_le_bound k s g T C hleg hcost hT
