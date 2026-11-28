import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29948_aux

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


lemma z2_add_self (a : F2) : a + a = 0 := by
  fin_cases a <;> decide

structure SSlice (n : ℕ) where
  U : Submodule F2 (Fin n → F2)
  p : Fin n → F2
  slope : ℕ → (Fin n → F2)
  off0 : ℕ → F2
  off1 : ℕ → F2

def ValidSSlice {n : ℕ} (gs : List Gate) (S : SSlice n) : Prop :=
  n ≤ Module.finrank F2 S.U + costGates gs ∧
  ∀ w < n + 1 + gs.length, ∀ v : Fin n → F2, v ∈ S.U →
    (wiresOf gs (bitsOf (n + 1) (Fin.cons 0 (S.p + v)))).getD w false =
      decide (dotProduct (S.slope w) v + S.off0 w = 1) ∧
    (wiresOf gs (bitsOf (n + 1) (Fin.cons 1 (S.p + v)))).getD w false =
      decide (dotProduct (S.slope w) v + S.off1 w = 1)

def SSlice.upd {n : ℕ} (S : SSlice n) (w0 : ℕ) (a : Fin n → F2) (c0 c1 : F2) : SSlice n where
  U := S.U
  p := S.p
  slope := fun w => if w = w0 then a else S.slope w
  off0 := fun w => if w = w0 then c0 else S.off0 w
  off1 := fun w => if w = w0 then c1 else S.off1 w

lemma SSlice.valid_upd {n : ℕ} {gs : List Gate} {g : Gate} {S : SSlice n}
    (hS : ValidSSlice gs S) (a : Fin n → F2) (c0 c1 : F2)
    (hnew : ∀ v : Fin n → F2, v ∈ S.U →
      g.op.eval (g.inputs.map fun i => (wiresOf gs (bitsOf (n + 1) (Fin.cons 0 (S.p + v)))).getD i false) =
        decide (dotProduct a v + c0 = 1) ∧
      g.op.eval (g.inputs.map fun i => (wiresOf gs (bitsOf (n + 1) (Fin.cons 1 (S.p + v)))).getD i false) =
        decide (dotProduct a v + c1 = 1)) :
    ValidSSlice (gs ++ [g]) (S.upd (n + 1 + gs.length) a c0 c1) := by
  have hcost_le : costGates gs ≤ costGates (gs ++ [g]) := by rw [costGates_append]; omega
  refine ⟨by have h1 : n ≤ Module.finrank F2 S.U + costGates gs := hS.1; change n ≤ Module.finrank F2 S.U + costGates (gs ++ [g]); omega, ?_⟩
  intro w hw v hv
  simp only [List.length_append, List.length_singleton] at hw
  dsimp only [SSlice.upd] at hv ⊢
  by_cases hweq : w = n + 1 + gs.length
  · subst hweq
    simp only [↓reduceIte]
    rw [wiresOf_snoc_last_eq gs g _ (bitsOf_len (n + 1) _),
        wiresOf_snoc_last_eq gs g _ (bitsOf_len (n + 1) _)]
    exact hnew v hv
  · simp only [hweq, ↓reduceIte]
    rw [wiresOf_append_getD_lt gs [g] _ (by rw [bitsOf_len]; omega),
        wiresOf_append_getD_lt gs [g] _ (by rw [bitsOf_len]; omega)]
    exact hS.2 w (by omega) v hv

def SSlice.split0 {n : ℕ} (S : SSlice n) (a : Fin n → F2) : SSlice n where
  U := kerDot S.U a
  p := S.p
  slope := S.slope
  off0 := S.off0
  off1 := S.off1

def SSlice.split1 {n : ℕ} (S : SSlice n) (a v0 : Fin n → F2) : SSlice n where
  U := kerDot S.U a
  p := S.p + v0
  slope := S.slope
  off0 := fun w => S.off0 w + dotProduct (S.slope w) v0
  off1 := fun w => S.off1 w + dotProduct (S.slope w) v0

lemma SSlice.split_spec {n : ℕ} {gs : List Gate} (S : SSlice n) (hS : ValidSSlice gs S)
    (a v0 : Fin n → F2) (hv0 : v0 ∈ S.U) (hdot : dotProduct a v0 = 1) :
    let S0 := S.split0 a
    let S1 := S.split1 a v0
    Module.finrank F2 S0.U + 1 = Module.finrank F2 S.U ∧
    Module.finrank F2 S1.U + 1 = Module.finrank F2 S.U ∧
    (∀ w < n + 1 + gs.length, ∀ v ∈ S0.U,
      (wiresOf gs (bitsOf (n + 1) (Fin.cons 0 (S0.p + v)))).getD w false =
        decide (dotProduct (S0.slope w) v + S0.off0 w = 1) ∧
      (wiresOf gs (bitsOf (n + 1) (Fin.cons 1 (S0.p + v)))).getD w false =
        decide (dotProduct (S0.slope w) v + S0.off1 w = 1)) ∧
    (∀ w < n + 1 + gs.length, ∀ v ∈ S1.U,
      (wiresOf gs (bitsOf (n + 1) (Fin.cons 0 (S1.p + v)))).getD w false =
        decide (dotProduct (S1.slope w) v + S1.off0 w = 1) ∧
      (wiresOf gs (bitsOf (n + 1) (Fin.cons 1 (S1.p + v)))).getD w false =
        decide (dotProduct (S1.slope w) v + S1.off1 w = 1)) ∧
    (∀ u : Fin n → F2,
      (u - S.p ∈ S.U → (u - S0.p ∈ S0.U ∨ u - S1.p ∈ S1.U) ∧ ¬ (u - S0.p ∈ S0.U ∧ u - S1.p ∈ S1.U)) ∧
      (u - S.p ∉ S.U → u - S0.p ∉ S0.U ∧ u - S1.p ∉ S1.U)) := by
  intro S0 S1
  have hdim := finrank_ker_dot S.U a v0 hv0 hdot
  refine ⟨hdim, hdim, ?_, ?_, ?_⟩
  · intro w hw v hv
    exact hS.2 w hw v hv.1
  · intro w hw v hv
    have hmem : v0 + v ∈ S.U := S.U.add_mem hv0 hv.1
    have hadd : S1.p + v = S.p + (v0 + v) := by dsimp only [S1, SSlice.split1]; abel
    have h2 := hS.2 w hw (v0 + v) hmem
    rw [hadd, h2.1, h2.2]
    dsimp only [S1, SSlice.split1]
    rw [dotProduct_add]
    exact ⟨congrArg (fun x => decide (x = 1)) (by ring), congrArg (fun x => decide (x = 1)) (by ring)⟩
  · intro u
    have hdiff1 : u - S1.p = (u - S.p) + v0 := by
      dsimp only [S1, SSlice.split1]
      rw [zmod2_vec_sub_eq_add, zmod2_vec_sub_eq_add, add_assoc]
    constructor
    · intro hu
      constructor
      · rcases zmod2_cases (dotProduct a (u - S.p)) with hd | hd
        · left; exact ⟨hu, hd⟩
        · right
          rw [hdiff1]
          refine ⟨S.U.add_mem hu hv0, ?_⟩
          show dotProduct a ((u - S.p) + v0) = 0
          rw [dotProduct_add, hd, hdot]; decide
      · rintro ⟨h0, h1⟩
        rw [hdiff1] at h1
        have hd0 : dotProduct a (u - S.p) = 0 := h0.2
        have hd1 : dotProduct a ((u - S.p) + v0) = 0 := h1.2
        rw [dotProduct_add, hd0, hdot, zero_add] at hd1
        exact one_ne_zero hd1
    · intro hnu
      refine ⟨fun h0 => hnu h0.1, fun h1 => hnu ?_⟩
      rw [hdiff1] at h1
      have h2 := S.U.add_mem h1.1 hv0
      rw [add_assoc, zmod2_vec_add_self, add_zero] at h2
      exact h2

lemma step_sslice_single {n : ℕ} {gs : List Gate} {g : Gate} (S : SSlice n)
    (hleg : legalGates (n + 1) (gs ++ [g])) (hS : ValidSSlice gs S) :
    ∃ L : List (SSlice n),
      (∀ S' ∈ L, ValidSSlice (gs ++ [g]) S') ∧
      ∀ u : Fin n → F2,
        (u - S.p ∈ S.U → ∃! idx : Fin L.length, u - (L.get idx).p ∈ (L.get idx).U) ∧
        (u - S.p ∉ S.U → ∀ idx : Fin L.length, u - (L.get idx).p ∉ (L.get idx).U) := by
  have hpre := legalGates_prefix hleg
  have hback := hpre.2.1
  have hshape := hpre.2.2
  have hwrap1 : ∀ (S' : SSlice n), ValidSSlice (gs ++ [g]) S' → S'.U = S.U → S'.p = S.p →
      ∃ L : List (SSlice n),
        (∀ b ∈ L, ValidSSlice (gs ++ [g]) b) ∧
        ∀ u : Fin n → F2,
          (u - S.p ∈ S.U → ∃! idx : Fin L.length, u - (L.get idx).p ∈ (L.get idx).U) ∧
          (u - S.p ∉ S.U → ∀ idx : Fin L.length, u - (L.get idx).p ∉ (L.get idx).U) := by
    intro S' hS' hU hp
    refine ⟨[S'], fun b hb => by simp at hb; subst hb; exact hS', fun u => ⟨?_, ?_⟩⟩
    · intro hu
      exact ⟨⟨0, by simp⟩, by simpa [hU, hp] using hu, fun j _ => Fin.ext (by have := j.isLt; simp only [List.length_singleton] at this; change j.val = 0; omega)⟩
    · intro hnu idx
      have hi0 : idx = ⟨0, by simp⟩ := Fin.ext (by have := idx.isLt; simp only [List.length_singleton] at this; change idx.val = 0; omega)
      subst hi0; simpa [hU, hp] using hnu
  have hnl_case : ∀ (isOr : Bool) (w0 w1 : ℕ),
      (if isOr then g.op = .or else g.op = .and) → g.inputs = [w0, w1] →
      w0 < n + 1 + gs.length → w1 < n + 1 + gs.length →
      ∃ L : List (SSlice n),
        (∀ S' ∈ L, ValidSSlice (gs ++ [g]) S') ∧
        ∀ u : Fin n → F2,
          (u - S.p ∈ S.U → ∃! idx : Fin L.length, u - (L.get idx).p ∈ (L.get idx).U) ∧
          (u - S.p ∉ S.U → ∀ idx : Fin L.length, u - (L.get idx).p ∉ (L.get idx).U) := by
    intro isOr w0 w1 hop hg hw0 hw1
    have hcost1 : costGates (gs ++ [g]) = costGates gs + 1 := by
      apply costGates_snoc_one gs g
      cases isOr
      · simp at hop; exact ⟨Or.inl hop, by rw [hg]; rfl⟩
      · simp at hop; exact ⟨Or.inr hop, by rw [hg]; rfl⟩
    have heval_bin : ∀ (b1 b2 : Bool), g.op.eval [b1, b2] = if isOr then (b1 || b2) else (b1 && b2) := by
      intro b1 b2; cases isOr <;> simp at hop <;> simp [hop, GateOp.eval]
    have hsolve_on : ∀ (P : SSlice n),
        n ≤ Module.finrank F2 P.U + costGates (gs ++ [g]) →
        (∀ w < n + 1 + gs.length, ∀ v ∈ P.U,
          (wiresOf gs (bitsOf (n + 1) (Fin.cons 0 (P.p + v)))).getD w false =
            decide (dotProduct (P.slope w) v + P.off0 w = 1) ∧
          (wiresOf gs (bitsOf (n + 1) (Fin.cons 1 (P.p + v)))).getD w false =
            decide (dotProduct (P.slope w) v + P.off1 w = 1)) →
        ((∀ v ∈ P.U, dotProduct (P.slope w0) v = 0) ∧ P.off0 w0 = P.off1 w0) ∨
        ((∀ v ∈ P.U, dotProduct (P.slope w1) v = 0) ∧ P.off0 w1 = P.off1 w1) ∨
        ((∀ v ∈ P.U, dotProduct (P.slope w0 + P.slope w1) v = 0) ∧ P.off0 w0 + P.off0 w1 = P.off1 w0 + P.off1 w1) →
        ∃ (a : Fin n → F2) (c0 c1 : F2),
          ValidSSlice (gs ++ [g]) (P.upd (n + 1 + gs.length) a c0 c1) := by
      intro P hPdim hPval hcond
      have mk_upd : ∀ (a : Fin n → F2) (c0 c1 : F2),
          (∀ v ∈ P.U,
            g.op.eval (g.inputs.map fun i => (wiresOf gs (bitsOf (n + 1) (Fin.cons 0 (P.p + v)))).getD i false) =
              decide (dotProduct a v + c0 = 1) ∧
            g.op.eval (g.inputs.map fun i => (wiresOf gs (bitsOf (n + 1) (Fin.cons 1 (P.p + v)))).getD i false) =
              decide (dotProduct a v + c1 = 1)) →
          ValidSSlice (gs ++ [g]) (P.upd (n + 1 + gs.length) a c0 c1) := by
        intro a c0 c1 hnew
        refine ⟨hPdim, ?_⟩
        intro w hw v hv
        simp only [List.length_append, List.length_singleton] at hw
        dsimp only [SSlice.upd] at hv ⊢
        by_cases hweq : w = n + 1 + gs.length
        · subst hweq; simp only [↓reduceIte]
          rw [wiresOf_snoc_last_eq gs g _ (bitsOf_len (n + 1) _),
              wiresOf_snoc_last_eq gs g _ (bitsOf_len (n + 1) _)]
          exact hnew v hv
        · simp only [hweq, ↓reduceIte]
          rw [wiresOf_append_getD_lt gs [g] _ (by rw [bitsOf_len]; omega),
              wiresOf_append_getD_lt gs [g] _ (by rw [bitsOf_len]; omega)]
          exact hPval w (by omega) v hv
      rcases hcond with ⟨h0, he0⟩ | ⟨h1, he1⟩ | ⟨h01, he01⟩
      · rcases zmod2_cases (P.off0 w0) with hc | hc
        · cases isOr
          · refine ⟨0, 0, 0, mk_upd 0 0 0 fun v hv => ?_⟩
            rw [hg]; simp only [List.map_cons, List.map_nil, heval_bin, Bool.false_eq_true, ↓reduceIte]
            rw [(hPval w0 hw0 v hv).1, (hPval w0 hw0 v hv).2, h0 v hv, ← he0, hc]; simp
          · refine ⟨P.slope w1, P.off0 w1, P.off1 w1, mk_upd _ _ _ fun v hv => ?_⟩
            rw [hg]; simp only [List.map_cons, List.map_nil, heval_bin, ↓reduceIte]
            rw [(hPval w0 hw0 v hv).1, (hPval w0 hw0 v hv).2, (hPval w1 hw1 v hv).1, (hPval w1 hw1 v hv).2,
                h0 v hv, ← he0, hc]; simp
        · cases isOr
          · refine ⟨P.slope w1, P.off0 w1, P.off1 w1, mk_upd _ _ _ fun v hv => ?_⟩
            rw [hg]; simp only [List.map_cons, List.map_nil, heval_bin, Bool.false_eq_true, ↓reduceIte]
            rw [(hPval w0 hw0 v hv).1, (hPval w0 hw0 v hv).2, (hPval w1 hw1 v hv).1, (hPval w1 hw1 v hv).2,
                h0 v hv, ← he0, hc]; simp
          · refine ⟨0, 1, 1, mk_upd 0 1 1 fun v hv => ?_⟩
            rw [hg]; simp only [List.map_cons, List.map_nil, heval_bin, ↓reduceIte]
            rw [(hPval w0 hw0 v hv).1, (hPval w0 hw0 v hv).2, h0 v hv, ← he0, hc]; simp
      · rcases zmod2_cases (P.off0 w1) with hc | hc
        · cases isOr
          · refine ⟨0, 0, 0, mk_upd 0 0 0 fun v hv => ?_⟩
            rw [hg]; simp only [List.map_cons, List.map_nil, heval_bin, Bool.false_eq_true, ↓reduceIte]
            rw [(hPval w1 hw1 v hv).1, (hPval w1 hw1 v hv).2, h1 v hv, ← he1, hc]; simp
          · refine ⟨P.slope w0, P.off0 w0, P.off1 w0, mk_upd _ _ _ fun v hv => ?_⟩
            rw [hg]; simp only [List.map_cons, List.map_nil, heval_bin, ↓reduceIte]
            rw [(hPval w0 hw0 v hv).1, (hPval w0 hw0 v hv).2, (hPval w1 hw1 v hv).1, (hPval w1 hw1 v hv).2,
                h1 v hv, ← he1, hc]; simp
        · cases isOr
          · refine ⟨P.slope w0, P.off0 w0, P.off1 w0, mk_upd _ _ _ fun v hv => ?_⟩
            rw [hg]; simp only [List.map_cons, List.map_nil, heval_bin, Bool.false_eq_true, ↓reduceIte]
            rw [(hPval w0 hw0 v hv).1, (hPval w0 hw0 v hv).2, (hPval w1 hw1 v hv).1, (hPval w1 hw1 v hv).2,
                h1 v hv, ← he1, hc]; simp
          · refine ⟨0, 1, 1, mk_upd 0 1 1 fun v hv => ?_⟩
            rw [hg]; simp only [List.map_cons, List.map_nil, heval_bin, ↓reduceIte]
            rw [(hPval w1 hw1 v hv).1, (hPval w1 hw1 v hv).2, h1 v hv, ← he1, hc]; simp
      · have hrel0 : ∀ v ∈ P.U, dotProduct (P.slope w1) v + P.off0 w1 =
            dotProduct (P.slope w0) v + P.off0 w0 + (P.off0 w0 + P.off0 w1) := by
          intro v hv
          have hs := h01 v hv; rw [add_dotProduct] at hs
          have h1 := z2_add_self (dotProduct (P.slope w0) v)
          have h2 := z2_add_self (P.off0 w0)
          linear_combination hs - h1 - h2
        have hrel1 : ∀ v ∈ P.U, dotProduct (P.slope w1) v + P.off1 w1 =
            dotProduct (P.slope w0) v + P.off1 w0 + (P.off0 w0 + P.off0 w1) := by
          intro v hv
          have hs := h01 v hv; rw [add_dotProduct] at hs
          have h1 := z2_add_self (dotProduct (P.slope w0) v)
          have h2 := z2_add_self (P.off1 w0)
          linear_combination hs - he01 - h1 - h2
        rcases zmod2_cases (P.off0 w0 + P.off0 w1) with hgam | hgam
        · refine ⟨P.slope w0, P.off0 w0, P.off1 w0, mk_upd _ _ _ fun v hv => ?_⟩
          rw [hg]; simp only [List.map_cons, List.map_nil, heval_bin]
          rw [(hPval w0 hw0 v hv).1, (hPval w0 hw0 v hv).2, (hPval w1 hw1 v hv).1, (hPval w1 hw1 v hv).2,
              hrel0 v hv, hrel1 v hv, hgam, add_zero]
          cases isOr <;> simp
        · cases isOr
          · refine ⟨0, 0, 0, mk_upd 0 0 0 fun v hv => ?_⟩
            rw [hg]; simp only [List.map_cons, List.map_nil, heval_bin, Bool.false_eq_true, ↓reduceIte]
            rw [(hPval w0 hw0 v hv).1, (hPval w0 hw0 v hv).2, (hPval w1 hw1 v hv).1, (hPval w1 hw1 v hv).2,
                hrel0 v hv, hrel1 v hv, hgam]
            constructor
            · rcases zmod2_cases (dotProduct (P.slope w0) v + P.off0 w0) with h | h <;> rw [h] <;> simp only [zero_dotProduct, zero_add] <;> decide
            · rcases zmod2_cases (dotProduct (P.slope w0) v + P.off1 w0) with h | h <;> rw [h] <;> simp only [zero_dotProduct, zero_add] <;> decide
          · refine ⟨0, 1, 1, mk_upd 0 1 1 fun v hv => ?_⟩
            rw [hg]; simp only [List.map_cons, List.map_nil, heval_bin, ↓reduceIte]
            rw [(hPval w0 hw0 v hv).1, (hPval w0 hw0 v hv).2, (hPval w1 hw1 v hv).1, (hPval w1 hw1 v hv).2,
                hrel0 v hv, hrel1 v hv, hgam]
            constructor
            · rcases zmod2_cases (dotProduct (P.slope w0) v + P.off0 w0) with h | h <;> rw [h] <;> simp only [zero_dotProduct, zero_add] <;> decide
            · rcases zmod2_cases (dotProduct (P.slope w0) v + P.off1 w0) with h | h <;> rw [h] <;> simp only [zero_dotProduct, zero_add] <;> decide
    have hsplit_and_solve : ∀ (a : Fin n → F2),
        ((a = S.slope w0 ∧ S.off0 w0 = S.off1 w0) ∨
         (a = S.slope w1 ∧ S.off0 w1 = S.off1 w1) ∨
         (a = S.slope w0 + S.slope w1 ∧ S.off0 w0 + S.off0 w1 = S.off1 w0 + S.off1 w1)) →
        ∃ L : List (SSlice n),
          (∀ S' ∈ L, ValidSSlice (gs ++ [g]) S') ∧
          ∀ u : Fin n → F2,
            (u - S.p ∈ S.U → ∃! idx : Fin L.length, u - (L.get idx).p ∈ (L.get idx).U) ∧
            (u - S.p ∉ S.U → ∀ idx : Fin L.length, u - (L.get idx).p ∉ (L.get idx).U) := by
      intro a ha_spec
      by_cases hvan : ∀ v ∈ S.U, dotProduct a v = 0
      · have hcond : ((∀ v ∈ S.U, dotProduct (S.slope w0) v = 0) ∧ S.off0 w0 = S.off1 w0) ∨
            ((∀ v ∈ S.U, dotProduct (S.slope w1) v = 0) ∧ S.off0 w1 = S.off1 w1) ∨
            ((∀ v ∈ S.U, dotProduct (S.slope w0 + S.slope w1) v = 0) ∧ S.off0 w0 + S.off0 w1 = S.off1 w0 + S.off1 w1) := by
          rcases ha_spec with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
          · exact Or.inl ⟨hvan, h⟩
          · exact Or.inr (Or.inl ⟨hvan, h⟩)
          · exact Or.inr (Or.inr ⟨hvan, h⟩)
        obtain ⟨a', c0', c1', hv'⟩ := hsolve_on S (by have := hS.1; omega) hS.2 hcond
        exact hwrap1 _ hv' rfl rfl
      · push Not at hvan
        rcases hvan with ⟨v0, hv0, hne⟩
        have hdot : dotProduct a v0 = 1 := by
          rcases zmod2_cases (dotProduct a v0) with h | h
          · exact absurd h hne
          · exact h
        have hsp := S.split_spec hS a v0 hv0 hdot
        set S0 := S.split0 a
        set S1 := S.split1 a v0
        have hdim0 : n ≤ Module.finrank F2 S0.U + costGates (gs ++ [g]) := by
          have := hS.1; have := hsp.1; omega
        have hdim1 : n ≤ Module.finrank F2 S1.U + costGates (gs ++ [g]) := by
          have := hS.1; have := hsp.2.1; omega
        have hcond0 : ((∀ v ∈ S0.U, dotProduct (S0.slope w0) v = 0) ∧ S0.off0 w0 = S0.off1 w0) ∨
            ((∀ v ∈ S0.U, dotProduct (S0.slope w1) v = 0) ∧ S0.off0 w1 = S0.off1 w1) ∨
            ((∀ v ∈ S0.U, dotProduct (S0.slope w0 + S0.slope w1) v = 0) ∧ S0.off0 w0 + S0.off0 w1 = S0.off1 w0 + S0.off1 w1) := by
          rcases ha_spec with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
          · exact Or.inl ⟨fun v hv => hv.2, h⟩
          · exact Or.inr (Or.inl ⟨fun v hv => hv.2, h⟩)
          · exact Or.inr (Or.inr ⟨fun v hv => hv.2, h⟩)
        have hcond1 : ((∀ v ∈ S1.U, dotProduct (S1.slope w0) v = 0) ∧ S1.off0 w0 = S1.off1 w0) ∨
            ((∀ v ∈ S1.U, dotProduct (S1.slope w1) v = 0) ∧ S1.off0 w1 = S1.off1 w1) ∨
            ((∀ v ∈ S1.U, dotProduct (S1.slope w0 + S1.slope w1) v = 0) ∧ S1.off0 w0 + S1.off0 w1 = S1.off1 w0 + S1.off1 w1) := by
          rcases ha_spec with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
          · exact Or.inl ⟨fun v hv => hv.2, by dsimp only [S1, SSlice.split1]; rw [h]⟩
          · exact Or.inr (Or.inl ⟨fun v hv => hv.2, by dsimp only [S1, SSlice.split1]; rw [h]⟩)
          · refine Or.inr (Or.inr ⟨fun v hv => hv.2, ?_⟩)
            dsimp only [S1, SSlice.split1]
            linear_combination h
        obtain ⟨a0', c00, c01, hv0'⟩ := hsolve_on S0 hdim0 hsp.2.2.1 hcond0
        obtain ⟨a1', c10, c11, hv1'⟩ := hsolve_on S1 hdim1 hsp.2.2.2.1 hcond1
        let P0 := S0.upd (n + 1 + gs.length) a0' c00 c01
        let P1 := S1.upd (n + 1 + gs.length) a1' c10 c11
        refine ⟨[P0, P1], fun b hb => by simp at hb; rcases hb with rfl | rfl; exact hv0'; exact hv1', fun u => ⟨?_, ?_⟩⟩
        · intro hu
          have ⟨hor, hdisj⟩ := (hsp.2.2.2.2 u).1 hu
          rcases hor with h0 | h1
          · refine ⟨⟨0, by simp⟩, h0, fun idx hidx => ?_⟩
            have hlt : idx.val < 2 := idx.isLt
            interval_cases hv : idx.val
            · exact Fin.ext hv
            · exfalso; exact hdisj ⟨h0, by simpa [hv, P1, SSlice.upd] using hidx⟩
          · refine ⟨⟨1, by simp⟩, h1, fun idx hidx => ?_⟩
            have hlt : idx.val < 2 := idx.isLt
            interval_cases hv : idx.val
            · exfalso; exact hdisj ⟨by simpa [hv, P0, SSlice.upd] using hidx, h1⟩
            · exact Fin.ext hv
        · intro hnu idx hidx
          have ⟨hn0, hn1⟩ := (hsp.2.2.2.2 u).2 hnu
          have hlt : idx.val < 2 := idx.isLt
          interval_cases hv : idx.val
          · exact hn0 (by simpa [hv, P0, SSlice.upd] using hidx)
          · exact hn1 (by simpa [hv, P1, SSlice.upd] using hidx)
    by_cases he0 : S.off0 w0 = S.off1 w0
    · exact hsplit_and_solve (S.slope w0) (Or.inl ⟨rfl, he0⟩)
    · by_cases he1 : S.off0 w1 = S.off1 w1
      · exact hsplit_and_solve (S.slope w1) (Or.inr (Or.inl ⟨rfl, he1⟩))
      · have hne2 : ∀ a b c d : F2, a ≠ b → c ≠ d → a + c = b + d := fun a b c d h1 h2 => by
          rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
            rcases zmod2_cases c with rfl | rfl <;> rcases zmod2_cases d with rfl | rfl <;>
            first | exact absurd rfl h1 | exact absurd rfl h2 | decide
        have he01 : S.off0 w0 + S.off0 w1 = S.off1 w0 + S.off1 w1 := hne2 _ _ _ _ he0 he1
        exact hsplit_and_solve (S.slope w0 + S.slope w1) (Or.inr (Or.inr ⟨rfl, he01⟩))
  rcases hshape.2 with hop | hop | hop | ⟨hop, hlen1⟩
  · rcases hg : g.inputs with _ | ⟨w0, rest⟩
    · exact hwrap1 _ (S.valid_upd hS 0 1 1 fun v _ => by rw [hop, hg]; simp [GateOp.eval]) rfl rfl
    · rcases rest with _ | ⟨w1, rest2⟩
      · have hw0 := hback w0 (by rw [hg]; simp)
        refine hwrap1 _ (S.valid_upd hS (S.slope w0) (S.off0 w0) (S.off1 w0) fun v hv => ?_) rfl rfl
        rw [hop, hg]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        exact hS.2 w0 hw0 v hv
      · rcases rest2 with _ | ⟨_, _⟩
        · exact hnl_case false w0 w1 (by simpa using hop) hg (hback w0 (by rw [hg]; simp)) (hback w1 (by rw [hg]; simp))
        · exfalso; have := hshape.1; rw [hg] at this; simp at this
  · rcases hg : g.inputs with _ | ⟨w0, rest⟩
    · exact hwrap1 _ (S.valid_upd hS 0 0 0 fun v _ => by rw [hop, hg]; simp [GateOp.eval]) rfl rfl
    · rcases rest with _ | ⟨w1, rest2⟩
      · have hw0 := hback w0 (by rw [hg]; simp)
        refine hwrap1 _ (S.valid_upd hS (S.slope w0) (S.off0 w0) (S.off1 w0) fun v hv => ?_) rfl rfl
        rw [hop, hg]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        exact hS.2 w0 hw0 v hv
      · rcases rest2 with _ | ⟨_, _⟩
        · exact hnl_case true w0 w1 (by simpa using hop) hg (hback w0 (by rw [hg]; simp)) (hback w1 (by rw [hg]; simp))
        · exfalso; have := hshape.1; rw [hg] at this; simp at this
  · rcases hg : g.inputs with _ | ⟨w0, rest⟩
    · exact hwrap1 _ (S.valid_upd hS 0 1 1 fun v _ => by rw [hop, hg]; simp [GateOp.eval]) rfl rfl
    · rcases rest with _ | ⟨w1, rest2⟩
      · have hw0 := hback w0 (by rw [hg]; simp)
        refine hwrap1 _ (S.valid_upd hS (S.slope w0) (S.off0 w0 + 1) (S.off1 w0 + 1) fun v hv => ?_) rfl rfl
        rw [hop, hg]; simp only [List.map_cons, List.map_nil, GateOp.eval, (hS.2 w0 hw0 v hv).1, (hS.2 w0 hw0 v hv).2]
        constructor
        · rcases zmod2_cases (dotProduct (S.slope w0) v + S.off0 w0) with h | h <;> rw [← add_assoc, h] <;> decide
        · rcases zmod2_cases (dotProduct (S.slope w0) v + S.off1 w0) with h | h <;> rw [← add_assoc, h] <;> decide
      · rcases rest2 with _ | ⟨_, _⟩
        · have hw0 := hback w0 (by rw [hg]; simp)
          have hw1 := hback w1 (by rw [hg]; simp)
          refine hwrap1 _ (S.valid_upd hS (S.slope w0 + S.slope w1) (S.off0 w0 + S.off0 w1 + 1)
            (S.off1 w0 + S.off1 w1 + 1) fun v hv => ?_) rfl rfl
          rw [hop, hg]
          simp only [List.map_cons, List.map_nil, GateOp.eval, (hS.2 w0 hw0 v hv).1, (hS.2 w0 hw0 v hv).2,
            (hS.2 w1 hw1 v hv).1, (hS.2 w1 hw1 v hv).2, add_dotProduct]
          constructor
          · have hrw : dotProduct (S.slope w0) v + dotProduct (S.slope w1) v + (S.off0 w0 + S.off0 w1 + 1) =
                (dotProduct (S.slope w0) v + S.off0 w0) + (dotProduct (S.slope w1) v + S.off0 w1) + 1 := by ring
            rw [hrw]
            rcases zmod2_cases (dotProduct (S.slope w0) v + S.off0 w0) with h0 | h0 <;>
              rcases zmod2_cases (dotProduct (S.slope w1) v + S.off0 w1) with h1 | h1 <;> rw [h0, h1] <;> decide
          · have hrw : dotProduct (S.slope w0) v + dotProduct (S.slope w1) v + (S.off1 w0 + S.off1 w1 + 1) =
                (dotProduct (S.slope w0) v + S.off1 w0) + (dotProduct (S.slope w1) v + S.off1 w1) + 1 := by ring
            rw [hrw]
            rcases zmod2_cases (dotProduct (S.slope w0) v + S.off1 w0) with h0 | h0 <;>
              rcases zmod2_cases (dotProduct (S.slope w1) v + S.off1 w1) with h1 | h1 <;> rw [h0, h1] <;> decide
        · exfalso; have := hshape.1; rw [hg] at this; simp at this
  · rcases hg : g.inputs with _ | ⟨w0, rest⟩
    · simp [hg] at hlen1
    · rcases rest with _ | ⟨_, _⟩
      · have hw0 := hback w0 (by rw [hg]; simp)
        refine hwrap1 _ (S.valid_upd hS (S.slope w0) (S.off0 w0 + 1) (S.off1 w0 + 1) fun v hv => ?_) rfl rfl
        rw [hop, hg]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons,
          (hS.2 w0 hw0 v hv).1, (hS.2 w0 hw0 v hv).2]
        constructor
        · rcases zmod2_cases (dotProduct (S.slope w0) v + S.off0 w0) with h | h <;> rw [← add_assoc, h] <;> decide
        · rcases zmod2_cases (dotProduct (S.slope w0) v + S.off1 w0) with h | h <;> rw [← add_assoc, h] <;> decide
      · simp [hg] at hlen1

lemma build_sslice_list (n : ℕ) (gs : List Gate) (hleg : legalGates (n + 1) gs) :
    ∃ L : List (SSlice n),
      (∀ S ∈ L, ValidSSlice gs S) ∧
      ∀ u : Fin n → F2, ∃! idx : Fin L.length, u - (L.get idx).p ∈ (L.get idx).U := by
  induction gs using List.reverseRecOn with
  | nil =>
    let S0 : SSlice n :=
      { U := ⊤
        p := 0
        slope := fun w => if hw : 1 ≤ w ∧ w < n + 1 then Pi.single ⟨w - 1, by omega⟩ 1 else 0
        off0 := fun _ => 0
        off1 := fun w => if w = 0 then 1 else 0 }
    have hval0 : ValidSSlice [] S0 := by
      refine ⟨by simp [S0], ?_⟩
      intro w hw v _
      simp only [List.length_nil, Nat.add_zero] at hw
      dsimp only [S0]
      rw [zero_add]
      change (bitsOf (n + 1) (Fin.cons 0 v)).getD (⟨w, hw⟩ : Fin (n + 1)).val false = _ ∧
             (bitsOf (n + 1) (Fin.cons 1 v)).getD (⟨w, hw⟩ : Fin (n + 1)).val false = _
      rw [bitsOf_getD, bitsOf_getD]
      cases w with
      | zero => simp
      | succ j =>
        have hj : j < n := by omega
        have hcond : 1 ≤ j + 1 ∧ j + 1 < n + 1 := ⟨by omega, hw⟩
        have heq : (⟨j + 1, hw⟩ : Fin (n + 1)) = (⟨j, hj⟩ : Fin n).succ := Fin.ext rfl
        rw [heq, Fin.cons_succ, Fin.cons_succ]
        constructor <;> apply congrArg (fun x => decide (x = 1))
        · rw [dif_pos hcond]; simp [single_dotProduct]
        · rw [dif_pos hcond]; simp [single_dotProduct]
    refine ⟨[S0], fun b hb => by simp at hb; subst hb; exact hval0, fun u => ?_⟩
    exact ⟨⟨0, by simp⟩, by simp [S0], fun idx _ => Fin.ext (by have := idx.isLt; simp only [List.length_singleton] at this; change idx.val = 0; omega)⟩
  | append_singleton gs g ih =>
    have hpre := legalGates_prefix hleg
    rcases ih hpre.1 with ⟨L, hLval, hLpart⟩
    have hstep_all : ∀ idx : Fin L.length, ∃ Lc : List (SSlice n),
        (∀ S' ∈ Lc, ValidSSlice (gs ++ [g]) S') ∧
        ∀ u : Fin n → F2,
          (u - (L.get idx).p ∈ (L.get idx).U → ∃! j : Fin Lc.length, u - (Lc.get j).p ∈ (Lc.get j).U) ∧
          (u - (L.get idx).p ∉ (L.get idx).U → ∀ j : Fin Lc.length, u - (Lc.get j).p ∉ (Lc.get j).U) :=
      fun idx => step_sslice_single (L.get idx) hleg (hLval _ (List.get_mem L idx))
    let children : Fin L.length → List (SSlice n) := fun idx => (hstep_all idx).choose
    have hchildren_spec : ∀ idx : Fin L.length,
        (∀ S' ∈ children idx, ValidSSlice (gs ++ [g]) S') ∧
        ∀ u : Fin n → F2,
          (u - (L.get idx).p ∈ (L.get idx).U → ∃! j : Fin (children idx).length, u - ((children idx).get j).p ∈ ((children idx).get j).U) ∧
          (u - (L.get idx).p ∉ (L.get idx).U → ∀ j : Fin (children idx).length, u - ((children idx).get j).p ∉ ((children idx).get j).U) :=
      fun idx => (hstep_all idx).choose_spec
    let L' : List (SSlice n) := (List.finRange L.length).flatMap children
    refine ⟨L', ?_, ?_⟩
    · intro S' hS'
      rcases List.mem_flatMap.mp hS' with ⟨idx, _, hmem⟩
      exact (hchildren_spec idx).1 S' hmem
    · intro u
      have hflat_bij : ∀ (ms : List (Fin L.length)), ms.Nodup →
          ∀ (p : SSlice n → Prop),
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
            · dsimp only; rw [List.get_eq_getElem, List.getElem_append_left j0.isLt]; exact hj0
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
                have hmem_b := List.get_mem (ms.flatMap children) ⟨q.val - (children idx).length, hqr⟩
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
                apply Fin.ext
                have := congrArg Fin.val heq
                dsimp at this ⊢; omega
      rcases hLpart u with ⟨idx0, hidx0, hidx0u⟩
      apply hflat_bij (List.finRange L.length) (List.nodup_finRange L.length) (fun S => u - S.p ∈ S.U)
      refine ⟨idx0, List.mem_finRange idx0, ((hchildren_spec idx0).2 u).1 hidx0, ?_⟩
      intro idx2 _ hne2
      exact ((hchildren_spec idx2).2 u).2 (fun hm => hne2 (hidx0u idx2 hm))

lemma rank_add_ker_mat {n : ℕ} (M : Matrix (Fin n) (Fin n) F2) :
    M.rank + Module.finrank F2 (LinearMap.ker M.mulVecLin) = n := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fin_fun] at h
  exact h

lemma polar_symm_mat {n : ℕ} (d : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hd : ∀ u v, d (u + v) + d u + d v + d 0 = dotProduct u (M.mulVec v)) (u v : Fin n → F2) :
    dotProduct u (M.mulVec v) = dotProduct v (M.mulVec u) := by
  rw [← hd u v, ← hd v u, add_comm u v]; ring

lemma polar_self_mat {n : ℕ} (d : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hd : ∀ u v, d (u + v) + d u + d v + d 0 = dotProduct u (M.mulVec v)) (u : Fin n → F2) :
    dotProduct u (M.mulVec u) = 0 := by
  have h := hd u u
  rw [zmod2_vec_add_self] at h
  have h1 : d 0 + d u + d u + d 0 = 0 := by
    have hz1 := z2_add_self (d 0); have hz2 := z2_add_self (d u); linear_combination hz1 + hz2
  rw [h1] at h; exact h.symm

lemma quad_subspace_bias_le {n r : ℕ} (d : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hrk : M.rank = 2 * r)
    (hd : ∀ u v, d (u + v) + d u + d v + d 0 = dotProduct u (M.mulVec v))
    (U : Submodule F2 (Fin n → F2)) (p lin : Fin n → F2) (c : F2) :
    (∑ v : U, signBool (decide (d (p + v.val) + dotProduct lin v.val + c = 1))).natAbs ≤ 2 ^ (n - r) := by
  have h2r_le_n : 2 * r ≤ n := by have := rank_add_ker_mat M; omega
  let h : U → F2 := fun v => d (p + v.val) + dotProduct lin v.val + c
  have hbil : ∀ v w : U, h (v + w) + h v + h w + h 0 = dotProduct v.val (M.mulVec w.val) := by
    intro v w
    dsimp only [h]
    have hlin : dotProduct lin (v.val + w.val) + dotProduct lin v.val + dotProduct lin w.val + dotProduct lin 0 = 0 := by
      rw [dotProduct_add, dotProduct_zero, add_zero]
      have hz1 := z2_add_self (dotProduct lin v.val); have hz2 := z2_add_self (dotProduct lin w.val)
      linear_combination hz1 + hz2
    have hc4 : c + c + c + c = 0 := by have hz := z2_add_self c; linear_combination hz + hz
    have hdp : d (p + (v.val + w.val)) + d (p + v.val) + d (p + w.val) + d (p + 0) =
        dotProduct v.val (M.mulVec w.val) := by
      have e1 := hd p (v.val + w.val)
      have e2 := hd p v.val
      have e3 := hd p w.val
      have e4 := hd v.val w.val
      rw [Matrix.mulVec_add, dotProduct_add] at e1
      have hz1 := z2_add_self (d p)
      have hz2 := z2_add_self (d (v.val + w.val))
      have hz3 := z2_add_self (d v.val)
      have hz4 := z2_add_self (d w.val)
      have hz5 := z2_add_self (d 0)
      have hz6 := z2_add_self (dotProduct p (M.mulVec v.val))
      have hz7 := z2_add_self (dotProduct p (M.mulVec w.val))
      rw [add_zero]
      linear_combination e1 + e2 + e3 + e4 - hz1 - hz2 - hz3 - hz4 - hz5 - hz5 + hz6 + hz7
    change d (p + (v.val + w.val)) + dotProduct lin (v.val + w.val) + c +
      (d (p + v.val) + dotProduct lin v.val + c) +
      (d (p + w.val) + dotProduct lin w.val + c) +
      (d (p + 0) + dotProduct lin 0 + c) = dotProduct v.val (M.mulVec w.val)
    linear_combination hdp + hlin + hc4
  let KU : Submodule F2 (Fin n → F2) :=
    U ⊓ ({ carrier := {w | ∀ v ∈ U, dotProduct v (M.mulVec w) = 0}
           zero_mem' := fun v _ => by simp
           smul_mem' := fun a {w} hw v hv => (by rw [Matrix.mulVec_smul, dotProduct_smul, hw v hv, smul_zero]), add_mem' := fun {w1 w2} h1 h2 v hv => (by rw [Matrix.mulVec_add, dotProduct_add, h1 v hv, h2 v hv, add_zero]) } : Submodule F2 (Fin n → F2))
  have hdim_sum : Module.finrank F2 U + Module.finrank F2 KU ≤ 2 * (n - r) := by
    let T : KU →ₗ[F2] orthoComp U :=
      { toFun := fun w => ⟨M.mulVec w.val, fun v hv => by rw [dotProduct_comm]; exact w.property.2 v hv⟩
        map_add' := fun x y => Subtype.ext (Matrix.mulVec_add M x.val y.val)
        map_smul' := fun a x => Subtype.ext (Matrix.mulVec_smul M a x.val) }
    have hrkT := LinearMap.finrank_range_add_finrank_ker T
    have hran : Module.finrank F2 (LinearMap.range T) ≤ Module.finrank F2 (orthoComp U) :=
      Submodule.finrank_le _
    let embKer : LinearMap.ker T →ₗ[F2] LinearMap.ker M.mulVecLin :=
      { toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hemb_inj : Function.Injective embKer := fun x y hxy => by
      have h : (embKer x).val = (embKer y).val := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
    have hker_le : Module.finrank F2 (LinearMap.ker T) ≤ Module.finrank F2 (LinearMap.ker M.mulVecLin) :=
      LinearMap.finrank_le_finrank_of_injective hemb_inj
    have horth := finrank_orthoComp U
    have hMrk := rank_add_ker_mat M
    omega
  set S := ∑ v : U, signBool (decide (h v = 1))
  have hsq : S * S = ∑ w : U, signBool (decide (h w + h 0 = 1)) *
      ∑ v : U, signBool (decide (dotProduct (M.mulVec w.val) v.val = 1)) := by
    calc S * S = ∑ v : U, ∑ v' : U, signBool (decide (h v' = 1)) * signBool (decide (h v = 1)) := by
          simp only [S, Finset.sum_mul, Finset.mul_sum]
      _ = ∑ v : U, ∑ w : U, signBool (decide (h (v + w) = 1)) * signBool (decide (h v = 1)) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          let e : U ≃ U :=
            { toFun := fun w => v + w
              invFun := fun w => v + w
              left_inv := fun w => Subtype.ext (by show v.val + (v.val + w.val) = w.val; rw [← add_assoc, zmod2_vec_add_self, zero_add])
              right_inv := fun w => Subtype.ext (by show v.val + (v.val + w.val) = w.val; rw [← add_assoc, zmod2_vec_add_self, zero_add]) }
          exact (Equiv.sum_comp e (fun v' => signBool (decide (h v' = 1)) * signBool (decide (h v = 1)))).symm
      _ = ∑ w : U, ∑ v : U, signBool (decide (h (v + w) + h v = 1)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
          exact (by rw [zmod2_add_decide (h (v + w)) (h v), signBool_xor] : signBool (decide (h (v + w) + h v = 1)) = _).symm
      _ = ∑ w : U, signBool (decide (h w + h 0 = 1)) *
            ∑ v : U, signBool (decide (dotProduct (M.mulVec w.val) v.val = 1)) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          have h1 : h (v + w) + h v = (h w + h 0) + dotProduct (M.mulVec w.val) v.val := by
            have hb := hbil v w
            rw [dotProduct_comm] at hb
            have hz1 := z2_add_self (h w); have hz2 := z2_add_self (h 0)
            linear_combination hb - hz1 - hz2
          rw [h1, zmod2_add_decide, signBool_xor]
  have hsq_le : (S.natAbs : ℤ) ^ 2 ≤ (2 : ℤ) ^ Module.finrank F2 U * (2 : ℤ) ^ Module.finrank F2 KU := by
    have h1 : (S.natAbs : ℤ) ^ 2 = S * S := by rw [sq, ← Nat.cast_mul, Int.natAbs_mul_self]
    rw [h1, hsq]
    simp_rw [sum_sign_dot_submodule U]
    have htri := Finset.abs_sum_le_sum_abs
      (fun w : U => signBool (decide (h w + h 0 = 1)) *
        if M.mulVec w.val ∈ orthoComp U then (2 : ℤ) ^ Module.finrank F2 U else 0) Finset.univ
    refine le_trans (le_trans (le_abs_self _) htri) ?_
    have habs : ∀ w : U,
        |signBool (decide (h w + h 0 = 1)) * if M.mulVec w.val ∈ orthoComp U then (2 : ℤ) ^ Module.finrank F2 U else 0| =
        if M.mulVec w.val ∈ orthoComp U then (2 : ℤ) ^ Module.finrank F2 U else 0 := by
      intro w; rw [abs_mul, signBool_abs_one, one_mul]
      split_ifs
      · exact abs_of_nonneg (by positivity)
      · simp
    simp_rw [habs, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter (fun w : U => M.mulVec w.val ∈ orthoComp U)).card =
        2 ^ Module.finrank F2 KU := by
      let eK : KU ≃ {w : U // M.mulVec w.val ∈ orthoComp U} :=
        { toFun := fun w => ⟨⟨w.val, w.property.1⟩, fun v hv => by rw [dotProduct_comm]; exact w.property.2 v hv⟩
          invFun := fun w => ⟨w.val.val, ⟨w.val.property, fun v hv => by rw [dotProduct_comm]; exact w.property v hv⟩⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [← Fintype.card_subtype, ← Fintype.card_congr eK, card_submodule_zmod2]
    rw [hcard, mul_comm]; push_cast; rfl
  have hnat : S.natAbs ^ 2 ≤ (2 ^ (n - r)) ^ 2 := by
    have h2 : (2 : ℤ) ^ Module.finrank F2 U * (2 : ℤ) ^ Module.finrank F2 KU ≤ ((2 ^ (n - r) : ℕ) : ℤ) ^ 2 := by
      rw [← pow_add]
      have : ((2 ^ (n - r) : ℕ) : ℤ) ^ 2 = (2 : ℤ) ^ (2 * (n - r)) := by push_cast; rw [← pow_mul, mul_comm]
      rw [this]
      exact pow_le_pow_right₀ (by norm_num) hdim_sum
    exact_mod_cast le_trans hsq_le h2
  by_contra hlt; push Not at hlt
  have : (2 ^ (n - r)) ^ 2 < S.natAbs ^ 2 := Nat.pow_lt_pow_left hlt (by omega)
  omega

lemma full_slice_atom_bound (n r c : ℕ) (Q : Bool → (Fin n → F2) → F2)
    (M : Matrix (Fin n) (Fin n) F2) (hrk : M.rank = 2 * r)
    (hd : ∀ u v, (Q false (u + v) + Q true (u + v)) + (Q false u + Q true u) +
      (Q false v + Q true v) + (Q false 0 + Q true 0) = dotProduct u (M.mulVec v))
    (D : Circuit) (tap : Fin (n + 1) → ℕ)
    (hleg : legalGates (n + 1) D.gates) (hcost : costGates D.gates ≤ c)
    (hout : D.output < n + 1 + D.gates.length) (htap : ∀ j, tap j < n + 1 + D.gates.length) :
    let pos := fun (y : Fin (n + 1) → F2) (j : Fin (n + 1)) =>
      if (D.wires (bitsOf (n + 1) y)).getD (tap j) false then (1 : F2) else 0
    let S := fun t : Bool =>
      ∑ u : Fin n → F2,
        let y : Fin (n + 1) → F2 := Fin.cons (if t then 1 else 0) u
        signBool (Bool.xor (D.eval (bitsOf (n + 1) y)) (decide (dotProduct (pos y) y = 1))) *
          signBool (decide (Q t u = 1))
    |(S false : ℚ)| / 2 ^ n + |(S true : ℚ)| / 2 ^ n ≤ 1 + 1 / (2 : ℚ) ^ (r - c) := by
  intro pos S
  let f0 : (Fin n → F2) → Bool := fun u =>
    let y : Fin (n + 1) → F2 := Fin.cons 0 u
    Bool.xor (D.eval (bitsOf (n + 1) y)) (decide (dotProduct (pos y) y = 1))
  let f1 : (Fin n → F2) → Bool := fun u =>
    let y : Fin (n + 1) → F2 := Fin.cons 1 u
    Bool.xor (D.eval (bitsOf (n + 1) y)) (decide (dotProduct (pos y) y = 1))
  let eps0 : (Fin n → F2) → ℤ := fun u => signBool (f0 u) * signBool (decide (Q false u = 1))
  let eps1 : (Fin n → F2) → ℤ := fun u => signBool (f1 u) * signBool (decide (Q true u = 1))
  have hS0 : S false = ∑ u : Fin n → F2, eps0 u := rfl
  have hS1 : S true = ∑ u : Fin n → F2, eps1 u := rfl
  have hpair_le : ∀ (σ0 σ1 : ℤ), (σ0 = 1 ∨ σ0 = -1) → (σ1 = 1 ∨ σ1 = -1) →
      σ0 * S false + σ1 * S true ≤
        (2 : ℤ) ^ n + σ0 * σ1 * ∑ u : Fin n → F2, eps0 u * eps1 u := by
    intro σ0 σ1 hσ0 hσ1
    rw [hS0, hS1, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    have hcard : (2 : ℤ) ^ n = ∑ _u : Fin n → F2, (1 : ℤ) := by simp [ZMod.card]
    rw [hcard, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun u _ => ?_
    have he0 : eps0 u = 1 ∨ eps0 u = -1 := by
      dsimp only [eps0]; cases f0 u <;> cases decide (Q false u = 1) <;> simp [signBool]
    have he1 : eps1 u = 1 ∨ eps1 u = -1 := by
      dsimp only [eps1]; cases f1 u <;> cases decide (Q true u = 1) <;> simp [signBool]
    rcases hσ0 with rfl | rfl <;> rcases hσ1 with rfl | rfl <;>
      rcases he0 with h0 | h0 <;> rcases he1 with h1 | h1 <;> rw [h0, h1] <;> omega
  have habs_le : (S false).natAbs + (S true).natAbs ≤
      2 ^ n + (∑ u : Fin n → F2, eps0 u * eps1 u).natAbs := by
    have hcomb : |(S false : ℤ)| + |(S true : ℤ)| ≤ (2 : ℤ) ^ n + |∑ u : Fin n → F2, eps0 u * eps1 u| := by
      rcases abs_cases (S false) with ⟨h0, _⟩ | ⟨h0, _⟩ <;> rcases abs_cases (S true) with ⟨h1, _⟩ | ⟨h1, _⟩
      · have hp := hpair_le 1 1 (Or.inl rfl) (Or.inl rfl)
        rw [h0, h1]; linarith [le_abs_self (∑ u : Fin n → F2, eps0 u * eps1 u)]
      · have hp := hpair_le 1 (-1) (Or.inl rfl) (Or.inr rfl)
        rw [h0, h1]; linarith [neg_le_abs (∑ u : Fin n → F2, eps0 u * eps1 u)]
      · have hp := hpair_le (-1) 1 (Or.inr rfl) (Or.inl rfl)
        rw [h0, h1]; linarith [neg_le_abs (∑ u : Fin n → F2, eps0 u * eps1 u)]
      · have hp := hpair_le (-1) (-1) (Or.inr rfl) (Or.inr rfl)
        rw [h0, h1]; linarith [le_abs_self (∑ u : Fin n → F2, eps0 u * eps1 u)]
    have hnat : ((S false).natAbs + (S true).natAbs : ℤ) ≤
        ((2 ^ n + (∑ u : Fin n → F2, eps0 u * eps1 u).natAbs : ℕ) : ℤ) := by
      simpa [Int.natCast_natAbs] using hcomb
    exact_mod_cast hnat
  rcases build_sslice_list n D.gates hleg with ⟨L, hLval, hLpart⟩
  let hpart_equiv : (Σ idx : Fin L.length, (L.get idx).U) ≃ (Fin n → F2) :=
    let fIdx : (Fin n → F2) → Fin L.length := fun u => (hLpart u).choose
    have hmem : ∀ u, u - (L.get (fIdx u)).p ∈ (L.get (fIdx u)).U := fun u => (hLpart u).choose_spec.1
    have huniq : ∀ u idx, u - (L.get idx).p ∈ (L.get idx).U → idx = fIdx u := fun u idx h => (hLpart u).choose_spec.2 idx h
    { toFun := fun q => (L.get q.1).p + q.2.val
      invFun := fun u => ⟨fIdx u, ⟨u - (L.get (fIdx u)).p, hmem u⟩⟩
      left_inv := fun ⟨idx, ⟨v, hv⟩⟩ => by
        have hm : (L.get idx).p + v - (L.get idx).p ∈ (L.get idx).U := by simpa using hv
        have hi : fIdx ((L.get idx).p + v) = idx := (huniq _ idx hm).symm
        dsimp only
        generalize hmem ((L.get idx).p + v) = hjm
        revert hjm
        generalize fIdx ((L.get idx).p + v) = j at hi ⊢
        subst hi; intro _
        congr 1; apply Subtype.ext; simp
      right_inv := fun u => by show (L.get (fIdx u)).p + (u - (L.get (fIdx u)).p) = u; abel }
  have hsum_card : ∑ idx : Fin L.length, 2 ^ Module.finrank F2 (L.get idx).U = 2 ^ n := by
    have h1 : Fintype.card (Σ idx : Fin L.length, (L.get idx).U) =
        ∑ idx : Fin L.length, 2 ^ Module.finrank F2 (L.get idx).U := by
      rw [Fintype.card_sigma]
      refine Finset.sum_congr rfl fun idx _ => card_submodule_zmod2 _
    have h2 : Fintype.card (Fin n → F2) = 2 ^ n := by simp [ZMod.card]
    rw [← h1, ← h2]
    exact Fintype.card_congr hpart_equiv
  have hleaf_bound : ∀ idx : Fin L.length,
      (∑ v : (L.get idx).U, eps0 ((L.get idx).p + v.val) * eps1 ((L.get idx).p + v.val)).natAbs * 2 ^ (r - c) ≤
        2 ^ Module.finrank F2 (L.get idx).U := by
    intro idx
    set P := L.get idx
    have hP := hLval P (List.get_mem L idx)
    have hPdim : n ≤ Module.finrank F2 P.U + c := by have := hP.1; omega
    by_cases hcr : r ≤ c
    · have hrc : r - c = 0 := by omega
      rw [hrc, pow_zero, mul_one]
      have htri := Finset.abs_sum_le_sum_abs
        (fun v : P.U => eps0 (P.p + v.val) * eps1 (P.p + v.val)) Finset.univ
      have habs1 : ∀ v : P.U, |eps0 (P.p + v.val) * eps1 (P.p + v.val)| = 1 := by
        intro v; dsimp only [eps0, eps1]
        rw [abs_mul, abs_mul, abs_mul, signBool_abs_one, signBool_abs_one, signBool_abs_one, signBool_abs_one]
        norm_num
      simp_rw [habs1] at htri
      have hnat : ((∑ v : P.U, eps0 (P.p + v.val) * eps1 (P.p + v.val)).natAbs : ℤ) ≤
          (Fintype.card P.U : ℤ) := by simpa [Int.natCast_natAbs] using htri
      rw [card_submodule_zmod2] at hnat
      exact_mod_cast hnat
    · have h2r_le_n : 2 * r ≤ n := by have := rank_add_ker_mat M; omega
      have hdim_le : n - r + (r - c) ≤ Module.finrank F2 P.U := by omega
      let lin : Fin n → F2 :=
        P.slope (tap 0) + ∑ j : Fin n, (P.off0 (tap j.succ) + P.off1 (tap j.succ)) • Pi.single j 1
      let cc : F2 := (P.off0 D.output + P.off1 D.output) + P.off1 (tap 0) +
        ∑ j : Fin n, (P.off0 (tap j.succ) + P.off1 (tap j.succ)) * P.p j
      have hterm : ∀ v : P.U, eps0 (P.p + v.val) * eps1 (P.p + v.val) =
          signBool (decide ((Q false (P.p + v.val) + Q true (P.p + v.val)) + dotProduct lin v.val + cc = 1)) := by
        intro v
        dsimp only [eps0, eps1, f0, f1]
        have hD := hP.2 D.output hout v.val v.property
        have hT : ∀ j : Fin (n + 1),
            pos (Fin.cons 0 (P.p + v.val)) j = dotProduct (P.slope (tap j)) v.val + P.off0 (tap j) ∧
            pos (Fin.cons 1 (P.p + v.val)) j = dotProduct (P.slope (tap j)) v.val + P.off1 (tap j) := by
          intro j
          have ht := hP.2 (tap j) (htap j) v.val v.property
          dsimp only [pos]
          change (if (wiresOf D.gates _).getD (tap j) false then (1 : F2) else 0) = _ ∧
                 (if (wiresOf D.gates _).getD (tap j) false then (1 : F2) else 0) = _
          rw [ht.1, ht.2, zmod2_decide_bool, zmod2_decide_bool]
          exact ⟨rfl, rfl⟩
        have hdot0 : dotProduct (pos (Fin.cons 0 (P.p + v.val))) (Fin.cons 0 (P.p + v.val)) =
            ∑ j : Fin n, (dotProduct (P.slope (tap j.succ)) v.val + P.off0 (tap j.succ)) * (P.p j + v.val j) := by
          rw [dotProduct, Fin.sum_univ_succ]
          simp only [Fin.cons_zero, mul_zero, zero_add, Fin.cons_succ, Pi.add_apply]
          refine Finset.sum_congr rfl fun j _ => by rw [(hT j.succ).1]
        have hdot1 : dotProduct (pos (Fin.cons 1 (P.p + v.val))) (Fin.cons 1 (P.p + v.val)) =
            (dotProduct (P.slope (tap 0)) v.val + P.off1 (tap 0)) +
            ∑ j : Fin n, (dotProduct (P.slope (tap j.succ)) v.val + P.off1 (tap j.succ)) * (P.p j + v.val j) := by
          rw [dotProduct, Fin.sum_univ_succ]
          simp only [Fin.cons_zero, mul_one, Fin.cons_succ, Pi.add_apply]
          rw [(hT 0).2]
          congr 1
          refine Finset.sum_congr rfl fun j _ => by rw [(hT j.succ).2]
        have hDeval0 : D.eval (bitsOf (n + 1) (Fin.cons 0 (P.p + v.val))) =
            decide (dotProduct (P.slope D.output) v.val + P.off0 D.output = 1) := hD.1
        have hDeval1 : D.eval (bitsOf (n + 1) (Fin.cons 1 (P.p + v.val))) =
            decide (dotProduct (P.slope D.output) v.val + P.off1 D.output = 1) := hD.2
        rw [hDeval0, hDeval1, hdot0, hdot1]
        rw [← zmod2_add_decide, ← zmod2_add_decide]
        have hmul4 : ∀ b1 b2 b3 b4 : F2,
            signBool (decide (b1 = 1)) * signBool (decide (b2 = 1)) *
            (signBool (decide (b3 = 1)) * signBool (decide (b4 = 1))) =
            signBool (decide (b1 + b2 + b3 + b4 = 1)) := by
          intro b1 b2 b3 b4
          rw [← signBool_xor, ← signBool_xor, ← signBool_xor, ← zmod2_add_decide, ← zmod2_add_decide, ← zmod2_add_decide]
          congr 2; ring
        rw [hmul4]
        apply congrArg (fun x => signBool (decide (x = 1)))
        have hlin_v : dotProduct lin v.val = dotProduct (P.slope (tap 0)) v.val +
            ∑ j : Fin n, (P.off0 (tap j.succ) + P.off1 (tap j.succ)) * v.val j := by
          simp only [lin, add_dotProduct, sum_dotProduct, smul_dotProduct, single_dotProduct, smul_eq_mul, one_mul]
        have hsum_cancel : (∑ j : Fin n, (dotProduct (P.slope (tap j.succ)) v.val + P.off0 (tap j.succ)) * (P.p j + v.val j)) +
            (∑ j : Fin n, (dotProduct (P.slope (tap j.succ)) v.val + P.off1 (tap j.succ)) * (P.p j + v.val j)) =
            (∑ j : Fin n, (P.off0 (tap j.succ) + P.off1 (tap j.succ)) * P.p j) +
            (∑ j : Fin n, (P.off0 (tap j.succ) + P.off1 (tap j.succ)) * v.val j) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hz := z2_add_self (dotProduct (P.slope (tap j.succ)) v.val * (P.p j + v.val j))
          linear_combination hz
        have hzD := z2_add_self (dotProduct (P.slope D.output) v.val)
        dsimp only [cc]
        linear_combination hsum_cancel - hlin_v + hzD
      simp_rw [hterm]
      have hq := quad_subspace_bias_le (fun u => Q false u + Q true u) M hrk hd P.U P.p lin cc
      calc (∑ v : P.U, signBool (decide ((Q false (P.p + v.val) + Q true (P.p + v.val)) + dotProduct lin v.val + cc = 1))).natAbs * 2 ^ (r - c)
          ≤ 2 ^ (n - r) * 2 ^ (r - c) := Nat.mul_le_mul_right _ hq
        _ = 2 ^ (n - r + (r - c)) := (pow_add 2 _ _).symm
        _ ≤ 2 ^ Module.finrank F2 P.U := Nat.pow_le_pow_right (by omega) hdim_le
  have hprod_bound : (∑ u : Fin n → F2, eps0 u * eps1 u).natAbs * 2 ^ (r - c) ≤ 2 ^ n := by
    have hdecomp : (∑ u : Fin n → F2, eps0 u * eps1 u) =
        ∑ idx : Fin L.length, ∑ v : (L.get idx).U, eps0 ((L.get idx).p + v.val) * eps1 ((L.get idx).p + v.val) := by
      rw [← Equiv.sum_comp hpart_equiv, Fintype.sum_sigma]
      rfl
    rw [hdecomp]
    have htri := Finset.abs_sum_le_sum_abs
      (fun idx : Fin L.length => ∑ v : (L.get idx).U, eps0 ((L.get idx).p + v.val) * eps1 ((L.get idx).p + v.val)) Finset.univ
    have hnat_tri : (∑ idx : Fin L.length, ∑ v : (L.get idx).U, eps0 ((L.get idx).p + v.val) * eps1 ((L.get idx).p + v.val)).natAbs ≤
        ∑ idx : Fin L.length, (∑ v : (L.get idx).U, eps0 ((L.get idx).p + v.val) * eps1 ((L.get idx).p + v.val)).natAbs := by
      have h1 : ((∑ idx : Fin L.length, ∑ v : (L.get idx).U, eps0 ((L.get idx).p + v.val) * eps1 ((L.get idx).p + v.val)).natAbs : ℤ) ≤
          ((∑ idx : Fin L.length, (∑ v : (L.get idx).U, eps0 ((L.get idx).p + v.val) * eps1 ((L.get idx).p + v.val)).natAbs : ℕ) : ℤ) := by
        simpa [Int.natCast_natAbs, Nat.cast_sum] using htri
      exact Int.ofNat_le.mp h1
    calc (∑ idx : Fin L.length, ∑ v : (L.get idx).U, eps0 ((L.get idx).p + v.val) * eps1 ((L.get idx).p + v.val)).natAbs * 2 ^ (r - c)
        ≤ (∑ idx : Fin L.length, (∑ v : (L.get idx).U, eps0 ((L.get idx).p + v.val) * eps1 ((L.get idx).p + v.val)).natAbs) * 2 ^ (r - c) :=
          Nat.mul_le_mul_right _ hnat_tri
      _ = ∑ idx : Fin L.length, (∑ v : (L.get idx).U, eps0 ((L.get idx).p + v.val) * eps1 ((L.get idx).p + v.val)).natAbs * 2 ^ (r - c) :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ idx : Fin L.length, 2 ^ Module.finrank F2 (L.get idx).U := Finset.sum_le_sum fun idx _ => hleaf_bound idx
      _ = 2 ^ n := hsum_card
  have h2n_pos : (0 : ℚ) < (2 : ℚ) ^ n := by positivity
  have h2rc_pos : (0 : ℚ) < (2 : ℚ) ^ (r - c) := by positivity
  have habs_q : |(S false : ℚ)| + |(S true : ℚ)| ≤ (2 : ℚ) ^ n + (2 : ℚ) ^ n / (2 : ℚ) ^ (r - c) := by
    have hq1 : |(S false : ℚ)| + |(S true : ℚ)| = (((S false).natAbs + (S true).natAbs : ℕ) : ℚ) := by
      push_cast
      rw [show |(S false : ℚ)| = ((S false).natAbs : ℚ) by rw [← Int.cast_abs, ← Int.natCast_natAbs]; rfl,
          show |(S true : ℚ)| = ((S true).natAbs : ℚ) by rw [← Int.cast_abs, ← Int.natCast_natAbs]; rfl]
    have hq2 : (((S false).natAbs + (S true).natAbs : ℕ) : ℚ) ≤
        ((2 ^ n + (∑ u : Fin n → F2, eps0 u * eps1 u).natAbs : ℕ) : ℚ) := by exact_mod_cast habs_le
    have hq3 : (((∑ u : Fin n → F2, eps0 u * eps1 u).natAbs : ℕ) : ℚ) * (2 : ℚ) ^ (r - c) ≤ (2 : ℚ) ^ n := by
      exact_mod_cast hprod_bound
    have hq4 : (((∑ u : Fin n → F2, eps0 u * eps1 u).natAbs : ℕ) : ℚ) ≤ (2 : ℚ) ^ n / (2 : ℚ) ^ (r - c) :=
      (le_div_iff₀ h2rc_pos).mpr hq3
    push_cast at hq1 hq2
    linarith
  calc |(S false : ℚ)| / 2 ^ n + |(S true : ℚ)| / 2 ^ n
      = (|(S false : ℚ)| + |(S true : ℚ)|) / 2 ^ n := by ring
    _ ≤ ((2 : ℚ) ^ n + (2 : ℚ) ^ n / (2 : ℚ) ^ (r - c)) / 2 ^ n := div_le_div_of_nonneg_right habs_q (le_of_lt h2n_pos)
    _ = 1 + 1 / (2 : ℚ) ^ (r - c) := by field_simp

def scoreQ (n : ℕ) (Q : Bool → (Fin n → F2) → F2) (C : Circuit) (t : Bool) : ℚ :=
  let k := n + 1
  (∑ x : Fin k → F2, ∑ u : Fin n → F2,
    let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
    if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + Q t u = 1)
    then (1 : ℚ) else -1) / 2 ^ (k + n)

lemma score_in_region (n r s : ℕ) (Q : Bool → (Fin n → F2) → F2)
    (M : Matrix (Fin n) (Fin n) F2) (hrk : M.rank = 2 * r)
    (hd : ∀ u v, (Q false (u + v) + Q true (u + v)) + (Q false u + Q true u) +
      (Q false v + Q true v) + (Q false 0 + Q true 0) = dotProduct u (M.mulVec v))
    (C : Circuit) (hleg : legalGates (2 * (n + 1)) C.gates) (hcost : costGates C.gates ≤ s) :
    let k := n + 1
    let rho : ℚ := if s < k then 1 / 2 ^ (n - s) else 1
    let total : ℚ := if s < k then rho else 1 + 1 / 2 ^ (r - (s - k))
    |scoreQ n Q C false| ≤ rho ∧ |scoreQ n Q C true| ≤ rho ∧
      |scoreQ n Q C false| + |scoreQ n Q C true| ≤ total := by
  intro k rho total
  have hleg' : legalGates (k + k) C.gates := by rwa [show k + k = 2 * (n + 1) by omega]
  rcases decomp_835 k k C hleg' with ⟨N, ri, U, a, D, tap, hNpos, hmeta, hpart, heval⟩
  let pos := fun (i : Fin N) (y : Fin k → F2) (j : Fin k) =>
    if ((D i).wires (bitsOf k y)).getD (tap i j) false then (1 : F2) else 0
  let W : Fin N → Submodule F2 (Fin k → F2) := fun i => orthoComp (U i)
  have hW_dim : ∀ i, Module.finrank F2 (W i) = ri i := by
    intro i; dsimp only [W]; have := finrank_orthoComp (U i); have := (hmeta i).1; omega
  have hU_dim : ∀ i, Module.finrank F2 (U i) = k - ri i := by
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
        subst hi; intro _
        congr 1; apply Subtype.ext; simp
      right_inv := fun x => by show pos (idxOf x) y + (x - pos (idxOf x) y) = x; abel }
  have hsum_pow : (∑ i : Fin N, 2 ^ (k - ri i)) = 2 ^ k := by
    have h1 : Fintype.card (Σ i : Fin N, U i) = ∑ i : Fin N, 2 ^ (k - ri i) := by
      rw [Fintype.card_sigma]
      refine Finset.sum_congr rfl fun i _ => by rw [card_submodule_zmod2, hU_dim i]
    have h2 : Fintype.card (Fin k → F2) = 2 ^ k := by simp [ZMod.card]
    rw [← h1, ← h2]
    exact Fintype.card_congr (hpart_equiv 0)
  have hprof : ∀ y : Fin k → F2,
      (∑ x : Fin k → F2, signBool (Bool.xor (C.eval (bitsOf k x ++ bitsOf k y)) (decide (dotProduct x y = 1)))) =
      ∑ i : Fin N, (2 : ℤ) ^ (k - ri i) *
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
      rw [hdot_eq, zmod2_add_decide, signBool_xor, signBool_xor]; ring
    have heq_fn : ∀ u : U i, hpart_equiv y ⟨i, u⟩ = pos i y + u.val := fun _ => by dsimp [hpart_equiv]
    simp_rw [heq_fn, hterm, ← Finset.mul_sum, sum_sign_dot_submodule (U i) (y - a i), hU_dim i]
    dsimp only [W]; split_ifs <;> ring
  let wt : Fin N → ℚ := fun i => (2 : ℚ) ^ (k - ri i) / (2 : ℚ) ^ k
  have hwt_nonneg : ∀ i, 0 ≤ wt i := fun i => by dsimp only [wt]; positivity
  have hwt_sum : ∑ i : Fin N, wt i = 1 := by
    dsimp only [wt]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← div_eq_mul_inv]
    have hq : (∑ i : Fin N, (2 : ℚ) ^ (k - ri i)) = (2 : ℚ) ^ k := by exact_mod_cast hsum_pow
    rw [hq, div_self (by positivity)]
  let atomS : Fin N → Bool → ℚ := fun i t =>
    ((∑ u : Fin n → F2,
      let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
      if y - a i ∈ W i then
        signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
          signBool (decide (Q t u = 1))
      else 0 : ℤ) : ℚ) / (2 : ℚ) ^ n
  have hscore_decomp : ∀ t : Bool, scoreQ n Q C t = ∑ i : Fin N, wt i * atomS i t := by
    intro t
    dsimp only [scoreQ]
    have hnum_int : (∑ x : Fin k → F2, ∑ u : Fin n → F2,
        let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
        if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + Q t u = 1)
        then (1 : ℚ) else -1) =
        ((∑ x : Fin k → F2, ∑ u : Fin n → F2,
          let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
          if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + Q t u = 1)
          then (1 : ℤ) else -1 : ℤ) : ℚ) := by
      push_cast
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun u _ => ?_
      split_ifs <;> norm_num
    rw [hnum_int]
    have hsum_z : (∑ x : Fin k → F2, ∑ u : Fin n → F2,
        let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
        if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + Q t u = 1)
        then (1 : ℤ) else -1) =
        ∑ i : Fin N, (2 : ℤ) ^ (k - ri i) *
          ∑ u : Fin n → F2,
            let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
            if y - a i ∈ W i then
              signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
                signBool (decide (Q t u = 1))
            else 0 := by
      rw [Finset.sum_comm]
      have hu : ∀ u : Fin n → F2,
          let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
          (∑ x : Fin k → F2, if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + Q t u = 1)
            then (1 : ℤ) else -1) =
          ∑ i : Fin N, (2 : ℤ) ^ (k - ri i) *
            (if y - a i ∈ W i then
              signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
                signBool (decide (Q t u = 1))
            else 0) := by
        intro u y
        have hstep : ∀ x : Fin k → F2,
            (if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + Q t u = 1) then (1 : ℤ) else -1) =
            signBool (Bool.xor (C.eval (bitsOf k x ++ bitsOf k y)) (decide (dotProduct x y = 1))) *
              signBool (decide (Q t u = 1)) := fun x => by rw [zmod2_add_decide, agree_eq_sign]
        simp_rw [hstep, ← Finset.sum_mul, hprof y, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
      simp_rw [hu]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    rw [hsum_z]
    dsimp only [wt, atomS]
    push_cast
    rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← div_eq_mul_inv, pow_add]; field_simp; ring
  have hatom_bound : ∀ i : Fin N,
      |atomS i false| ≤ rho ∧ |atomS i true| ≤ rho ∧ |atomS i false| + |atomS i true| ≤ total := by
    intro i
    have hri_le_s : ri i ≤ s := by have := (hmeta i).2.2.1; omega
    have hri_le_k : ri i ≤ k := by have := (hmeta i).1; omega
    have hcard_slice : ∀ t : Bool,
        |atomS i t| ≤ ((Finset.univ.filter (fun u : Fin n → F2 =>
          (Fin.cons (if t then (1 : F2) else 0) u) - a i ∈ W i)).card : ℚ) / (2 : ℚ) ^ n := by
      intro t
      dsimp only [atomS]
      rw [abs_div, abs_of_pos (by positivity : (0 : ℚ) < (2 : ℚ) ^ n)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have htri := Finset.abs_sum_le_sum_abs
        (fun u : Fin n → F2 =>
          let y : Fin k → F2 := Fin.cons (if t then (1 : F2) else 0) u
          if y - a i ∈ W i then
            signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
              signBool (decide (Q t u = 1))
          else 0) Finset.univ
      have habs : ∀ u : Fin n → F2,
          |let y : Fin k → F2 := Fin.cons (if t then (1 : F2) else 0) u
           if y - a i ∈ W i then
            signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
              signBool (decide (Q t u = 1))
          else 0| = if (Fin.cons (if t then (1 : F2) else 0) u) - a i ∈ W i then (1 : ℤ) else 0 := by
        intro u; dsimp only
        by_cases hmem : (Fin.cons (if t then (1 : F2) else 0) u) - a i ∈ W i
        · simp only [hmem, ↓reduceIte, abs_mul, signBool_abs_one, mul_one]
        · simp only [hmem, ↓reduceIte, abs_zero]
      simp_rw [habs] at htri
      have hfilt : (∑ u : Fin n → F2, if (Fin.cons (if t then (1 : F2) else 0) u) - a i ∈ W i then (1 : ℤ) else 0) =
          ((Finset.univ.filter (fun u : Fin n → F2 =>
            (Fin.cons (if t then (1 : F2) else 0) u) - a i ∈ W i)).card : ℤ) := by
        simp [Finset.sum_boole]
      rw [hfilt] at htri
      exact_mod_cast htri
    have hsum_cards : (Finset.univ.filter (fun u : Fin n → F2 => (Fin.cons (0 : F2) u) - a i ∈ W i)).card +
        (Finset.univ.filter (fun u : Fin n → F2 => (Fin.cons (1 : F2) u) - a i ∈ W i)).card = 2 ^ (ri i) := by
      let e01 : {u : Fin n → F2 // Fin.cons (0 : F2) u - a i ∈ W i} ⊕
                {u : Fin n → F2 // Fin.cons (1 : F2) u - a i ∈ W i} ≃ W i :=
        { toFun := Sum.elim (fun u => ⟨Fin.cons 0 u.val - a i, u.property⟩)
                            (fun u => ⟨Fin.cons 1 u.val - a i, u.property⟩)
          invFun := fun w =>
            let y := a i + w.val
            if h0 : y 0 = 0 then
              Sum.inl ⟨fun j => y j.succ, by
                have hy : Fin.cons (0 : F2) (fun j => y j.succ) = y := by
                  funext j; refine Fin.cases (by simp [h0]) (fun _ => by simp) j
                rw [hy]; show a i + w.val - a i ∈ W i; simpa using w.property⟩
            else
              Sum.inr ⟨fun j => y j.succ, by
                have h1 : y 0 = 1 := by rcases zmod2_cases (y 0) with h | h; exact absurd h h0; exact h
                have hy : Fin.cons (1 : F2) (fun j => y j.succ) = y := by
                  funext j; refine Fin.cases (by simp [h1]) (fun _ => by simp) j
                rw [hy]; show a i + w.val - a i ∈ W i; simpa using w.property⟩
          left_inv := fun s => by
            cases s with
            | inl u =>
              let y0 : Fin k → F2 := Fin.cons (0 : F2) u.val
              have hy : a i + (y0 - a i) = y0 := by abel
              have hy0 : (a i + (y0 - a i)) 0 = 0 := by rw [hy]; simp [y0]
              dsimp only; change (if h0 : (a i + (y0 - a i)) 0 = 0 then _ else _) = Sum.inl u
              rw [dif_pos hy0]
              congr 1; apply Subtype.ext; funext j; dsimp only [Sum.elim_inl]; rw [hy]; simp [y0]
            | inr u =>
              let y1 : Fin k → F2 := Fin.cons (1 : F2) u.val
              have hy : a i + (y1 - a i) = y1 := by abel
              have hy1 : (a i + (y1 - a i)) 0 ≠ 0 := by rw [hy]; simp [y1]
              dsimp only; change (if h0 : (a i + (y1 - a i)) 0 = 0 then _ else _) = Sum.inr u
              rw [dif_neg hy1]
              congr 1; apply Subtype.ext; funext j; dsimp only [Sum.elim_inr]; rw [hy]; simp [y1]
          right_inv := fun w => by
            dsimp only
            by_cases h0 : (a i + w.val) 0 = 0
            · simp only [h0, ↓reduceDIte, Sum.elim_inl]
              apply Subtype.ext; dsimp only
              have hy : Fin.cons (0 : F2) (fun j => (a i + w.val) j.succ) = a i + w.val := by
                funext j; refine Fin.cases (by simp [h0]) (fun _ => by simp) j
              rw [hy]; abel
            · have h1 : (a i + w.val) 0 = 1 := by rcases zmod2_cases ((a i + w.val) 0) with h | h; exact absurd h h0; exact h
              simp only [h0, ↓reduceDIte, Sum.elim_inr]
              apply Subtype.ext; dsimp only
              have hy : Fin.cons (1 : F2) (fun j => (a i + w.val) j.succ) = a i + w.val := by
                funext j; refine Fin.cases (by simp [h1]) (fun _ => by simp) j
              rw [hy]; abel }
      rw [← Fintype.card_subtype, ← Fintype.card_subtype, ← Fintype.card_sum, Fintype.card_congr e01,
          card_submodule_zmod2, hW_dim i]
    have hsum_le_pow : |atomS i false| + |atomS i true| ≤ (2 : ℚ) ^ (ri i) / (2 : ℚ) ^ n := by
      have h0 := hcard_slice false
      have h1 := hcard_slice true
      simp only [Bool.false_eq_true, ↓reduceIte] at h0
      simp only [↓reduceIte] at h1
      calc |atomS i false| + |atomS i true|
          ≤ ((Finset.univ.filter (fun u : Fin n → F2 => (Fin.cons (0 : F2) u) - a i ∈ W i)).card : ℚ) / 2 ^ n +
            ((Finset.univ.filter (fun u : Fin n → F2 => (Fin.cons (1 : F2) u) - a i ∈ W i)).card : ℚ) / 2 ^ n :=
            by exact add_le_add h0 h1
        _ = (((Finset.univ.filter (fun u : Fin n → F2 => (Fin.cons (0 : F2) u) - a i ∈ W i)).card +
              (Finset.univ.filter (fun u : Fin n → F2 => (Fin.cons (1 : F2) u) - a i ∈ W i)).card : ℕ) : ℚ) / 2 ^ n := by
            push_cast; ring
        _ = (2 : ℚ) ^ (ri i) / (2 : ℚ) ^ n := by rw [hsum_cards]; push_cast; rfl
    have hle_one : ∀ t : Bool, |atomS i t| ≤ 1 := by
      intro t
      have h1 := hcard_slice t
      have h2 : ((Finset.univ.filter (fun u : Fin n → F2 => (Fin.cons (if t then (1 : F2) else 0) u) - a i ∈ W i)).card : ℚ) ≤ (2 : ℚ) ^ n := by
        have hc : (Finset.univ.filter (fun u : Fin n → F2 => (Fin.cons (if t then (1 : F2) else 0) u) - a i ∈ W i)).card ≤
            Fintype.card (Fin n → F2) := Finset.card_filter_le _ _
        simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card] at hc
        exact_mod_cast hc
      calc |atomS i t| ≤ _ := h1
        _ ≤ (2 : ℚ) ^ n / (2 : ℚ) ^ n := div_le_div_of_nonneg_right h2 (by positivity)
        _ = 1 := div_self (by positivity)
    by_cases hsk : s < k
    · have hrho_eq : rho = 1 / 2 ^ (n - s) := if_pos hsk
      have htot_eq : total = 1 / 2 ^ (n - s) := by dsimp only [total]; rw [if_pos hsk, hrho_eq]
      have hpow_le : (2 : ℚ) ^ (ri i) / (2 : ℚ) ^ n ≤ 1 / 2 ^ (n - s) := by
        have h1 : (2 : ℚ) ^ (ri i) ≤ (2 : ℚ) ^ s := pow_le_pow_right₀ (by norm_num) hri_le_s
        have h2 : (2 : ℚ) ^ n = (2 : ℚ) ^ s * (2 : ℚ) ^ (n - s) := by
          rw [← pow_add, show s + (n - s) = n by omega]
        rw [h2]
        calc (2 : ℚ) ^ (ri i) / ((2 : ℚ) ^ s * (2 : ℚ) ^ (n - s))
            ≤ (2 : ℚ) ^ s / ((2 : ℚ) ^ s * (2 : ℚ) ^ (n - s)) := div_le_div_of_nonneg_right h1 (by positivity)
          _ = 1 / (2 : ℚ) ^ (n - s) := by field_simp
      have htot : |atomS i false| + |atomS i true| ≤ 1 / 2 ^ (n - s) := le_trans hsum_le_pow hpow_le
      rw [hrho_eq, htot_eq]
      exact ⟨by linarith [abs_nonneg (atomS i true)], by linarith [abs_nonneg (atomS i false)], htot⟩
    · have hrho_eq : rho = 1 := if_neg hsk
      have htot_eq : total = 1 + 1 / 2 ^ (r - (s - k)) := if_neg hsk
      rw [hrho_eq, htot_eq]
      refine ⟨hle_one false, hle_one true, ?_⟩
      by_cases hfull : ri i < k
      · have h1 : (2 : ℚ) ^ (ri i) ≤ (2 : ℚ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
        have h2 : (2 : ℚ) ^ (ri i) / (2 : ℚ) ^ n ≤ 1 := (div_le_one (by positivity)).mpr h1
        have h3 : (0 : ℚ) ≤ 1 / 2 ^ (r - (s - k)) := by positivity
        linarith
      · have hrik : ri i = k := by omega
        have hWtop : W i = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hW_dim i, hrik, Module.finrank_fin_fun])
        have hcostD : costGates (D i).gates ≤ s - k := by have := (hmeta i).2.2.1; omega
        have hfb := full_slice_atom_bound n r (s - k) Q M hrk hd (D i) (tap i)
          (hmeta i).2.1 hcostD (hmeta i).2.2.2.1 (hmeta i).2.2.2.2
        have heq_t : ∀ t : Bool, |atomS i t| =
            |((∑ u : Fin n → F2,
              let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
              signBool (Bool.xor ((D i).eval (bitsOf k y)) (decide (dotProduct (pos i y) y = 1))) *
                signBool (decide (Q t u = 1)) : ℤ) : ℚ)| / (2 : ℚ) ^ n := by
          intro t
          dsimp only [atomS]
          rw [abs_div, abs_of_pos (by positivity : (0 : ℚ) < (2 : ℚ) ^ n)]
          congr 2; simp only [hWtop, Submodule.mem_top, ↓reduceIte]
        rw [heq_t false, heq_t true]
        exact hfb
  have hconv_abs : ∀ t : Bool, |scoreQ n Q C t| ≤ ∑ i : Fin N, wt i * |atomS i t| := by
    intro t
    rw [hscore_decomp t]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul, abs_of_nonneg (hwt_nonneg i)]
  refine ⟨?_, ?_, ?_⟩
  · calc |scoreQ n Q C false| ≤ ∑ i : Fin N, wt i * |atomS i false| := hconv_abs false
      _ ≤ ∑ i : Fin N, wt i * rho := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hatom_bound i).1 (hwt_nonneg i)
      _ = (∑ i : Fin N, wt i) * rho := (Finset.sum_mul _ _ _).symm
      _ = rho := by rw [hwt_sum, one_mul]
  · calc |scoreQ n Q C true| ≤ ∑ i : Fin N, wt i * |atomS i true| := hconv_abs true
      _ ≤ ∑ i : Fin N, wt i * rho := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hatom_bound i).2.1 (hwt_nonneg i)
      _ = (∑ i : Fin N, wt i) * rho := (Finset.sum_mul _ _ _).symm
      _ = rho := by rw [hwt_sum, one_mul]
  · calc |scoreQ n Q C false| + |scoreQ n Q C true|
        ≤ (∑ i : Fin N, wt i * |atomS i false|) + (∑ i : Fin N, wt i * |atomS i true|) := by
          exact add_le_add (hconv_abs false) (hconv_abs true)
      _ = ∑ i : Fin N, wt i * (|atomS i false| + |atomS i true|) := by
          rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i : Fin N, wt i * total := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hatom_bound i).2.2 (hwt_nonneg i)
      _ = (∑ i : Fin N, wt i) * total := (Finset.sum_mul _ _ _).symm
      _ = total := by rw [hwt_sum, one_mul]

lemma affine_of_rank_zero_mat {n : ℕ} (f : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y)) (h0 : M.rank = 0) :
    ∃ (a : Fin n → F2) (b : F2), ∀ x, f x = dotProduct a x + b := by
  have hker : LinearMap.ker M.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by have := rank_add_ker_mat M; rw [Module.finrank_fin_fun]; omega)
  have hM0 : ∀ y, M.mulVec y = 0 := fun y => by
    have hy : y ∈ LinearMap.ker M.mulVecLin := by rw [hker]; trivial
    exact hy
  let L : (Fin n → F2) →ₗ[F2] F2 :=
    { toFun := fun x => f x + f 0
      map_add' := fun x y => by
        have h := hf x y; rw [hM0 y, dotProduct_zero] at h
        have hz0 := z2_add_self (f 0); have hzx := z2_add_self (f x); have hzy := z2_add_self (f y)
        linear_combination h - hzx - hzy - hz0
      map_smul' := fun c x => by
        rcases zmod2_cases c with rfl | rfl
        · simp [z2_add_self]
        · simp }
  obtain ⟨a, ha⟩ := linear_coord_dot L
  refine ⟨a, f 0, fun x => ?_⟩
  have h1 := ha x
  dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk] at h1
  have hz := z2_add_self (f 0)
  linear_combination h1 - hz

lemma symplectic_peel_step {n r : ℕ} (f : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (hrk : M.rank = 2 * (r + 1)) :
    ∃ (u v c1 c2 : Fin n → F2) (M' : Matrix (Fin n) (Fin n) F2),
      let f' := fun x => f x + dotProduct c1 x * dotProduct c2 x
      M'.rank = 2 * r ∧
      (∀ x y, f' (x + y) + f' x + f' y + f' 0 = dotProduct x (M'.mulVec y)) ∧
      M'.mulVec u = 0 ∧ M'.mulVec v = 0 ∧
      dotProduct c1 u = 0 ∧ dotProduct c1 v = 1 ∧ dotProduct c2 u = 1 ∧ dotProduct c2 v = 0 := by
  have hne0 : M.rank ≠ 0 := by omega
  have hexv : ∃ v : Fin n → F2, M.mulVec v ≠ 0 := by
    by_contra hno; push Not at hno
    have hker : LinearMap.ker M.mulVecLin = ⊤ := eq_top_iff.mpr fun y _ => hno y
    have := rank_add_ker_mat M; rw [hker, finrank_top, Module.finrank_fin_fun] at this; omega
  obtain ⟨v, hv⟩ := hexv
  have hexi : ∃ i : Fin n, M.mulVec v i = 1 := by
    by_contra hno; push Not at hno; apply hv; funext i
    rcases zmod2_cases (M.mulVec v i) with h | h; exact h; exact absurd h (hno i)
  obtain ⟨i, hi⟩ := hexi
  let u : Fin n → F2 := Pi.single i 1
  have huv : dotProduct u (M.mulVec v) = 1 := by simp [u, single_dotProduct, hi]
  let c1 : Fin n → F2 := M.mulVec u
  let c2 : Fin n → F2 := M.mulVec v
  have hc1 : ∀ x, dotProduct c1 x = dotProduct u (M.mulVec x) := fun x => by rw [dotProduct_comm, polar_symm_mat f M hf]
  have hc2 : ∀ x, dotProduct c2 x = dotProduct v (M.mulVec x) := fun x => by rw [dotProduct_comm, polar_symm_mat f M hf]
  let f' : (Fin n → F2) → F2 := fun x => f x + dotProduct c1 x * dotProduct c2 x
  let M' : Matrix (Fin n) (Fin n) F2 := Matrix.of fun a b => M a b + c1 a * c2 b + c2 a * c1 b
  have hM'mul : ∀ y a, M'.mulVec y a = M.mulVec y a + c1 a * dotProduct c2 y + c2 a * dotProduct c1 y := by
    intro y a; simp only [Matrix.mulVec, dotProduct, M', Matrix.of_apply]
    have heq : ∀ b, (M a b + c1 a * c2 b + c2 a * c1 b) * y b =
        M a b * y b + c1 a * (c2 b * y b) + c2 a * (c1 b * y b) := fun b => by ring
    simp only [heq, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hf' : ∀ x y, f' (x + y) + f' x + f' y + f' 0 = dotProduct x (M'.mulVec y) := by
    intro x y
    have hdot : dotProduct x (M'.mulVec y) =
        dotProduct x (M.mulVec y) + dotProduct x c1 * dotProduct c2 y + dotProduct x c2 * dotProduct c1 y := by
      unfold dotProduct; simp only [hM'mul, dotProduct]
      have heq : ∀ a, x a * (M.mulVec y a + c1 a * ∑ b, c2 b * y b + c2 a * ∑ b, c1 b * y b) =
          x a * M.mulVec y a + (x a * c1 a) * (∑ b, c2 b * y b) + (x a * c2 a) * (∑ b, c1 b * y b) := fun a => by ring
      simp only [heq, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [hdot, ← hf x y]
    simp only [f', dotProduct_add, dotProduct_zero, mul_zero, add_zero]
    rw [dotProduct_comm x c1, dotProduct_comm x c2]
    have hz1 := z2_add_self (dotProduct c1 x * dotProduct c2 x)
    have hz2 := z2_add_self (dotProduct c1 y * dotProduct c2 y)
    linear_combination hz1 + hz2
  have hc1u : dotProduct c1 u = 0 := by rw [hc1, polar_self_mat f M hf]
  have hc1v : dotProduct c1 v = 1 := by rw [hc1, huv]
  have hc2u : dotProduct c2 u = 1 := by rw [hc2, polar_symm_mat f M hf, huv]
  have hc2v : dotProduct c2 v = 0 := by rw [hc2, polar_self_mat f M hf]
  have hu_ker : M'.mulVec u = 0 := by
    funext a; rw [hM'mul, hc2u, hc1u]; change c1 a + c1 a * 1 + c2 a * 0 = 0
    simp [z2_add_self]
  have hv_ker : M'.mulVec v = 0 := by
    funext a; rw [hM'mul, hc2v, hc1v]; change c2 a + c1 a * 0 + c2 a * 1 = 0
    simp [z2_add_self]
  have hker_eq : LinearMap.ker M'.mulVecLin =
      LinearMap.ker M.mulVecLin ⊔ (Submodule.span F2 {u} ⊔ Submodule.span F2 {v}) := by
    apply le_antisymm
    · intro w hw
      have hw0 : M'.mulVec w = 0 := hw
      let w0 := w + dotProduct c2 w • u + dotProduct c1 w • v
      have hw0_ker : w0 ∈ LinearMap.ker M.mulVecLin := by
        show M.mulVec w0 = 0
        funext a
        have hwa : M'.mulVec w a = 0 := congrFun hw0 a
        rw [hM'mul] at hwa
        simp only [w0, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        change M.mulVec w a + dotProduct c2 w * c1 a + dotProduct c1 w * c2 a = 0
        linear_combination hwa
      have hw_eq : w = w0 + (dotProduct c2 w • u + dotProduct c1 w • v) := by
        dsimp only [w0]
        calc w = w + (dotProduct c2 w • u + dotProduct c2 w • u) + (dotProduct c1 w • v + dotProduct c1 w • v) := by
                rw [zmod2_vec_add_self, zmod2_vec_add_self, add_zero, add_zero]
          _ = (w + dotProduct c2 w • u + dotProduct c1 w • v) + (dotProduct c2 w • u + dotProduct c1 w • v) := by abel
      rw [hw_eq]
      refine Submodule.add_mem_sup hw0_ker (Submodule.add_mem_sup ?_ ?_)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · refine sup_le (fun y hy => ?_) (sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hu_ker))
        (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv_ker)))
      show M'.mulVec y = 0
      funext a; rw [hM'mul, hc2 y, hc1 y]
      have hy0 : M.mulVec y = 0 := hy
      rw [hy0]; simp
  let S : Submodule F2 (Fin n → F2) := Submodule.span F2 {u} ⊔ Submodule.span F2 {v}
  have hune : u ≠ 0 := fun h => by rw [h, zero_dotProduct] at huv; exact one_ne_zero huv.symm
  have hvne : v ≠ 0 := fun h => by rw [h, Matrix.mulVec_zero, dotProduct_zero] at huv; exact one_ne_zero huv.symm
  have hdisj_uv : Submodule.span F2 {u} ⊓ Submodule.span F2 {v} = ⊥ := by
    rw [eq_bot_iff]; intro w hw
    rw [Submodule.mem_inf, Submodule.mem_span_singleton, Submodule.mem_span_singleton] at hw
    obtain ⟨⟨a1, rfl⟩, ⟨a2, ha2⟩⟩ := hw
    rcases zmod2_cases a1 with rfl | rfl
    · simp
    · rcases zmod2_cases a2 with rfl | rfl
      · simp at ha2; exact absurd ha2.symm hune
      · simp only [one_smul] at ha2; rw [← ha2, polar_self_mat f M hf v] at huv; exact absurd huv (by decide)
  have hSdim : Module.finrank F2 S = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F2 {u}) (Submodule.span F2 {v})
    rw [hdisj_uv, finrank_bot, add_zero, finrank_span_singleton hune, finrank_span_singleton hvne] at h
    exact h
  have hdisj_kS : LinearMap.ker M.mulVecLin ⊓ S = ⊥ := by
    rw [eq_bot_iff]; intro w hw
    rw [Submodule.mem_inf] at hw; obtain ⟨hwk, hwS⟩ := hw
    rw [Submodule.mem_sup] at hwS; obtain ⟨x1, hx1, x2, hx2, rfl⟩ := hwS
    rw [Submodule.mem_span_singleton] at hx1 hx2
    obtain ⟨a1, rfl⟩ := hx1; obtain ⟨a2, rfl⟩ := hx2
    have hm0 : M.mulVec (a1 • u + a2 • v) = 0 := hwk
    have hdu : dotProduct u (M.mulVec (a1 • u + a2 • v)) = 0 := by rw [hm0, dotProduct_zero]
    have hdv : dotProduct v (M.mulVec (a1 • u + a2 • v)) = 0 := by rw [hm0, dotProduct_zero]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul, polar_self_mat f M hf, huv, polar_symm_mat f M hf v u] at hdu hdv
    have ha2 : a2 = 0 := by simpa using hdu
    have ha1 : a1 = 0 := by simpa using hdv
    rw [Submodule.mem_bot, ha1, ha2]; simp
  have hker_dim : Module.finrank F2 (LinearMap.ker M'.mulVecLin) =
      Module.finrank F2 (LinearMap.ker M.mulVecLin) + 2 := by
    rw [hker_eq]
    have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker M.mulVecLin) S
    rw [hdisj_kS, finrank_bot, add_zero, hSdim] at h
    exact h
  have hMrk := rank_add_ker_mat M
  have hM'rk := rank_add_ker_mat M'
  refine ⟨u, v, c1, c2, M', by omega, hf', hu_ker, hv_ker, hc1u, hc1v, hc2u, hc2v⟩

lemma symplectic_approx {n : ℕ} :
    ∀ (r m : ℕ) (f : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2),
      M.rank = 2 * r →
      (∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y)) →
      ∃ (ps : List ((Fin n → F2) × (Fin n → F2))) (a : Fin n → F2) (b : F2),
        ps.length ≤ m ∧
        (∑ x : Fin n → F2, signBool (decide (f x +
          (ps.map (fun p => dotProduct p.1 x * dotProduct p.2 x)).sum + dotProduct a x + b = 1))) =
          (2 : ℤ) ^ (n - (r - m)) := by
  intro r
  induction r with
  | zero =>
    intro m f M hrk hf
    obtain ⟨a, b, hab⟩ := affine_of_rank_zero_mat f M hf (by omega)
    refine ⟨[], a, b, by simp, ?_⟩
    have hterm : ∀ x : Fin n → F2,
        signBool (decide (f x + ([].map (fun p : (Fin n → F2) × (Fin n → F2) => dotProduct p.1 x * dotProduct p.2 x)).sum +
          dotProduct a x + b = 1)) = 1 := by
      intro x
      simp only [List.map_nil, List.sum_nil, add_zero, hab x]
      have hz1 := z2_add_self (dotProduct a x); have hz2 := z2_add_self b
      have hz : dotProduct a x + b + dotProduct a x + b = 0 := by linear_combination hz1 + hz2
      rw [hz]; rfl
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.zero_sub, Nat.sub_zero, Nat.cast_pow, Nat.cast_ofNat]
  | succ r ih =>
    intro m f M hrk hf
    have h2r_le_n : 2 * (r + 1) ≤ n := by have := rank_add_ker_mat M; omega
    obtain ⟨u, v, c1, c2, M', hM'rk, hf', huker, hvker, hc1u, hc1v, hc2u, hc2v⟩ :=
      symplectic_peel_step f M hf hrk
    set f' : (Fin n → F2) → F2 := fun x => f x + dotProduct c1 x * dotProduct c2 x
    cases m with
    | succ m =>
      obtain ⟨ps, a, b, hlen, hsum⟩ := ih m f' M' hM'rk hf'
      refine ⟨(c1, c2) :: ps, a, b, by simp; omega, ?_⟩
      have hsub : r + 1 - (m + 1) = r - m := by omega
      rw [hsub, ← hsum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [List.map_cons, List.sum_cons, f']
      congr 2; ring
    | zero =>
      obtain ⟨ps, a, b, hlen, hsum⟩ := ih 0 f' M' hM'rk hf'
      have hps_nil : ps = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hps_nil
      simp only [List.map_nil, List.sum_nil, add_zero, Nat.sub_zero] at hsum
      let g' : (Fin n → F2) → F2 := fun x => f' x + dotProduct a x + b
      have hg'_shift_u : ∀ x : Fin n → F2, g' (x + u) = g' x + (g' u + g' 0) := by
        intro x
        have h1 := hf' x u; rw [huker, dotProduct_zero] at h1
        dsimp only [g']; rw [dotProduct_add, dotProduct_zero]
        have hz1 := z2_add_self (f' x); have hz2 := z2_add_self (f' u); have hz3 := z2_add_self (f' 0)
        have hz4 := z2_add_self b
        linear_combination h1 - hz1 - hz2 - hz3 - hz4
      have hg'_shift_v : ∀ x : Fin n → F2, g' (x + v) = g' x + (g' v + g' 0) := by
        intro x
        have h1 := hf' x v; rw [hvker, dotProduct_zero] at h1
        dsimp only [g']; rw [dotProduct_add, dotProduct_zero]
        have hz1 := z2_add_self (f' x); have hz2 := z2_add_self (f' v); have hz3 := z2_add_self (f' 0)
        have hz4 := z2_add_self b
        linear_combination h1 - hz1 - hz2 - hz3 - hz4
      have hgu0 : g' u + g' 0 = 0 := by
        by_contra hne
        have h1 : g' u + g' 0 = 1 := by rcases zmod2_cases (g' u + g' 0) with h | h; exact absurd h hne; exact h
        let e : (Fin n → F2) ≃ (Fin n → F2) :=
          { toFun := fun x => x + u
            invFun := fun x => x + u
            left_inv := fun x => by dsimp only; rw [add_assoc, zmod2_vec_add_self, add_zero]
            right_inv := fun x => by dsimp only; rw [add_assoc, zmod2_vec_add_self, add_zero] }
        have hneg : (∑ x : Fin n → F2, signBool (decide (g' x = 1))) = -(∑ x : Fin n → F2, signBool (decide (g' x = 1))) := by
          calc (∑ x : Fin n → F2, signBool (decide (g' x = 1)))
              = ∑ x : Fin n → F2, signBool (decide (g' (e x) = 1)) := (Equiv.sum_comp e _).symm
            _ = ∑ x : Fin n → F2, -signBool (decide (g' x = 1)) := by
                refine Finset.sum_congr rfl fun x _ => ?_
                show signBool (decide (g' (x + u) = 1)) = _
                rw [hg'_shift_u x, h1, zmod2_add_decide]
                cases decide (g' x = 1) <;> rfl
            _ = -(∑ x : Fin n → F2, signBool (decide (g' x = 1))) := by rw [Finset.sum_neg_distrib]
        have hpos : (0 : ℤ) < (2 : ℤ) ^ (n - r) := by positivity
        change (∑ x : Fin n → F2, signBool (decide (g' x = 1))) = (2 : ℤ) ^ (n - r) at hsum
        omega
      have hgv0 : g' v + g' 0 = 0 := by
        by_contra hne
        have h1 : g' v + g' 0 = 1 := by rcases zmod2_cases (g' v + g' 0) with h | h; exact absurd h hne; exact h
        let e : (Fin n → F2) ≃ (Fin n → F2) :=
          { toFun := fun x => x + v
            invFun := fun x => x + v
            left_inv := fun x => by dsimp only; rw [add_assoc, zmod2_vec_add_self, add_zero]
            right_inv := fun x => by dsimp only; rw [add_assoc, zmod2_vec_add_self, add_zero] }
        have hneg : (∑ x : Fin n → F2, signBool (decide (g' x = 1))) = -(∑ x : Fin n → F2, signBool (decide (g' x = 1))) := by
          calc (∑ x : Fin n → F2, signBool (decide (g' x = 1)))
              = ∑ x : Fin n → F2, signBool (decide (g' (e x) = 1)) := (Equiv.sum_comp e _).symm
            _ = ∑ x : Fin n → F2, -signBool (decide (g' x = 1)) := by
                refine Finset.sum_congr rfl fun x _ => ?_
                show signBool (decide (g' (x + v) = 1)) = _
                rw [hg'_shift_v x, h1, zmod2_add_decide]
                cases decide (g' x = 1) <;> rfl
            _ = -(∑ x : Fin n → F2, signBool (decide (g' x = 1))) := by rw [Finset.sum_neg_distrib]
        have hpos : (0 : ℤ) < (2 : ℤ) ^ (n - r) := by positivity
        change (∑ x : Fin n → F2, signBool (decide (g' x = 1))) = (2 : ℤ) ^ (n - r) at hsum
        omega
      let W : Submodule F2 (Fin n → F2) := LinearMap.ker (dotLin c1) ⊓ LinearMap.ker (dotLin c2)
      let eW : (F2 × F2) × W ≃ (Fin n → F2) :=
        { toFun := fun ⟨⟨α, β⟩, w⟩ => α • u + β • v + w.val
          invFun := fun x => ((dotProduct c2 x, dotProduct c1 x),
            ⟨x + dotProduct c2 x • u + dotProduct c1 x • v, by
              refine ⟨?_, ?_⟩
              · show dotProduct c1 (x + dotProduct c2 x • u + dotProduct c1 x • v) = 0
                rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, hc1u, hc1v, smul_eq_mul, smul_eq_mul]
                simp [z2_add_self]
              · show dotProduct c2 (x + dotProduct c2 x • u + dotProduct c1 x • v) = 0
                rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, hc2u, hc2v, smul_eq_mul, smul_eq_mul]
                simp [z2_add_self]⟩)
          left_inv := fun ⟨⟨α, β⟩, ⟨w, hw1, hw2⟩⟩ => by
            have hw1' : dotProduct c1 w = 0 := hw1
            have hw2' : dotProduct c2 w = 0 := hw2
            have h1 : dotProduct c1 (α • u + β • v + w) = β := by
              rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, hc1u, hc1v, hw1']
              simp
            have h2 : dotProduct c2 (α • u + β • v + w) = α := by
              rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, hc2u, hc2v, hw2']
              simp
            apply Prod.ext
            · apply Prod.ext; exact h2; exact h1
            · apply Subtype.ext; dsimp only; rw [h1, h2]
              calc α • u + β • v + w + α • u + β • v
                  = (α • u + α • u) + (β • v + β • v) + w := by abel
                _ = w := by rw [zmod2_vec_add_self, zmod2_vec_add_self, add_zero, zero_add]
          right_inv := fun x => by
            dsimp only
            calc dotProduct c2 x • u + dotProduct c1 x • v + (x + dotProduct c2 x • u + dotProduct c1 x • v)
                = (dotProduct c2 x • u + dotProduct c2 x • u) + (dotProduct c1 x • v + dotProduct c1 x • v) + x := by abel
              _ = x := by rw [zmod2_vec_add_self, zmod2_vec_add_self, add_zero, zero_add] }
      have hg'_inv : ∀ (α β : F2) (w : W), g' (α • u + β • v + w.val) = g' w.val := by
        intro α β w
        rcases zmod2_cases α with rfl | rfl <;> rcases zmod2_cases β with rfl | rfl
        · simp
        · simp only [zero_smul, zero_add, one_smul]; rw [add_comm, hg'_shift_v, hgv0, add_zero]
        · simp only [one_smul, zero_smul, add_zero]; rw [add_comm, hg'_shift_u, hgu0, add_zero]
        · simp only [one_smul]
          calc g' (u + v + w.val) = g' ((w.val + u) + v) := by congr 1; abel
            _ = g' (w.val + u) := by rw [hg'_shift_v, hgv0, add_zero]
            _ = g' w.val := by rw [hg'_shift_u, hgu0, add_zero]
      have hsum_W : 4 * (∑ w : W, signBool (decide (g' w.val = 1))) = (2 : ℤ) ^ (n - r) := by
        rw [← hsum, ← Equiv.sum_comp eW, Fintype.sum_prod_type]
        have h4 : ∀ w : W, ∑ ab : F2 × F2, signBool (decide (g' (eW (ab, w)) = 1)) =
            4 * signBool (decide (g' w.val = 1)) := by
          intro w
          have hterm : ∀ ab : F2 × F2, signBool (decide (g' (eW (ab, w)) = 1)) = signBool (decide (g' w.val = 1)) :=
            fun ⟨α, β⟩ => by dsimp only [eW, Equiv.coe_fn_mk]; exact congrArg (fun x => signBool (decide (x = 1))) (hg'_inv α β w)
          simp_rw [hterm]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul]; norm_num
        rw [Finset.sum_comm]
        have hrew : (∑ w : W, ∑ ab : F2 × F2, signBool (decide (g' (eW (ab, w)) = 1))) =
            ∑ w : W, 4 * signBool (decide (g' w.val = 1)) := Finset.sum_congr rfl fun w _ => h4 w
        change _ = ∑ w : W, ∑ ab : F2 × F2, signBool (decide (g' (eW (ab, w)) = 1))
        rw [hrew, ← Finset.mul_sum]
      refine ⟨[], a, b, by simp, ?_⟩
      simp only [List.map_nil, List.sum_nil, add_zero, Nat.sub_zero]
      have hfx : ∀ x : Fin n → F2, f x + dotProduct a x + b = g' x + dotProduct c1 x * dotProduct c2 x := by
        intro x; dsimp only [g', f']
        have hz := z2_add_self (dotProduct c1 x * dotProduct c2 x)
        linear_combination -hz
      simp_rw [hfx]
      rw [← Equiv.sum_comp eW, Fintype.sum_prod_type, Finset.sum_comm]
      have hinner : ∀ w : W,
          (∑ ab : F2 × F2, signBool (decide (g' (eW (ab, w)) + dotProduct c1 (eW (ab, w)) * dotProduct c2 (eW (ab, w)) = 1))) =
          2 * signBool (decide (g' w.val = 1)) := by
        intro w
        have hterm : ∀ ab : F2 × F2,
            signBool (decide (g' (eW (ab, w)) + dotProduct c1 (eW (ab, w)) * dotProduct c2 (eW (ab, w)) = 1)) =
            signBool (decide (g' w.val = 1)) * signBool (decide (ab.2 * ab.1 = 1)) := by
          intro ⟨α, β⟩
          dsimp only [eW, Equiv.coe_fn_mk]
          have hw1' : dotProduct c1 w.val = 0 := w.property.1
          have hw2' : dotProduct c2 w.val = 0 := w.property.2
          have h1 : dotProduct c1 (α • u + β • v + w.val) = β := by
            rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, hc1u, hc1v, hw1']; simp
          have h2 : dotProduct c2 (α • u + β • v + w.val) = α := by
            rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, hc2u, hc2v, hw2']; simp
          have harg : g' (α • u + β • v + w.val) + dotProduct c1 (α • u + β • v + w.val) * dotProduct c2 (α • u + β • v + w.val) =
              g' w.val + β * α := by rw [hg'_inv α β w, h1, h2]
          rw [congrArg (fun x => signBool (decide (x = 1))) harg, zmod2_add_decide, signBool_xor]
        simp_rw [hterm, ← Finset.mul_sum]
        have h2 : (∑ ab : F2 × F2, signBool (decide (ab.2 * ab.1 = 1))) = 2 := by
          rw [Fintype.sum_prod_type]
          have hF : ∀ h : F2 → ℤ, (∑ x : F2, h x) = h 0 + h 1 := fun h => by
            have : (Finset.univ : Finset F2) = {0, 1} := by ext x; rcases zmod2_cases x with rfl | rfl <;> simp
            rw [this, Finset.sum_pair (by decide)]
          simp only [hF]; decide
        rw [h2, mul_comm]
      simp_rw [hinner, ← Finset.mul_sum]
      have hpow : (2 : ℤ) ^ (n - r) = 2 * (2 : ℤ) ^ (n - (r + 1)) := by
        rw [show n - r = (n - (r + 1)) + 1 by omega, pow_succ, mul_comm]
      omega

lemma flip_output_circuit (n : ℕ) (Q : Bool → (Fin n → F2) → F2) (C : Circuit)
    (hleg : legalGates (2 * (n + 1)) C.gates) (hout : C.output < 2 * (n + 1) + C.gates.length) :
    ∃ C' : Circuit, legalGates (2 * (n + 1)) C'.gates ∧ costGates C'.gates = costGates C.gates ∧
      C'.output < 2 * (n + 1) + C'.gates.length ∧
      ∀ t : Bool, scoreQ n Q C' t = -scoreQ n Q C t := by
  let k := n + 1
  let gs' := C.gates ++ [⟨.not, [C.output]⟩]
  have hleg' : legalGates (2 * k) gs' :=
    legalGates_snoc hleg (fun i hi => by simp at hi; subst hi; exact hout) ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  have hcost' : costGates gs' = costGates C.gates := costGates_snoc_zero C.gates _ (by simp)
  refine ⟨⟨gs', 2 * k + C.gates.length⟩, hleg', hcost', by simp [gs', k], fun t => ?_⟩
  dsimp only [scoreQ]
  rw [← neg_div, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  have heval : (Circuit.mk gs' (2 * k + C.gates.length)).eval (bitsOf k x ++ bitsOf k (Fin.cons (if t then 1 else 0) u)) =
      !(C.eval (bitsOf k x ++ bitsOf k (Fin.cons (if t then 1 else 0) u))) := by
    change (wiresOf (C.gates ++ [⟨.not, [C.output]⟩]) _).getD (2 * k + C.gates.length) false = _
    rw [wiresOf_snoc_last_eq C.gates ⟨.not, [C.output]⟩ _ (by simp [bitsOf_len]; omega)]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]; rfl
  rw [heval]
  cases C.eval (bitsOf k x ++ bitsOf k (Fin.cons (if t then 1 else 0) u)) <;>
    cases decide (dotProduct x (Fin.cons (if t then 1 else 0) u) + Q t u = 1) <;> norm_num

lemma flip_true_circuit (n : ℕ) (Q : Bool → (Fin n → F2) → F2) (C : Circuit)
    (hleg : legalGates (2 * (n + 1)) C.gates) (hout : C.output < 2 * (n + 1) + C.gates.length) :
    ∃ C' : Circuit, legalGates (2 * (n + 1)) C'.gates ∧ costGates C'.gates = costGates C.gates ∧
      C'.output < 2 * (n + 1) + C'.gates.length ∧
      scoreQ n Q C' false = scoreQ n Q C false ∧ scoreQ n Q C' true = -scoreQ n Q C true := by
  let k := n + 1
  have hstep := addXor_step (2 * k) C.gates C.output k hleg hout (by omega)
  let gs' := C.gates ++ [⟨.mod 2, [C.output, k]⟩, ⟨.not, [2 * k + C.gates.length]⟩]
  refine ⟨⟨gs', 2 * k + C.gates.length + 1⟩, hstep.1, hstep.2.1, by simp [gs', k]; omega, ?_, ?_⟩
  · dsimp only [scoreQ]; congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun u _ => ?_
    have hlen : (bitsOf k x ++ bitsOf k (Fin.cons (0 : F2) u)).length = 2 * k := by simp [bitsOf_len]; omega
    have heval : (Circuit.mk gs' (2 * k + C.gates.length + 1)).eval (bitsOf k x ++ bitsOf k (Fin.cons (0 : F2) u)) =
        C.eval (bitsOf k x ++ bitsOf k (Fin.cons (0 : F2) u)) := by
      change (wiresOf gs' _).getD (2 * k + C.gates.length + 1) false = _
      rw [hstep.2.2.2 _ hlen]
      have hk_wire : (wiresOf C.gates (bitsOf k x ++ bitsOf k (Fin.cons (0 : F2) u))).getD k false = false := by
        rw [wiresOf_getD_lt C.gates _ (by rw [hlen]; omega), bitsOf_concatVec]
        have h1 := bitsOf_getD (2 * k) (concatVec x (Fin.cons (0 : F2) u)) ⟨k, by omega⟩
        have hnot : ¬ (k < k) := lt_irrefl k
        simp only [concatVec, hnot, ↓reduceDIte, Nat.sub_self] at h1
        have h0 : (⟨0, by omega⟩ : Fin k) = 0 := rfl
        rw [h0, Fin.cons_zero] at h1
        simpa using h1
      rw [hk_wire, Bool.xor_false]; rfl
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [heval]
  · dsimp only [scoreQ]
    rw [← neg_div, ← Finset.sum_neg_distrib]; congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hlen : (bitsOf k x ++ bitsOf k (Fin.cons (1 : F2) u)).length = 2 * k := by simp [bitsOf_len]; omega
    have heval : (Circuit.mk gs' (2 * k + C.gates.length + 1)).eval (bitsOf k x ++ bitsOf k (Fin.cons (1 : F2) u)) =
        !(C.eval (bitsOf k x ++ bitsOf k (Fin.cons (1 : F2) u))) := by
      change (wiresOf gs' _).getD (2 * k + C.gates.length + 1) false = _
      rw [hstep.2.2.2 _ hlen]
      have hk_wire : (wiresOf C.gates (bitsOf k x ++ bitsOf k (Fin.cons (1 : F2) u))).getD k false = true := by
        rw [wiresOf_getD_lt C.gates _ (by rw [hlen]; omega), bitsOf_concatVec]
        have h1 := bitsOf_getD (2 * k) (concatVec x (Fin.cons (1 : F2) u)) ⟨k, by omega⟩
        have hnot : ¬ (k < k) := lt_irrefl k
        simp only [concatVec, hnot, ↓reduceDIte, Nat.sub_self] at h1
        have h0 : (⟨0, by omega⟩ : Fin k) = 0 := rfl
        rw [h0, Fin.cons_zero] at h1
        simpa using h1
      rw [hk_wire, Bool.xor_true]; rfl
    simp only [↓reduceIte]
    rw [heval]
    cases C.eval (bitsOf k x ++ bitsOf k (Fin.cons (1 : F2) u)) <;>
      cases decide (dotProduct x (Fin.cons (1 : F2) u) + Q true u = 1) <;> norm_num

lemma vertex_lt_k (n s : ℕ) (hs : s < n + 1) (Q : Bool → (Fin n → F2) → F2)
    (hQ : ∀ t, isQuad (Q t)) (t0 : Bool) :
    ∃ C : Circuit, legalGates (2 * (n + 1)) C.gates ∧ costGates C.gates ≤ s ∧
      C.output < 2 * (n + 1) + C.gates.length ∧
      scoreQ n Q C t0 = 1 / (2 : ℚ) ^ (n - s) ∧ scoreQ n Q C (!t0) = 0 := by
  let k := n + 1
  rcases hQ t0 with ⟨qb, qa, qM, hq_eq⟩
  let b0 : F2 := if t0 then 1 else 0
  let embS : Fin s → Fin n := fun i => ⟨i.val, by omega⟩
  let pad : (Fin n → F2) → (Fin n → F2) := fun u j => if j.val < s then u j else 0
  let c0 : Fin (2 * k) → F2 :=
    concatVec (Pi.single 0 b0) (Fin.cons 0 (fun j => if j.val < s then qa j else 0))
  let cA : Fin s → Fin (2 * k) → F2 := fun i => concatVec 0 (Pi.single (embS i).succ 1)
  let cB : Fin s → Fin (2 * k) → F2 := fun i =>
    concatVec (Pi.single (embS i).succ 1) (Fin.cons 0 (fun j => if j.val < s then qM (embS i) j else 0))
  have hnil : legalGates (2 * k) [] := ⟨fun j hj => by simp at hj, fun h hh => by simp at hh⟩
  rcases appendAffine_spec (2 * k) [] c0 qb hnil with ⟨_, _, h0leg, h0cost, h0lt, h0sem⟩
  set res0 := appendAffine (2 * k) [] c0 qb
  rcases appendSumProdsLoop_spec (2 * k) s cA cB (fun _ => 0) (fun _ => 0) s (le_refl s) res0.1 res0.2 h0leg h0lt with
    ⟨_, _, hleg, hcost, hlt, hsem⟩
  set res := appendSumProdsLoop (2 * k) s cA cB (fun _ => 0) (fun _ => 0) s (le_refl s) res0.1 res0.2
  refine ⟨⟨res.1, res.2⟩, hleg, ?_, hlt, ?_, ?_⟩
  · have hc0 : costGates ([] : List Gate) = 0 := by simp [costGates]
    dsimp only [res, res0] at hcost h0cost ⊢; omega
  all_goals
    have hCe : ∀ (x : Fin k → F2) (b : F2) (u : Fin n → F2),
        (Circuit.mk res.1 res.2).eval (bitsOf k x ++ bitsOf k (Fin.cons b u)) =
          decide (x 0 * b0 + Q t0 (pad u) + ∑ i : Fin s, u (embS i) * x (embS i).succ = 1) := by
      intro x b u
      rw [bitsOf_concatVec]
      change (wiresOf res.1 (bitsOf (2 * k) (concatVec x (Fin.cons b u)))).getD res.2 false = _
      rw [hsem (concatVec x (Fin.cons b u)), h0sem (concatVec x (Fin.cons b u))]
      have huniv : Finset.univ.filter (fun i : Fin s => i.val < s) = Finset.univ := by ext i; simp
      rw [huniv, ← zmod2_add_decide]
      congr 1
      have h0 : dotProduct c0 (concatVec x (Fin.cons b u)) + qb =
          x 0 * b0 + qb + ∑ i : Fin n, qa i * pad u i := by
        simp only [c0, dotProduct_concatVec, single_dotProduct]
        have hdot_y : dotProduct (Fin.cons (0 : F2) (fun j => if j.val < s then qa j else 0)) (Fin.cons b u) =
            ∑ i : Fin n, qa i * pad u i := by
          rw [dotProduct, Fin.sum_univ_succ]
          simp only [Fin.cons_zero, zero_mul, zero_add, Fin.cons_succ]
          refine Finset.sum_congr rfl fun j _ => by dsimp only [pad]; split_ifs <;> ring
        rw [hdot_y]; ring
      have hprod : ∀ i : Fin s,
          (dotProduct (cA i) (concatVec x (Fin.cons b u)) + 0) * (dotProduct (cB i) (concatVec x (Fin.cons b u)) + 0) =
          u (embS i) * x (embS i).succ + ∑ j : Fin n, qM (embS i) j * pad u (embS i) * pad u j := by
        intro i
        simp only [cA, cB, dotProduct_concatVec, zero_dotProduct, zero_add, add_zero, single_dotProduct, one_mul, Fin.cons_succ]
        have hdot_B : dotProduct (Fin.cons (0 : F2) (fun j => if j.val < s then qM (embS i) j else 0)) (Fin.cons b u) =
            ∑ j : Fin n, qM (embS i) j * pad u j := by
          rw [dotProduct, Fin.sum_univ_succ]
          simp only [Fin.cons_zero, zero_mul, zero_add, Fin.cons_succ]
          refine Finset.sum_congr rfl fun j _ => by dsimp only [pad]; split_ifs <;> ring
        rw [hdot_B, mul_add, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        have hi : (embS i).val < s := i.isLt
        dsimp only [pad]; simp only [hi, ↓reduceIte]; ring
      have hqM : (∑ i : Fin n, ∑ j : Fin n, qM i j * pad u i * pad u j) =
          ∑ i : Fin s, ∑ j : Fin n, qM (embS i) j * pad u (embS i) * pad u j := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => i.val < s)]
        have hzero : ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ i.val < s), ∑ j : Fin n, qM i j * pad u i * pad u j = 0 := by
          refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j _ => ?_
          have hnot : ¬ i.val < s := (Finset.mem_filter.mp hi).2
          simp [pad, hnot]
        rw [hzero, add_zero]
        symm
        refine Finset.sum_bij (fun i _ => embS i) (fun i _ => by simp [embS, i.isLt])
          (fun i1 _ i2 _ h => Fin.ext (congrArg (Fin.val : Fin n → ℕ) h))
          (fun j hj => ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, Fin.ext rfl⟩)
          (fun _ _ => rfl)
      rw [h0, hq_eq (pad u), hqM]
      simp_rw [hprod, Finset.sum_add_distrib]
      unfold dotProduct; ring
    have hscore_eval : ∀ t : Bool,
        scoreQ n Q ⟨res.1, res.2⟩ t = if t = t0 then 1 / (2 : ℚ) ^ (n - s) else 0 := by
      intro t
      dsimp only [scoreQ]
      have hnum_int : (∑ x : Fin k → F2, ∑ u : Fin n → F2,
          let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
          if (Circuit.mk res.1 res.2).eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + Q t u = 1)
          then (1 : ℚ) else -1) =
          ((∑ u : Fin n → F2, ∑ x : Fin k → F2,
            let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
            if (Circuit.mk res.1 res.2).eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + Q t u = 1)
            then (1 : ℤ) else -1 : ℤ) : ℚ) := by
        rw [Finset.sum_comm]; push_cast
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x _ => by split_ifs <;> norm_num
      rw [hnum_int]
      have hinner : ∀ u : Fin n → F2,
          (∑ x : Fin k → F2,
            let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
            if (Circuit.mk res.1 res.2).eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + Q t u = 1)
            then (1 : ℤ) else -1) =
          if t = t0 ∧ ∀ j : Fin n, s ≤ j.val → u j = 0 then (2 : ℤ) ^ k else 0 := by
        intro u
        let bt : F2 := if t then 1 else 0
        let w : Fin k → F2 := Fin.cons (b0 + bt) (fun j => if j.val < s then 0 else u j)
        have hterm : ∀ x : Fin k → F2,
            (if (Circuit.mk res.1 res.2).eval (bitsOf k x ++ bitsOf k (Fin.cons bt u)) =
                decide (dotProduct x (Fin.cons bt u) + Q t u = 1) then (1 : ℤ) else -1) =
            signBool (decide (dotProduct w x = 1)) * signBool (decide (Q t0 (pad u) + Q t u = 1)) := by
          intro x
          rw [hCe x bt u, ← signBool_xor, ← zmod2_add_decide]
          have hif : ∀ a b : Bool, (if a = b then (1 : ℤ) else -1) = signBool (Bool.xor a b) := by
            intro a b; cases a <;> cases b <;> rfl
          rw [hif, ← zmod2_add_decide]
          apply congrArg (fun x => signBool (decide (x = 1)))
          have hdot_x : dotProduct x (Fin.cons bt u) =
              x 0 * bt + (∑ i : Fin s, u (embS i) * x (embS i).succ) +
              ∑ j : Fin n, (if j.val < s then 0 else u j) * x j.succ := by
            rw [dotProduct, Fin.sum_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [add_assoc]
            congr 1
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => j.val < s)]
            congr 1
            · symm
              refine Finset.sum_bij (fun i _ => embS i) (fun i _ => by simp [embS, i.isLt])
                (fun i1 _ i2 _ h => Fin.ext (congrArg (Fin.val : Fin n → ℕ) h))
                (fun j hj => ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, Fin.ext rfl⟩)
                (fun i _ => mul_comm _ _)
            · symm
              rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => j.val < s)]
              have h0 : ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < s), (if j.val < s then (0 : F2) else u j) * x j.succ = 0 :=
                Finset.sum_eq_zero fun j hj => by simp [(Finset.mem_filter.mp hj).2]
              rw [h0, zero_add]
              refine Finset.sum_congr rfl fun j hj => by simp [(Finset.mem_filter.mp hj).2, mul_comm]
          have hdot_w : dotProduct w x = x 0 * (b0 + bt) + ∑ j : Fin n, (if j.val < s then 0 else u j) * x j.succ := by
            rw [dotProduct, Fin.sum_univ_succ]
            simp only [w, Fin.cons_zero, Fin.cons_succ]; ring
          rw [hdot_x, hdot_w]
          have hz := z2_add_self (∑ i : Fin s, u (embS i) * x (embS i).succ)
          linear_combination hz
        rw [show (∑ x : Fin k → F2,
            let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
            if (Circuit.mk res.1 res.2).eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + Q t u = 1)
            then (1 : ℤ) else -1) =
            ∑ x : Fin k → F2, signBool (decide (dotProduct w x = 1)) * signBool (decide (Q t0 (pad u) + Q t u = 1))
          from Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_mul]
        by_cases hcond : t = t0 ∧ ∀ j : Fin n, s ≤ j.val → u j = 0
        · rw [if_pos hcond]
          have hw0 : w = 0 := by
            funext j
            refine Fin.cases ?_ (fun i => ?_) j
            · simp [w, b0, bt, hcond.1, z2_add_self]
            · simp only [w, Fin.cons_succ, Pi.zero_apply]
              split_ifs with hlt
              · rfl
              · exact hcond.2 i (by omega)
          have hpad : pad u = u := by
            funext i; dsimp only [pad]; split_ifs with hlt
            · rfl
            · exact (hcond.2 i (by omega)).symm
          rw [hw0, hcond.1, hpad, z2_add_self]
          simp_rw [zero_dotProduct]
          change (∑ _x : Fin k → F2, (1 : ℤ)) * 1 = (2 : ℤ) ^ k
          simp [ZMod.card]
        · rw [if_neg hcond]
          have hwne : w ≠ 0 := by
            intro hw0
            apply hcond
            constructor
            · have h0 := congrFun hw0 0
              simp only [w, Fin.cons_zero, Pi.zero_apply] at h0
              cases t <;> cases t0 <;> simp [b0, bt] at h0 ⊢
            · intro j hj
              have h1 := congrFun hw0 j.succ
              have hnot : ¬ (j.val < s) := by omega
              simpa [w, hnot] using h1
          rw [sum_sign_dot_univ w hwne, zero_mul]
      simp_rw [hinner]
      by_cases ht : t = t0
      · simp only [ht, true_and, ↓reduceIte, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have hcard : (Finset.univ.filter (fun u : Fin n → F2 => ∀ j : Fin n, s ≤ j.val → u j = 0)).card = 2 ^ s := by
          let eS : (Fin s → F2) ≃ {u : Fin n → F2 // ∀ j : Fin n, s ≤ j.val → u j = 0} :=
            { toFun := fun v => ⟨fun j => if h : j.val < s then v ⟨j.val, h⟩ else 0, fun j hj => by simp [show ¬ j.val < s by omega]⟩
              invFun := fun u i => u.val (embS i)
              left_inv := fun v => by funext i; simp [embS, i.isLt]
              right_inv := fun ⟨u, hu⟩ => Subtype.ext (funext fun j => by
                by_cases h : j.val < s
                · simp [h, embS]
                · simp [h, hu j (by omega)]) }
          rw [← Fintype.card_subtype, ← Fintype.card_congr eS]
          simp [ZMod.card]
        rw [hcard]; push_cast
        have hpow : (2 : ℚ) ^ (k + n) = (2 : ℚ) ^ s * (2 : ℚ) ^ k * (2 : ℚ) ^ (n - s) := by
          rw [← pow_add, ← pow_add, show s + k + (n - s) = k + n by omega]
        rw [hpow]; field_simp
      · simp only [ht, false_and, ↓reduceIte, Finset.sum_const_zero, Int.cast_zero, zero_div]
  · simpa using hscore_eval t0
  · have hne : (!t0) ≠ t0 := by cases t0 <;> decide
    simpa [hne] using hscore_eval (!t0)

lemma vertex_ge_k (n r s : ℕ) (hs : n + 1 ≤ s) (Q : Bool → (Fin n → F2) → F2)
    (hQ : ∀ t, isQuad (Q t))
    (M : Matrix (Fin n) (Fin n) F2) (hrk : M.rank = 2 * r)
    (hd : ∀ u v, (Q false (u + v) + Q true (u + v)) + (Q false u + Q true u) +
      (Q false v + Q true v) + (Q false 0 + Q true 0) = dotProduct u (M.mulVec v))
    (t0 : Bool) :
    ∃ C : Circuit, legalGates (2 * (n + 1)) C.gates ∧ costGates C.gates ≤ s ∧
      C.output < 2 * (n + 1) + C.gates.length ∧
      scoreQ n Q C t0 = 1 ∧ scoreQ n Q C (!t0) = 1 / (2 : ℚ) ^ (r - (s - (n + 1))) := by
  let k := n + 1
  let c := s - k
  have hd_t0 : ∀ u v, (Q t0 (u + v) + Q (!t0) (u + v)) + (Q t0 u + Q (!t0) u) +
      (Q t0 v + Q (!t0) v) + (Q t0 0 + Q (!t0) 0) = dotProduct u (M.mulVec v) := by
    intro u v; cases t0
    · exact hd u v
    · simp only [Bool.not_true]; have h := hd u v; linear_combination h
  obtain ⟨ps, a_d, b_d, hps_len, hsum_d⟩ := symplectic_approx r c (fun u => Q t0 u + Q (!t0) u) M hrk hd_t0
  rcases hQ t0 with ⟨qb, qa, qM, hq_eq⟩
  let m := ps.length
  let cP1 : Fin m → Fin (2 * k) → F2 := fun i => concatVec 0 (Fin.cons 0 (ps.get i).1)
  let cP2 : Fin m → Fin (2 * k) → F2 := fun i => concatVec 0 (Fin.cons 0 (ps.get i).2)
  let cW0 : Fin (2 * k) → F2 := concatVec (Pi.single 0 1) (Fin.cons 0 a_d)
  have hnil : legalGates (2 * k) [] := ⟨fun j hj => by simp at hj, fun h hh => by simp at hh⟩
  rcases appendAffine_spec (2 * k) [] cW0 b_d hnil with ⟨_, _, hW0leg, hW0cost, hW0lt, hW0sem⟩
  set resW0 := appendAffine (2 * k) [] cW0 b_d
  rcases appendSumProdsLoop_spec (2 * k) m cP1 cP2 (fun _ => 0) (fun _ => 0) m (le_refl m) resW0.1 resW0.2 hW0leg hW0lt with
    ⟨_, _, hWleg, hWcost, hWlt, hWsem⟩
  set resW := appendSumProdsLoop (2 * k) m cP1 cP2 (fun _ => 0) (fun _ => 0) m (le_refl m) resW0.1 resW0.2
  let selB : F2 := if t0 then 1 else 0
  rcases appendAffine_spec (2 * k) resW.1 (concatVec 0 (Pi.single 0 1)) selB hWleg with
    ⟨extS, hSeq, hSleg, hScost, hSlt, hSsem⟩
  set resS := appendAffine (2 * k) resW.1 (concatVec 0 (Pi.single 0 1)) selB
  have hWltS : resW.2 < 2 * k + resS.1.length := by rw [hSeq, List.length_append]; omega
  let gs1 := resS.1 ++ [⟨.and, [resS.2, resW.2]⟩]
  let wSel := 2 * k + resS.1.length
  have hleg1 : legalGates (2 * k) gs1 :=
    legalGates_snoc hSleg (fun i hi => by simp at hi; rcases hi with rfl | rfl; exact hSlt; exact hWltS)
      ⟨by simp, Or.inl rfl⟩
  have hcost1 : costGates gs1 = costGates resS.1 + 1 :=
    costGates_snoc_one resS.1 _ ⟨Or.inl rfl, rfl⟩
  let cLin : Fin (2 * k) → F2 := concatVec (Pi.single 0 selB) (Fin.cons 0 qa)
  rcases appendAffine_spec (2 * k) gs1 cLin qb hleg1 with ⟨extL, hLeq, hLleg, hLcost, hLlt, hLsem⟩
  set resL := appendAffine (2 * k) gs1 cLin qb
  have hwSel_ltL : wSel < 2 * k + resL.1.length := by rw [hLeq, List.length_append]; simp [gs1, wSel]; omega
  have hxor := addXor_step (2 * k) resL.1 resL.2 wSel hLleg hLlt hwSel_ltL
  let gs2 := resL.1 ++ [⟨.mod 2, [resL.2, wSel]⟩, ⟨.not, [2 * k + resL.1.length]⟩]
  let wBase := 2 * k + resL.1.length + 1
  have hwBase_lt : wBase < 2 * k + gs2.length := by simp [gs2, wBase]; omega
  let cU : Fin n → Fin (2 * k) → F2 := fun i => concatVec 0 (Pi.single i.succ 1)
  let cV : Fin n → Fin (2 * k) → F2 := fun i => concatVec (Pi.single i.succ 1) (Fin.cons 0 (fun j => qM i j))
  rcases appendSumProdsLoop_spec (2 * k) n cU cV (fun _ => 0) (fun _ => 0) n (le_refl n) gs2 wBase hxor.1 hwBase_lt with
    ⟨_, _, hFleg, hFcost, hFlt, hFsem⟩
  set resF := appendSumProdsLoop (2 * k) n cU cV (fun _ => 0) (fun _ => 0) n (le_refl n) gs2 wBase
  let dApprox : (Fin n → F2) → F2 := fun u =>
    (ps.map (fun p => dotProduct p.1 u * dotProduct p.2 u)).sum + dotProduct a_d u + b_d
  have hCe : ∀ (x : Fin k → F2) (t : Bool) (u : Fin n → F2),
      let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
      (Circuit.mk resF.1 resF.2).eval (bitsOf k x ++ bitsOf k y) =
        decide (dotProduct x y + Q t0 u + (if t = t0 then 0 else dApprox u) = 1) := by
      intro x t u y
      set v := concatVec x y
      rw [bitsOf_concatVec]
      change (wiresOf resF.1 (bitsOf (2 * k) v)).getD resF.2 false = _
      rw [hFsem v]
      have huniv_n : Finset.univ.filter (fun i : Fin n => i.val < n) = Finset.univ := by ext i; simp
      have huniv_m : Finset.univ.filter (fun i : Fin m => i.val < m) = Finset.univ := by ext i; simp
      rw [huniv_n]
      have hWval : (wiresOf resW.1 (bitsOf (2 * k) v)).getD resW.2 false =
          decide (x 0 + dApprox u = 1) := by
        rw [hWsem v, hW0sem v, huniv_m, ← zmod2_add_decide]
        congr 1
        have hW0 : dotProduct cW0 v + b_d = x 0 + dotProduct a_d u + b_d := by
          simp only [cW0, v, dotProduct_concatVec, single_dotProduct, one_mul]
          have : dotProduct (Fin.cons (0 : F2) a_d) y = dotProduct a_d u := by
            rw [dotProduct, Fin.sum_univ_succ]; simp [y, dotProduct]
          rw [this]
        have hps_sum : (∑ i : Fin m, (dotProduct (cP1 i) v + 0) * (dotProduct (cP2 i) v + 0)) =
            (ps.map (fun p => dotProduct p.1 u * dotProduct p.2 u)).sum := by
          have h1 : ∀ i : Fin m, (dotProduct (cP1 i) v + 0) * (dotProduct (cP2 i) v + 0) =
              dotProduct (ps.get i).1 u * dotProduct (ps.get i).2 u := by
            intro i
            simp only [cP1, cP2, v, dotProduct_concatVec, zero_dotProduct, zero_add, add_zero]
            have hA : dotProduct (Fin.cons (0 : F2) (ps.get i).1) y = dotProduct (ps.get i).1 u := by
              rw [dotProduct, Fin.sum_univ_succ]; simp [y, dotProduct]
            have hB : dotProduct (Fin.cons (0 : F2) (ps.get i).2) y = dotProduct (ps.get i).2 u := by
              rw [dotProduct, Fin.sum_univ_succ]; simp [y, dotProduct]
            rw [hA, hB]
          simp_rw [h1]
          have hlsum : ∀ (l : List ((Fin n → F2) × (Fin n → F2))),
              (∑ i : Fin l.length, dotProduct (l.get i).1 u * dotProduct (l.get i).2 u) =
              (l.map (fun p => dotProduct p.1 u * dotProduct p.2 u)).sum := by
            intro l
            induction l with
            | nil => simp
            | cons p tl ih =>
                simp only [List.length_cons, List.map_cons, List.sum_cons, Fin.sum_univ_succ,
                  List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_zero, Fin.val_succ]
                simpa [List.get_eq_getElem] using congrArg (dotProduct p.1 u * dotProduct p.2 u + ·) ih
          exact hlsum ps
        rw [hW0, hps_sum]; dsimp only [dApprox]; ring
      have hSval : (wiresOf resS.1 (bitsOf (2 * k) v)).getD resS.2 false =
          decide ((if t = t0 then (0 : F2) else 1) = 1) := by
        rw [hSsem v]
        simp only [v, dotProduct_concatVec, zero_dotProduct, zero_add, single_dotProduct, one_mul, y, Fin.cons_zero]
        cases t <;> cases t0 <;> simp [selB] <;> decide
      have hwSel_val : (wiresOf gs1 (bitsOf (2 * k) v)).getD wSel false =
          decide ((if t = t0 then (0 : F2) else 1) * (x 0 + dApprox u) = 1) := by
        change (wiresOf (resS.1 ++ [⟨.and, [resS.2, resW.2]⟩]) _).getD (2 * k + resS.1.length) false = _
        rw [wiresOf_snoc_last_eq resS.1 _ _ (bitsOf_len (2 * k) v)]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        have hW_in_S : (wiresOf resS.1 (bitsOf (2 * k) v)).getD resW.2 false = decide (x 0 + dApprox u = 1) := by
          rw [hSeq, wiresOf_append_getD_lt resW.1 extS _ (by rw [bitsOf_len]; exact hWlt)]
          exact hWval
        rw [hSval, hW_in_S, zmod2_mul_decide]
      have hwBase_val : (wiresOf gs2 (bitsOf (2 * k) v)).getD wBase false =
          decide (selB * x 0 + dotProduct qa u + qb + (if t = t0 then (0 : F2) else 1) * (x 0 + dApprox u) = 1) := by
        change (wiresOf (resL.1 ++ [⟨.mod 2, [resL.2, wSel]⟩, ⟨.not, [2 * k + resL.1.length]⟩]) _).getD
          (2 * k + resL.1.length + 1) false = _
        rw [hxor.2.2.2 _ (bitsOf_len (2 * k) v), hLsem v]
        have hwSel_in_L : (wiresOf resL.1 (bitsOf (2 * k) v)).getD wSel false =
            decide ((if t = t0 then (0 : F2) else 1) * (x 0 + dApprox u) = 1) := by
          rw [hLeq, wiresOf_append_getD_lt gs1 extL _ (by rw [bitsOf_len]; simp [gs1, wSel])]
          exact hwSel_val
        rw [hwSel_in_L, ← zmod2_add_decide]
        congr 1
        have hLin : dotProduct cLin v = selB * x 0 + dotProduct qa u := by
          simp only [cLin, v, dotProduct_concatVec, single_dotProduct]
          congr 1
          rw [dotProduct, Fin.sum_univ_succ]; simp [y, dotProduct]
        rw [hLin]
      rw [hwBase_val, ← zmod2_add_decide]
      apply congrArg (fun x => decide (x = 1))
      have hUprod : ∀ i : Fin n, (dotProduct (cU i) v + 0) * (dotProduct (cV i) v + 0) =
          u i * x i.succ + ∑ j : Fin n, qM i j * u i * u j := by
        intro i
        simp only [cU, cV, v, dotProduct_concatVec, zero_dotProduct, zero_add, add_zero, single_dotProduct, one_mul, y, Fin.cons_succ]
        have hdot_q : dotProduct (Fin.cons (0 : F2) (fun j => qM i j)) (Fin.cons (if t then 1 else 0) u) =
            ∑ j : Fin n, qM i j * u j := by
          rw [dotProduct, Fin.sum_univ_succ]; simp [dotProduct]
        rw [hdot_q, mul_add, Finset.mul_sum]
        congr 1; refine Finset.sum_congr rfl fun j _ => by ring
      simp_rw [hUprod, Finset.sum_add_distrib]
      have hdot_xy : dotProduct x y = x 0 * (if t then 1 else 0) + ∑ i : Fin n, u i * x i.succ := by
        rw [dotProduct, Fin.sum_univ_succ]; simp only [y, Fin.cons_zero, Fin.cons_succ]
        congr 1; refine Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [hdot_xy, hq_eq u]
      have hsel_eq : selB * x 0 + (if t = t0 then (0 : F2) else 1) * x 0 = x 0 * (if t then 1 else 0) := by
        cases t <;> cases t0 <;> simp only [selB, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, zero_mul, one_mul, zero_add, add_zero, mul_zero, mul_one]
        exact z2_add_self (x 0)
      by_cases ht : t = t0
      · simp only [ht, ↓reduceIte, zero_mul, add_zero] at hsel_eq ⊢
        linear_combination hsel_eq
      · simp only [ht, ↓reduceIte, one_mul] at hsel_eq ⊢
        linear_combination hsel_eq
  have hscore_eval : ∀ t : Bool,
      scoreQ n Q ⟨resF.1, resF.2⟩ t = if t = t0 then 1 else 1 / (2 : ℚ) ^ (r - c) := by
    intro t
    dsimp only [scoreQ]
    have hnum_int : (∑ x : Fin k → F2, ∑ u : Fin n → F2,
        let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
        if (Circuit.mk resF.1 resF.2).eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + Q t u = 1)
        then (1 : ℚ) else -1) =
        ((∑ x : Fin k → F2, ∑ u : Fin n → F2,
          let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
          if (Circuit.mk resF.1 resF.2).eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + Q t u = 1)
          then (1 : ℤ) else -1 : ℤ) : ℚ) := by
      push_cast; refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun u _ => by split_ifs <;> norm_num
    rw [hnum_int]
    by_cases ht : t = t0
    · subst ht
      simp only [↓reduceIte]
      have h1 : ∀ (x : Fin k → F2) (u : Fin n → F2),
          (if (Circuit.mk resF.1 resF.2).eval (bitsOf k x ++ bitsOf k (Fin.cons (if t then 1 else 0) u)) =
              decide (dotProduct x (Fin.cons (if t then 1 else 0) u) + Q t u = 1)
            then (1 : ℤ) else -1) = 1 := by
        intro x u; rw [hCe x t u]; simp
      have hsum1 : (∑ x : Fin k → F2, ∑ u : Fin n → F2,
          let y : Fin k → F2 := Fin.cons (if t then 1 else 0) u
          if (Circuit.mk resF.1 resF.2).eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + Q t u = 1)
          then (1 : ℤ) else -1) = ∑ _x : Fin k → F2, ∑ _u : Fin n → F2, (1 : ℤ) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun u _ => h1 x u
      rw [hsum1]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        Fintype.card_fun, Fintype.card_fin, ZMod.card]
      push_cast; rw [← pow_add, div_self (by positivity)]
    · have ht' : t = !t0 := by cases t <;> cases t0 <;> first | exact absurd rfl ht | rfl
      have hnt : (!t0) ≠ t0 := by cases t0 <;> decide
      simp only [ht, ↓reduceIte]
      have hterm : ∀ (x : Fin k → F2) (u : Fin n → F2),
          (if (Circuit.mk resF.1 resF.2).eval (bitsOf k x ++ bitsOf k (Fin.cons (if t then 1 else 0) u)) =
              decide (dotProduct x (Fin.cons (if t then 1 else 0) u) + Q t u = 1)
            then (1 : ℤ) else -1) =
          signBool (decide ((Q t0 u + Q (!t0) u) + dApprox u = 1)) := by
        intro x u
        rw [hCe x t u]; simp only [ht, ↓reduceIte, ht', hnt]
        have hif : ∀ a b : Bool, (if a = b then (1 : ℤ) else -1) = signBool (Bool.xor a b) := by
          intro a b; cases a <;> cases b <;> rfl
        rw [hif, ← zmod2_add_decide]
        apply congrArg (fun x => signBool (decide (x = 1)))
        have hz := z2_add_self (dotProduct x (Fin.cons (if !t0 then 1 else 0) u))
        linear_combination hz
      simp_rw [hterm]
      have hsum_u : (∑ u : Fin n → F2, signBool (decide ((Q t0 u + Q (!t0) u) + dApprox u = 1))) =
          (2 : ℤ) ^ (n - (r - c)) := by
        have : ∀ u, (Q t0 u + Q (!t0) u) + dApprox u =
            (Q t0 u + Q (!t0) u) + (ps.map (fun p => dotProduct p.1 u * dotProduct p.2 u)).sum +
            dotProduct a_d u + b_d := fun u => by dsimp only [dApprox]; ring
        simp_rw [this]; exact hsum_d
      simp only [hsum_u, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fun, Fintype.card_fin, ZMod.card]
      push_cast
      have h2r_le_n : 2 * r ≤ n := by have := rank_add_ker_mat M; omega
      have hpow : (2 : ℚ) ^ (k + n) = (2 : ℚ) ^ k * (2 : ℚ) ^ (n - (r - c)) * (2 : ℚ) ^ (r - c) := by
        rw [← pow_add, ← pow_add, show k + (n - (r - c)) + (r - c) = k + n by omega]
      rw [hpow]; field_simp
  refine ⟨⟨resF.1, resF.2⟩, hFleg, ?_, hFlt, ?_, ?_⟩
  · have hc0 : costGates ([] : List Gate) = 0 := by simp [costGates]
    have hxor_cost : costGates gs2 = costGates resL.1 := hxor.2.1
    rw [hFcost, hxor_cost, hLcost, hcost1, hScost, hWcost, hW0cost, hc0, zero_add]
    dsimp only [m, c, k] at hps_len ⊢
    omega
  · simpa using hscore_eval t0
  · have hne : (!t0) ≠ t0 := by cases t0 <;> decide
    simpa [hne] using hscore_eval (!t0)

lemma region_to_mixture (n r s : ℕ) (Q : Bool → (Fin n → F2) → F2) (hQ : ∀ t, isQuad (Q t))
    (M : Matrix (Fin n) (Fin n) F2) (hrk : M.rank = 2 * r)
    (hd : ∀ u v, (Q false (u + v) + Q true (u + v)) + (Q false u + Q true u) +
      (Q false v + Q true v) + (Q false 0 + Q true 0) = dotProduct u (M.mulVec v))
    (v : Bool → ℚ) :
    let k := n + 1
    let rho : ℚ := if s < k then 1 / 2 ^ (n - s) else 1
    let total : ℚ := if s < k then rho else 1 + 1 / 2 ^ (r - (s - k))
    |v false| ≤ rho → |v true| ≤ rho → |v false| + |v true| ≤ total →
    ∃ (C : Fin 3 → Circuit) (p : Fin 3 → ℚ),
      (∀ i, legalGates (2 * k) (C i).gates ∧ costGates (C i).gates ≤ s ∧ 0 ≤ p i) ∧
      (∑ i, p i) = 1 ∧ ∀ t, v t = ∑ i, p i * scoreQ n Q (C i) t := by
  intro k rho total hvF hvT hvSum
  have mk_signed : ∀ (C : Circuit), legalGates (2 * k) C.gates → costGates C.gates ≤ s →
      C.output < 2 * k + C.gates.length → ∀ (sf st : Bool),
      ∃ C' : Circuit, legalGates (2 * k) C'.gates ∧ costGates C'.gates ≤ s ∧
        scoreQ n Q C' false = (if sf then -1 else 1) * scoreQ n Q C false ∧
        scoreQ n Q C' true = (if st then -1 else 1) * scoreQ n Q C true := by
    intro C hleg hcost hout sf st
    cases sf <;> cases st
    · exact ⟨C, hleg, hcost, by simp, by simp⟩
    · obtain ⟨C', h1, h2, _, h3, h4⟩ := flip_true_circuit n Q C hleg hout
      exact ⟨C', h1, by omega, by simp [h3], by simp [h4]⟩
    · obtain ⟨C1, h1, h2, ho1, h3, h4⟩ := flip_true_circuit n Q C hleg hout
      obtain ⟨C2, h1', h2', _, h3'⟩ := flip_output_circuit n Q C1 h1 ho1
      exact ⟨C2, h1', by omega, by simp [h3', h3], by simp [h3', h4]⟩
    · obtain ⟨C', h1, h2, _, h3⟩ := flip_output_circuit n Q C hleg hout
      exact ⟨C', h1, by omega, by simp [h3], by simp [h3]⟩
  by_cases hsk : s < k
  · have hrho_eq : rho = 1 / (2 : ℚ) ^ (n - s) := if_pos hsk
    have htot_eq : total = rho := if_pos hsk
    have hrho_pos : (0 : ℚ) < rho := by rw [hrho_eq]; positivity
    obtain ⟨CF, hCF1, hCF2, hCFo, hCFf, hCFt⟩ := vertex_lt_k n s hsk Q hQ false
    obtain ⟨CT, hCT1, hCT2, hCTo, hCTt, hCTf⟩ := vertex_lt_k n s hsk Q hQ true
    simp only [Bool.not_false, Bool.not_true] at hCFt hCTf
    let sf : Bool := decide (v false < 0)
    let st : Bool := decide (v true < 0)
    obtain ⟨C0, hC01, hC02, hC0f, hC0t⟩ := mk_signed CF hCF1 hCF2 hCFo sf false
    obtain ⟨C1, hC11, hC12, hC1f, hC1t⟩ := mk_signed CT hCT1 hCT2 hCTo false st
    obtain ⟨C2, hC21, hC22, hC2f, hC2t⟩ := mk_signed CF hCF1 hCF2 hCFo (!sf) false
    let p1 : ℚ := |v true| / rho
    let p2 : ℚ := (1 - |v false| / rho - |v true| / rho) / 2
    let p0 : ℚ := |v false| / rho + p2
    have hsum_le1 : |v false| / rho + |v true| / rho ≤ 1 := by
      rw [← add_div, div_le_one hrho_pos]; linarith
    refine ⟨fun i => if i = 0 then C0 else if i = 1 then C1 else C2,
            fun i => if i = 0 then p0 else if i = 1 then p1 else p2, ?_, ?_, ?_⟩
    · intro i; fin_cases i
      · simp only [Fin.zero_eta, ↓reduceIte]
        exact ⟨hC01, hC02, by dsimp only [p0, p2]; linarith [div_nonneg (abs_nonneg (v false)) (le_of_lt hrho_pos)]⟩
      · simp only [Fin.mk_one, Fin.one_eq_zero_iff, Nat.reduceEqDiff, ↓reduceIte]
        exact ⟨hC11, hC12, div_nonneg (abs_nonneg (v true)) (le_of_lt hrho_pos)⟩
      · simp only [Fin.reduceFinMk]
        change legalGates (2 * k) (if (2 : Fin 3) = 0 then C0 else if (2 : Fin 3) = 1 then C1 else C2).gates ∧
          costGates (if (2 : Fin 3) = 0 then C0 else if (2 : Fin 3) = 1 then C1 else C2).gates ≤ s ∧
          0 ≤ (if (2 : Fin 3) = 0 then p0 else if (2 : Fin 3) = 1 then p1 else p2)
        simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
        exact ⟨hC21, hC22, by dsimp only [p2]; linarith⟩
    · simp only [Fin.sum_univ_three, Fin.isValue, show (0 : Fin 3) = 0 from rfl,
        show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) = 1 from rfl,
        show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
      dsimp only [p0, p1, p2]; ring
    · intro t; cases t
      · simp only [Fin.sum_univ_three, Fin.isValue, show (0 : Fin 3) = 0 from rfl,
          show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) = 1 from rfl,
          show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
        rw [hC0f, hC1f, hC2f, hCFf, hCTf, ← hrho_eq]
        dsimp only [p0, p1, p2, sf]
        by_cases hlt : v false < 0
        · simp only [hlt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, abs_of_neg hlt]
          field_simp; ring
        · simp only [hlt, decide_false, Bool.not_false, Bool.false_eq_true, ↓reduceIte, abs_of_nonneg (not_lt.mp hlt)]
          field_simp; ring
      · simp only [Fin.sum_univ_three, Fin.isValue, show (0 : Fin 3) = 0 from rfl,
          show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) = 1 from rfl,
          show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
        rw [hC0t, hC1t, hC2t, hCFt, hCTt, ← hrho_eq]
        dsimp only [p0, p1, p2, st]
        by_cases hlt : v true < 0
        · simp only [hlt, decide_true, ↓reduceIte, abs_of_neg hlt]
          field_simp; ring
        · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte, abs_of_nonneg (not_lt.mp hlt)]
          field_simp; ring
  · have hge : k ≤ s := by omega
    have hrho_eq : rho = 1 := if_neg hsk
    let δ : ℚ := 1 / (2 : ℚ) ^ (r - (s - k))
    have htot_eq : total = 1 + δ := if_neg hsk
    have hδ_pos : 0 < δ := by dsimp only [δ]; positivity
    have hδ_le1 : δ ≤ 1 := by
      dsimp only [δ]; rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
    obtain ⟨CF, hCF1, hCF2, hCFo, hCFf, hCFt⟩ := vertex_ge_k n r s hge Q hQ M hrk hd false
    obtain ⟨CT, hCT1, hCT2, hCTo, hCTt, hCTf⟩ := vertex_ge_k n r s hge Q hQ M hrk hd true
    simp only [Bool.not_false, Bool.not_true] at hCFt hCTf
    let sf : Bool := decide (v false < 0)
    let st : Bool := decide (v true < 0)
    let a : ℚ := |v false|
    let b : ℚ := |v true|
    have ha_ge : 0 ≤ a := abs_nonneg _
    have hb_ge : 0 ≤ b := abs_nonneg _
    have ha_le : a ≤ 1 := by rwa [hrho_eq] at hvF
    have hb_le : b ≤ 1 := by rwa [hrho_eq] at hvT
    have hab_le : a + b ≤ 1 + δ := by rwa [htot_eq] at hvSum
    have hsign_f : (if sf then (-1 : ℚ) else 1) * a = v false := by
      dsimp only [sf, a]; by_cases h : v false < 0 <;> simp [h, abs_of_neg, abs_of_nonneg, not_lt.mp]
    have hsign_t : (if st then (-1 : ℚ) else 1) * b = v true := by
      dsimp only [st, b]; by_cases h : v true < 0 <;> simp [h, abs_of_neg, abs_of_nonneg, not_lt.mp]
    have hsolve_pos : ∀ (x y : ℚ), 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → x + y ≤ 1 + δ →
        ∃ (p0 p1 p2 : ℚ) (vx0 vy0 vx1 vy1 vx2 vy2 : ℚ) (C0 C1 C2 : Circuit),
          (legalGates (2 * k) C0.gates ∧ costGates C0.gates ≤ s ∧ scoreQ n Q C0 false = (if sf then -1 else 1) * vx0 ∧ scoreQ n Q C0 true = (if st then -1 else 1) * vy0) ∧
          (legalGates (2 * k) C1.gates ∧ costGates C1.gates ≤ s ∧ scoreQ n Q C1 false = (if sf then -1 else 1) * vx1 ∧ scoreQ n Q C1 true = (if st then -1 else 1) * vy1) ∧
          (legalGates (2 * k) C2.gates ∧ costGates C2.gates ≤ s ∧ scoreQ n Q C2 false = (if sf then -1 else 1) * vx2 ∧ scoreQ n Q C2 true = (if st then -1 else 1) * vy2) ∧
          0 ≤ p0 ∧ 0 ≤ p1 ∧ 0 ≤ p2 ∧ p0 + p1 + p2 = 1 ∧
          p0 * vx0 + p1 * vx1 + p2 * vx2 = x ∧ p0 * vy0 + p1 * vy1 + p2 * vy2 = y := by
      intro x y hx0 hx1 hy0 hy1 hxy
      obtain ⟨Vpp, hVpp1, hVpp2, hVppf, hVppt⟩ := mk_signed CF hCF1 hCF2 hCFo sf st
      obtain ⟨Vpm, hVpm1, hVpm2, hVpmf, hVpmt⟩ := mk_signed CF hCF1 hCF2 hCFo sf (!st)
      obtain ⟨Vmp, hVmp1, hVmp2, hVmpf, hVmpt⟩ := mk_signed CF hCF1 hCF2 hCFo (!sf) st
      obtain ⟨Vmm, hVmm1, hVmm2, hVmmf, hVmmt⟩ := mk_signed CF hCF1 hCF2 hCFo (!sf) (!st)
      obtain ⟨Wpp, hWpp1, hWpp2, hWppf, hWppt⟩ := mk_signed CT hCT1 hCT2 hCTo sf st
      obtain ⟨Wpm, hWpm1, hWpm2, hWpmf, hWpmt⟩ := mk_signed CT hCT1 hCT2 hCTo sf (!st)
      obtain ⟨Wmp, hWmp1, hWmp2, hWmpf, hWmpt⟩ := mk_signed CT hCT1 hCT2 hCTo (!sf) st
      obtain ⟨Wmm, hWmm1, hWmm2, hWmmf, hWmmt⟩ := mk_signed CT hCT1 hCT2 hCTo (!sf) (!st)
      have hneg_b : ∀ s0 : Bool, (if !s0 then (-1 : ℚ) else 1) = (if s0 then (-1 : ℚ) else 1) * (-1) := by
        intro s0; cases s0 <;> norm_num
      simp only [hCFf, hCFt] at hVppf hVppt hVpmf hVpmt hVmpf hVmpt hVmmf hVmmt
      simp only [hCTf, hCTt] at hWppf hWppt hWpmf hWpmt hWmpf hWmpt hWmmf hWmmt
      by_cases hyδ : y ≤ δ
      · by_cases hyxδ : y ≤ x * δ
        · let p0 := (δ + y) / (2 * δ)
          let p2 := (1 - x) / 2
          let p1 := (x * δ - y) / (2 * δ)
          refine ⟨p0, p1, p2, 1, δ, 1, -δ, -1, -δ, Vpp, Vpm, Vmm,
            ⟨hVpp1, hVpp2, by simpa using hVppf, by simpa [δ] using hVppt⟩,
            ⟨hVpm1, hVpm2, by simpa using hVpmf, by rw [hVpmt, hneg_b]; ring⟩,
            ⟨hVmm1, hVmm2, by rw [hVmmf, hneg_b]; ring, by rw [hVmmt, hneg_b]; ring⟩,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          · dsimp only [p0]; positivity
          · dsimp only [p1]; exact div_nonneg (by linarith) (by positivity)
          · dsimp only [p2]; linarith
          · dsimp only [p0, p1, p2]; field_simp; ring
          · dsimp only [p0, p1, p2]; field_simp; ring
          · dsimp only [p0, p1, p2]; field_simp; ring
        · let p0 := (1 + x) / 2
          let p2 := (δ - y) / (2 * δ)
          let p1 := (y - x * δ) / (2 * δ)
          refine ⟨p0, p1, p2, 1, δ, -1, δ, -1, -δ, Vpp, Vmp, Vmm,
            ⟨hVpp1, hVpp2, by simpa using hVppf, by simpa [δ] using hVppt⟩,
            ⟨hVmp1, hVmp2, by rw [hVmpf, hneg_b]; ring, by simpa [δ] using hVmpt⟩,
            ⟨hVmm1, hVmm2, by rw [hVmmf, hneg_b]; ring, by rw [hVmmt, hneg_b]; ring⟩,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          · dsimp only [p0]; linarith
          · dsimp only [p1]; exact div_nonneg (by linarith) (by positivity)
          · dsimp only [p2]; exact div_nonneg (by linarith) (by positivity)
          · dsimp only [p0, p1, p2]; field_simp; ring
          · dsimp only [p0, p1, p2]; field_simp; ring
          · dsimp only [p0, p1, p2]; field_simp; ring
      · by_cases hxδ : x ≤ δ
        · by_cases hxyδ : x ≤ y * δ
          · let p0 := (δ + x) / (2 * δ)
            let p2 := (1 - y) / 2
            let p1 := (y * δ - x) / (2 * δ)
            refine ⟨p0, p1, p2, δ, 1, -δ, 1, -δ, -1, Wpp, Wmp, Wmm,
              ⟨hWpp1, hWpp2, by simpa [δ] using hWppf, by simpa using hWppt⟩,
              ⟨hWmp1, hWmp2, by rw [hWmpf, hneg_b]; ring, by simpa using hWmpt⟩,
              ⟨hWmm1, hWmm2, by rw [hWmmf, hneg_b]; ring, by rw [hWmmt, hneg_b]; ring⟩,
              ?_, ?_, ?_, ?_, ?_, ?_⟩
            · dsimp only [p0]; positivity
            · dsimp only [p1]; exact div_nonneg (by linarith) (by positivity)
            · dsimp only [p2]; linarith
            · dsimp only [p0, p1, p2]; field_simp; ring
            · dsimp only [p0, p1, p2]; field_simp; ring
            · dsimp only [p0, p1, p2]; field_simp; ring
          · let p0 := (1 + y) / 2
            let p2 := (δ - x) / (2 * δ)
            let p1 := (x - y * δ) / (2 * δ)
            refine ⟨p0, p1, p2, δ, 1, δ, -1, -δ, -1, Wpp, Wpm, Wmm,
              ⟨hWpp1, hWpp2, by simpa [δ] using hWppf, by simpa using hWppt⟩,
              ⟨hWpm1, hWpm2, by simpa [δ] using hWpmf, by rw [hWpmt, hneg_b]; ring⟩,
              ⟨hWmm1, hWmm2, by rw [hWmmf, hneg_b]; ring, by rw [hWmmt, hneg_b]; ring⟩,
              ?_, ?_, ?_, ?_, ?_, ?_⟩
            · dsimp only [p0]; linarith
            · dsimp only [p1]; exact div_nonneg (by linarith) (by positivity)
            · dsimp only [p2]; exact div_nonneg (by linarith) (by positivity)
            · dsimp only [p0, p1, p2]; field_simp; ring
            · dsimp only [p0, p1, p2]; field_simp; ring
            · dsimp only [p0, p1, p2]; field_simp; ring
        · have hδ_lt1 : δ < 1 := by linarith
          have hden : 0 < 1 - δ ^ 2 := by
            have hfac : 1 - δ ^ 2 = (1 - δ) * (1 + δ) := by ring
            rw [hfac]; exact mul_pos (by linarith) (by linarith)
          let u := (x - δ * y) / (1 - δ ^ 2)
          let p1 := (y - δ * x) / (1 - δ ^ 2)
          let p0 := (1 - p1 + u) / 2
          let p2 := (1 - p1 - u) / 2
          have hu_pos : 0 ≤ u := div_nonneg (by have : δ * y ≤ δ := mul_le_of_le_one_right (le_of_lt hδ_pos) hy1; linarith) (le_of_lt hden)
          have hp1_pos : 0 ≤ p1 := div_nonneg (by have : δ * x ≤ δ := mul_le_of_le_one_right (le_of_lt hδ_pos) hx1; linarith) (le_of_lt hden)
          have hsum_up1 : p1 + u ≤ 1 := by
            dsimp only [p1, u]
            rw [← add_div, div_le_one hden]
            have h1 : (y - δ * x) + (x - δ * y) = (x + y) * (1 - δ) := by ring
            have h2 : 1 - δ ^ 2 = (1 + δ) * (1 - δ) := by ring
            rw [h1, h2]
            exact mul_le_mul_of_nonneg_right hxy (by linarith)
          refine ⟨p0, p1, p2, 1, δ, δ, 1, -1, -δ, Vpp, Wpp, Vmm,
            ⟨hVpp1, hVpp2, by simpa using hVppf, by simpa [δ] using hVppt⟩,
            ⟨hWpp1, hWpp2, by simpa [δ] using hWppf, by simpa using hWppt⟩,
            ⟨hVmm1, hVmm2, by rw [hVmmf, hneg_b]; ring, by rw [hVmmt, hneg_b]; ring⟩,
            by dsimp only [p0]; linarith, hp1_pos, by dsimp only [p2]; linarith,
            by dsimp only [p0, p2]; ring, ?_, ?_⟩
          · have : p0 * 1 + p1 * δ + p2 * -1 = u + p1 * δ := by dsimp only [p0, p2]; ring
            rw [this]; dsimp only [u, p1]; field_simp; ring
          · have : p0 * δ + p1 * 1 + p2 * -δ = u * δ + p1 := by dsimp only [p0, p2]; ring
            rw [this]; dsimp only [u, p1]; field_simp; ring
    obtain ⟨p0, p1, p2, vx0, vy0, vx1, vy1, vx2, vy2, C0, C1, C2,
      ⟨hC01, hC02, hC0f, hC0t⟩, ⟨hC11, hC12, hC1f, hC1t⟩, ⟨hC21, hC22, hC2f, hC2t⟩,
      hp0, hp1, hp2, hpsum, hx_eq, hy_eq⟩ := hsolve_pos a b ha_ge ha_le hb_ge hb_le hab_le
    refine ⟨fun i => if i = 0 then C0 else if i = 1 then C1 else C2,
            fun i => if i = 0 then p0 else if i = 1 then p1 else p2, ?_, ?_, ?_⟩
    · intro i; fin_cases i
      · simp only [Fin.zero_eta, ↓reduceIte]; exact ⟨hC01, hC02, hp0⟩
      · simp only [Fin.mk_one, Fin.one_eq_zero_iff, Nat.reduceEqDiff, ↓reduceIte]; exact ⟨hC11, hC12, hp1⟩
      · simp only [Fin.reduceFinMk]
        change legalGates (2 * k) (if (2 : Fin 3) = 0 then C0 else if (2 : Fin 3) = 1 then C1 else C2).gates ∧
          costGates (if (2 : Fin 3) = 0 then C0 else if (2 : Fin 3) = 1 then C1 else C2).gates ≤ s ∧
          0 ≤ (if (2 : Fin 3) = 0 then p0 else if (2 : Fin 3) = 1 then p1 else p2)
        simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
        exact ⟨hC21, hC22, hp2⟩
    · simp only [Fin.sum_univ_three, Fin.isValue, show (0 : Fin 3) = 0 from rfl,
        show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) = 1 from rfl,
        show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]; exact hpsum
    · intro t; cases t
      · simp only [Fin.sum_univ_three, Fin.isValue, show (0 : Fin 3) = 0 from rfl,
          show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) = 1 from rfl,
          show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
        rw [hC0f, hC1f, hC2f, ← hsign_f, ← hx_eq]; ring
      · simp only [Fin.sum_univ_three, Fin.isValue, show (0 : Fin 3) = 0 from rfl,
          show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) = 1 from rfl,
          show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
        rw [hC0t, hC1t, hC2t, ← hsign_t, ← hy_eq]; ring

lemma main_29948 (n r s : ℕ) (Q : Bool → (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hQ : ∀ t, isQuad (Q t)) (hrk : M.rank = 2 * r)
    (hd : ∀ u v, (Q false (u + v) + Q true (u + v)) + (Q false u + Q true u) +
      (Q false v + Q true v) + (Q false 0 + Q true 0) = dotProduct u (M.mulVec v)) :
    let k := n + 1
    let rho : ℚ := if s < k then 1 / 2 ^ (n - s) else 1
    let total : ℚ := if s < k then rho else 1 + 1 / 2 ^ (r - (s - k))
    (∀ v : Bool → ℚ,
      (∃ (C : Fin 3 → Circuit) (p : Fin 3 → ℚ),
        (∀ i, legalGates (2 * k) (C i).gates ∧ costGates (C i).gates ≤ s ∧ 0 ≤ p i) ∧
        (∑ i, p i) = 1 ∧ ∀ t, v t = ∑ i, p i * scoreQ n Q (C i) t) ↔
      |v false| ≤ rho ∧ |v true| ≤ rho ∧ |v false| + |v true| ≤ total) ∧
    ((∃ C : Circuit, legalGates (2 * k) C.gates ∧ costGates C.gates ≤ s ∧ ∀ t, scoreQ n Q C t = 1) ↔
      k + r ≤ s) := by
  intro k rho total
  have hpart1 : ∀ v : Bool → ℚ,
      (∃ (C : Fin 3 → Circuit) (p : Fin 3 → ℚ),
        (∀ i, legalGates (2 * k) (C i).gates ∧ costGates (C i).gates ≤ s ∧ 0 ≤ p i) ∧
        (∑ i, p i) = 1 ∧ ∀ t, v t = ∑ i, p i * scoreQ n Q (C i) t) ↔
      |v false| ≤ rho ∧ |v true| ≤ rho ∧ |v false| + |v true| ≤ total := by
    intro v
    constructor
    · rintro ⟨C, p, hCp, hpsum, hv⟩
      have hbd : ∀ i : Fin 3, |scoreQ n Q (C i) false| ≤ rho ∧ |scoreQ n Q (C i) true| ≤ rho ∧
          |scoreQ n Q (C i) false| + |scoreQ n Q (C i) true| ≤ total :=
        fun i => score_in_region n r s Q M hrk hd (C i) (hCp i).1 (hCp i).2.1
      have hconv : ∀ t : Bool, |v t| ≤ ∑ i : Fin 3, p i * |scoreQ n Q (C i) t| := by
        intro t; rw [hv t]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul, abs_of_nonneg (hCp i).2.2]
      refine ⟨?_, ?_, ?_⟩
      · calc |v false| ≤ ∑ i : Fin 3, p i * |scoreQ n Q (C i) false| := hconv false
          _ ≤ ∑ i : Fin 3, p i * rho := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hbd i).1 (hCp i).2.2
          _ = (∑ i : Fin 3, p i) * rho := (Finset.sum_mul _ _ _).symm
          _ = rho := by rw [hpsum, one_mul]
      · calc |v true| ≤ ∑ i : Fin 3, p i * |scoreQ n Q (C i) true| := hconv true
          _ ≤ ∑ i : Fin 3, p i * rho := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hbd i).2.1 (hCp i).2.2
          _ = (∑ i : Fin 3, p i) * rho := (Finset.sum_mul _ _ _).symm
          _ = rho := by rw [hpsum, one_mul]
      · calc |v false| + |v true|
            ≤ (∑ i : Fin 3, p i * |scoreQ n Q (C i) false|) + (∑ i : Fin 3, p i * |scoreQ n Q (C i) true|) := by
              exact add_le_add (hconv false) (hconv true)
          _ = ∑ i : Fin 3, p i * (|scoreQ n Q (C i) false| + |scoreQ n Q (C i) true|) := by
              rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => by ring
          _ ≤ ∑ i : Fin 3, p i * total := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hbd i).2.2 (hCp i).2.2
          _ = (∑ i : Fin 3, p i) * total := (Finset.sum_mul _ _ _).symm
          _ = total := by rw [hpsum, one_mul]
    · rintro ⟨h1, h2, h3⟩
      exact region_to_mixture n r s Q hQ M hrk hd v h1 h2 h3
  refine ⟨hpart1, ?_⟩
  constructor
  · rintro ⟨C, hleg, hcost, heq⟩
    have hbd := score_in_region n r s Q M hrk hd C hleg hcost
    have h2 : (2 : ℚ) ≤ total := by
      have h1 := hbd.2.2; rw [heq false, heq true] at h1
      have h11 : |(1 : ℚ)| + |(1 : ℚ)| = 2 := by norm_num
      linarith
    by_cases hsk : s < k
    · exfalso
      have htot : total = 1 / (2 : ℚ) ^ (n - s) := by dsimp only [total, rho]; simp [hsk]
      rw [htot] at h2
      have hle1 : (1 : ℚ) / (2 : ℚ) ^ (n - s) ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
      linarith
    · have htot : total = 1 + 1 / (2 : ℚ) ^ (r - (s - k)) := if_neg hsk
      rw [htot] at h2
      have h1 : (1 : ℚ) ≤ 1 / (2 : ℚ) ^ (r - (s - k)) := by linarith
      have hpow : (2 : ℚ) ^ (r - (s - k)) ≤ 1 := by
        have := (le_div_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ) ^ (r - (s - k)))).mp h1
        linarith
      have hnat : 2 ^ (r - (s - k)) ≤ 1 := by exact_mod_cast hpow
      have hzero : r - (s - k) = 0 := by
        by_contra hne
        have : 2 ^ 1 ≤ 2 ^ (r - (s - k)) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      omega
  · intro hge
    obtain ⟨C, hleg, hcost, _, hsf, hst⟩ := vertex_ge_k n r s (by omega) Q hQ M hrk hd false
    have hrc : r - (s - k) = 0 := by omega
    rw [hrc, pow_zero, div_one] at hst
    refine ⟨C, hleg, hcost, fun t => ?_⟩
    cases t
    · exact hsf
    · exact hst

end PEqualNP.Outside.L_meta_29948_aux

theorem PEqualNP.Outside.L_meta_29948 :
∀ (n r s : ℕ),
  let F := ZMod 2
  let V := Fin n → F
  let quad := fun (q : V → F) =>
    ∃ (b : F) (a : V) (M : Fin n → Fin n → F), ∀ v,
      q v = b + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (n : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (n : ℕ) (u : Fin n → F) => List.ofFn (fun j : Fin n => decide (u j = 1))
  ∀ (Q : Bool → V → F) (M : Matrix (Fin n) (Fin n) F), (∀ t, quad (Q t)) →
    let d := fun u : V => Q false u + Q true u
    M.rank = 2*r → (∀ u v, d (u+v) + d u + d v + d 0 = dotProduct u (M.mulVec v)) →
    let k := n+1
    let score := fun (C : Circ) (t : Bool) =>
      (∑ x : Fin k → F, ∑ u : V,
        let y : Fin k → F := Fin.cons (if t then 1 else 0) u
        if C.eval (bits k x ++ bits k y) = decide (dotProduct x y + Q t u = 1)
        then (1 : ℚ) else -1) / 2^(k+n)
    let rho : ℚ := if s < k then 1 / 2^(n-s) else 1
    let total : ℚ := if s < k then rho else 1 + 1 / 2^(r-(s-k))
    (∀ v : Bool → ℚ,
      (∃ (C : Fin 3 → Circ) (p : Fin 3 → ℚ),
        (∀ i, legal (2*k) (C i) ∧ cost (C i) ≤ s ∧ 0 ≤ p i) ∧
        (∑ i, p i) = 1 ∧ ∀ t, v t = ∑ i, p i * score (C i) t) ↔
      |v false| ≤ rho ∧ |v true| ≤ rho ∧ |v false| + |v true| ≤ total) ∧
    ((∃ C : Circ, legal (2*k) C ∧ cost C ≤ s ∧ ∀ t, score C t = 1) ↔ k+r ≤ s) := by
  intro n r s F V quad Circ legal cost bits Q M hQ d hrk hd k score rho total
  exact PEqualNP.Outside.L_meta_29948_aux.main_29948 n r s Q M hQ hrk hd
