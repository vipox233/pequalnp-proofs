import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32052_aux

namespace Previous

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

end Previous

theorem previousReduction :
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
    exact Previous.viaFlat_to_viaCircuit k s g T B a q hB hq hT
  refine ⟨hflat, ?_, ?_⟩
  · intro hbig
    refine ⟨?_, hflat⟩
    rintro ⟨C, hleg, hcost, hT⟩
    exact Previous.viaCircuit_to_viaFlat k s g T hbig C hleg hcost hT
  · rintro ⟨C, hleg, hcost, hT⟩
    exact Previous.viaCircuit_le_bound k s g T C hleg hcost hT

namespace Code32052

abbrev F := ZMod 2
abbrev Vec (j : ℕ) := Fin j → F

def extendByZero {s b : ℕ} (_h : s ≤ b) : Vec s →ₗ[F] Vec b where
  toFun v i := if hi : i.val < s then v ⟨i.val,hi⟩ else 0
  map_add' v w := by ext i; by_cases hi : i.val < s <;> simp [hi]
  map_smul' c v := by ext i; by_cases hi : i.val < s <;> simp [hi]

theorem inject_extend {s b : ℕ} (h : s ≤ b) : Function.Injective (extendByZero h) := by
  intro v w eq
  ext i
  have t := congrFun eq (Fin.castLE h i)
  simpa [extendByZero,i.isLt] using t

theorem zeroFlat {k m r s n : ℕ} (hs : s ≤ 2*m+r)
    (e : Vec n ≃ₗ[F] Vec k × (Vec m × (Vec m × Vec r))) :
    ∃ B : Vec s →ₗ[F] Vec n, Function.Injective B ∧ ∀ v, (e (B v)).1 = 0 := by
  classical
  let b := 2*m+r
  let coord : Vec b ≃ₗ[F] (Vec m × (Vec m × Vec r)) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [Vec,b,Module.finrank_prod,Module.finrank_pi]; omega)
  let ins := LinearMap.inr F (Vec k) (Vec m × (Vec m × Vec r))
  let B := e.symm.toLinearMap.comp (ins.comp (coord.toLinearMap.comp (extendByZero hs)))
  refine ⟨B, ?_, ?_⟩
  · apply e.symm.injective.comp
    apply (show Function.Injective ins from fun x y h => congrArg Prod.snd h).comp
    exact coord.injective.comp (inject_extend hs)
  · intro v
    simp [B,ins]

theorem base_opt : ∀ (k m r d : ℕ), 0 < k → 0 < d →
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
  ∀ (e : V ≃ₗ[F] S × (D × (D × Z))) (A : Fin m → S),
    let wt := fun (a : S) => ((Finset.univ : Finset (Fin m)).filter
      (fun i => dotProduct (A i) a ≠ 0)).card
    (∀ a : S, a ≠ 0 → d ≤ wt a) → (∃ a : S, a ≠ 0 ∧ wt a = d) →
    ∀ h : S → F,
      let g := fun (y : V) => h (e y).1 + ∑ i : Fin m,
        dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
      let raw := fun (C : Circ) => (∑ x : V, ∑ y : V,
        if C.eval (bits n x ++ bits n y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs
      let upper := fun (s p q : ℕ) => ∀ C : Circ, legal (2*n) C → cost C ≤ s →
        q * raw C ≤ p * 2^(n+s)
      let opt := fun (s p q : ℕ) => upper s p q ∧
        ∃ C : Circ, legal (2*n) C ∧ cost C ≤ s ∧ q * raw C = p * 2^(n+s)
      let two := ∃ a b : S, a ≠ b ∧ wt a = 1 ∧ wt b = 1
      ∀ s : ℕ, s ≤ base → opt s 1 1 := by
  classical
  intro k m r d hk hd n Circ FF legal cost bits V S D Z base e A wt hdist hex h g raw upper opt two s hs
  have hsn : s ≤ n := by dsimp [base,n] at *; omega
  obtain ⟨B, hB, hz⟩ := zeroFlat (s := s) (by exact hs) e
  have hg (v : Vec s) : g (B v) = h 0 := by simp [g,hz]
  let q := fun (_ : Vec s) => h 0
  have hq : ∃ (c : F) (a : Vec s) (M : Fin s → Fin s → F), ∀ v : Vec s,
      q v = c + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j := by
    exact ⟨h 0, 0, 0, by intro v; simp [q]⟩
  let T := 2^(n+s)
  have red := previousReduction n s hsn g T
  obtain ⟨Cup, hleg, hcost, hraw⟩ := red.1 ⟨B, 0, q, hB, hq, by
    simp [q,hg,T,pow_add,ZMod.card,Vec]⟩
  have ub (C : Circ) (hl : legal (2*n) C) (hc : cost C ≤ s) : raw C ≤ 2^(n+s) := by
    exact (previousReduction n s hsn g (raw C)).2.2 ⟨C,hl,hc,le_rfl⟩
  constructor
  · intro C hl hc
    simpa using ub C hl hc
  · exact ⟨Cup,hleg,hcost,by simpa [T] using Nat.le_antisymm (ub Cup hleg hcost) hraw⟩

end Code32052

namespace Code32052
abbrev K := ZMod 2
abbrev Vc (n : ℕ) := Fin n → K
def sign (x : K) : ℤ := if x = 0 then 1 else -1
theorem sign_add : ∀ a b, sign (a+b) = sign a * sign b := by decide
theorem sign_sum {ι : Type*} (s : Finset ι) (f : ι → K) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => simp [ha,sign_add,ih]

theorem diag_sum {m : ℕ} (c : Vc m) :
    (∑ u : Vc m, ∑ v : Vc m, sign (∑ i, c i*u i*v i)) =
      (2:ℤ)^((Finset.univ.filter fun i => c i ≠ 0).card) *
      4^((Finset.univ.filter fun i => c i = 0).card) := by
  classical
  let t (w : Vc m × Vc m) := ∏ i, sign (c i * w.1 i * w.2 i)
  let e : (Fin m → K × K) ≃ Vc m × Vc m :=
    ⟨fun f => (fun i => (f i).1, fun i => (f i).2),
     fun f i => (f.1 i, f.2 i), by intro f; rfl, by intro f; rfl⟩
  have fac := Finset.prod_univ_sum (ι := Fin m) (fun _ => (Finset.univ : Finset (K × K)))
    (fun i w => sign (c i*w.1*w.2))
  have each : ∀ x : K, (∑ w : K × K, sign (x*w.1*w.2)) = if x = 0 then 4 else 2 := by decide
  calc
    _ = ∑ w : Vc m × Vc m, t w := by simp [t,Fintype.sum_prod_type,sign_sum]
    _ = ∑ f : Fin m → K × K, t (e f) := (e.sum_comp t).symm
    _ = ∏ i, ∑ w : K × K, sign (c i*w.1*w.2) := by simpa [e,t] using fac.symm
    _ = ∏ i, (if c i = 0 then (4:ℤ) else 2) := by simp_rw [each]
    _ = _ := by rw [Finset.prod_ite]; simp [mul_comm]

end Code32052
namespace Code32052
open Previous
theorem cases_two : ∀ x : K, x = 0 ∨ x = 1 := by decide

theorem selectedSum (m r : ℕ) (c : Vc m) :
    let t := (Finset.univ.filter fun i => c i ≠ 0).card
    let value := fun (w : K × (Vc m × (Vc m × Vc r))) =>
      sign (∑ i, (w.1*c i)*w.2.1 i*w.2.2.1 i)
    (∑ w, value w) = (2:ℤ)^(2*m+r-t) * (2^t+1) := by
  classical
  intro t value
  have pair : (Finset.univ : Finset K) = {0,1} := by decide
  have two_ne : (0:K) ≠ 1 := by decide
  have ht : t + (Finset.univ.filter fun i => c i = 0).card = m := by
    simpa [t] using Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => c i ≠ 0)
  have hn : t ≤ m := by omega
  have sum_bit (s : K) :
      (∑ w : Vc m × (Vc m × Vc r), value (s,w)) =
        (∑ x : Vc m, ∑ y : Vc m, sign (∑ i, (s*c i)*x i*y i)) * 2^r := by
    simp [Fintype.sum_prod_type, value, Vc, ZMod.card, Finset.sum_mul, Finset.mul_sum, mul_comm]
  rw [Fintype.sum_prod_type]
  simp_rw [sum_bit]
  rw [pair, Finset.sum_insert (by simpa using two_ne), Finset.sum_singleton]
  simp only [zero_mul,Finset.sum_const_zero,one_mul]
  rw [diag_sum]
  have zc : (Finset.univ.filter fun i => c i = 0).card = m-t := by omega
  rw [zc]
  change _ + (2:ℤ)^t*4^(m-t)*2^r = _
  simp only [sign,if_pos rfl,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
    Fintype.card_fin,ZMod.card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,mul_one,Vc]
  have ar : 2*m+r-t = t+2*(m-t)+r := by omega
  have ar' : m+m+r = (2*m+r-t)+t := by omega
  have ha : (2:ℤ)^m * 2^m * 2^r = 2^(2*m+r-t)*2^t := by
    rw [← pow_add, ← pow_add, ar', pow_add]
  have hb : (2:ℤ)^t * 4^(m-t) * 2^r = 2^(2*m+r-t) := by
    rw [ar,pow_add,pow_add,pow_mul]; norm_num
  simp only [ite_true, eq_self] at *
  linear_combination ha + hb

end Code32052

namespace Code32052
open Previous

theorem lineScore {k m r n : ℕ} (e : Vc n ≃ₗ[K] Vc k × (Vc m × (Vc m × Vc r)))
    (A : Fin m → Vc k) (h : Vc k → K) (a : Vc k) (ha : a ≠ 0) :
    let s := 2*m+r+1
    let g (y : Vc n) := h (e y).1 + ∑ i, dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
    let d := (Finset.univ.filter fun i => dotProduct (A i) a ≠ 0).card
    ∃ (B : Vc s →ₗ[K] Vc n) (q : Vc s → K), Function.Injective B ∧ isQuad q ∧
      (∑ v : Vc s, if g (B v) = q v then (1:ℤ) else -1) = 2^(2*m+r-d)*(2^d+1) := by
  classical
  intro s g d
  let U := Vc m × (Vc m × Vc r)
  let f : Vc s ≃ₗ[K] K × U := LinearEquiv.ofFinrankEq _ _ (by
    simp [s,U,Vc,Module.finrank_prod,Module.finrank_pi]; omega)
  let t : Vc s →ₗ[K] K := (LinearMap.fst K K U).comp f.toLinearMap
  let lift : K × U →ₗ[K] Vc k × U :=
    ((LinearMap.fst K K U).smulRight a).prod (LinearMap.snd K K U)
  let B := e.symm.toLinearMap.comp (lift.comp f.toLinearMap)
  have inj : Function.Injective lift := by
    rintro ⟨i,u⟩ ⟨j,v⟩ eq
    have et : i • a = j • a := congrArg Prod.fst eq
    have eu : u = v := congrArg Prod.snd eq
    rcases cases_two i with rfl|rfl <;> rcases cases_two j with rfl|rfl <;> simp_all
  let q (v : Vc s) := h (t v • a)
  refine ⟨B,q,e.symm.injective.comp (inj.comp f.injective),?_,?_⟩
  · let L := (h a - h 0) • t
    obtain ⟨b,hb⟩ := linear_coord_dot L
    have hq := isQuad_affine b (h 0)
    convert hq using 1
    funext v
    rw [← hb]
    change h (t v • a) = (h a - h 0) * t v + h 0
    rcases cases_two (t v) with hv|hv <;> simp [hv]
  · let score (w : K × U) := sign (∑ i, w.1 * dotProduct (A i) a * w.2.1 i * w.2.2.1 i)
    have point (v : Vc s) : (if g (B v) = q v then (1:ℤ) else -1) = score (f v) := by
      have elem : e (B v) = ((f v).1 • a, (f v).2) := by simp [B,lift]
      simp [g,q,t,elem,dotProduct_smul,smul_eq_mul,score,sign]
    simp_rw [point]
    trans ∑ w : K × U, score w
    · exact f.toEquiv.sum_comp score
    exact selectedSum m r (fun i => dotProduct (A i) a)

end Code32052

namespace Code32052
open Previous
def weight {m : ℕ} (c : Vc m) := (Finset.univ.filter fun i => c i ≠ 0).card

theorem two_units {m k : ℕ} (A : Fin m → Vc k)
    (inj : ∀ x : Vc k, (∀ i, dotProduct (A i) x = 0) → x = 0)
    {a b : Vc k} (hab : a ≠ b)
    (wa : weight (fun i => dotProduct (A i) a) = 1)
    (wb : weight (fun i => dotProduct (A i) b) = 1) :
    weight (fun i => dotProduct (A i) (a+b)) = 2 := by
  classical
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp wa
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp wb
  have pa (l : Fin m) : dotProduct (A l) a ≠ 0 ↔ l = i := by
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton] using (congrArg (fun T : Finset (Fin m) => l ∈ T) hi).to_iff
  have pb (l : Fin m) : dotProduct (A l) b ≠ 0 ↔ l = j := by
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton] using (congrArg (fun T : Finset (Fin m) => l ∈ T) hj).to_iff
  have eqImp (c : Vc k) (u : Fin m) (h : ∀ l, dotProduct (A l) c ≠ 0 ↔ l = u) (l : Fin m) :
      dotProduct (A l) c = if l = u then 1 else 0 := by
    by_cases hl : l = u
    · rw [if_pos hl]
      exact (cases_two _).resolve_left ((h l).2 hl)
    · rw [if_neg hl]
      exact not_not.mp (fun hn => hl ((h l).1 hn))
  have neq : i ≠ j := by
    intro h
    apply hab
    apply sub_eq_zero.mp
    apply inj
    intro l
    rw [dotProduct_sub,eqImp a i pa,eqImp b j pb,h,sub_self]
  have union : (Finset.univ.filter fun l => dotProduct (A l) (a+b) ≠ 0) = {i,j} := by
    ext l
    rw [Finset.mem_filter,dotProduct_add,eqImp a i pa,eqImp b j pb]
    by_cases hl : l=i <;> by_cases hl' : l=j <;> simp_all
  unfold weight
  rw [union]
  simp [neq]

theorem affine_two {s : ℕ} (u v : Vc s →ₗ[K] K) (f : K → K → K) :
    isQuad (fun x => f (u x) (v x)) := by
  classical
  let lin := (f 1 0 - f 0 0) • u + (f 0 1 - f 0 0) • v
  let cross := (f 1 1 - f 1 0 - f 0 1 + f 0 0) • u
  obtain ⟨l,hl⟩ := linear_coord_dot lin
  obtain ⟨c,hc⟩ := linear_coord_dot cross
  obtain ⟨b,hb⟩ := linear_coord_dot v
  have hq := isQuad_add (isQuad_affine l (f 0 0)) (isQuad_mul_affine c b 0 0)
  convert hq using 1
  funext x
  simp only [← hl, ← hc, ← hb,add_zero]
  change f (u x) (v x) = ((_ * u x + _ * v x) + f 0 0) + (_ * u x) * v x
  rcases cases_two (u x) with hx|hx <;> rcases cases_two (v x) with hy|hy <;> rw [hx,hy] <;> ring

theorem dataSum {m r : ℕ} (c : Vc m) :
    (∑ w : Vc m × (Vc m × Vc r), sign (∑ i, c i*w.1 i*w.2.1 i)) = (2:ℤ)^(2*m+r-weight c) := by
  classical
  have ht : weight c + (Finset.univ.filter fun i => c i = 0).card = m := by
    simpa [weight] using Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => c i ≠ 0)
  calc
    _ = (∑ u : Vc m, ∑ v : Vc m, sign (∑ i, c i*u i*v i))*2^r := by
      simp [Fintype.sum_prod_type, Vc, ZMod.card, Finset.sum_mul, Finset.mul_sum, mul_comm]
    _ = _ := by
      rw [diag_sum]
      change (2:ℤ)^weight c * 4^_ * 2^r = _
      have ar : 2*m+r-weight c = weight c + 2*(Finset.univ.filter fun i => c i = 0).card + r := by omega
      rw [ar,pow_add,pow_add,pow_mul]; norm_num

end Code32052

namespace Code32052
open Previous
def choose2 (a b : Vc k) : K × K →ₗ[K] Vc k :=
  (LinearMap.fst K K K).smulRight a + (LinearMap.snd K K K).smulRight b

theorem choose2_inj {k : ℕ} (a b : Vc k) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Function.Injective (choose2 a b) := by
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨i,j⟩ hx
  change i • a + j • b = 0 at hx
  have nsum : a + b ≠ 0 := by
    intro hz
    have invol : ∀ t : K, t+t=0 := by decide
    apply hab
    ext t
    have h := congrFun hz t
    change a t + b t = 0 at h
    linear_combination h - invol (b t)
  rcases cases_two i with rfl|rfl <;> rcases cases_two j with rfl|rfl
  · rfl
  · exact (hb (by simpa only [zero_smul,one_smul,zero_add] using hx)).elim
  · exact (ha (by simpa only [zero_smul,one_smul,add_zero] using hx)).elim
  · exact (nsum (by simpa only [one_smul] using hx)).elim

theorem planeSum {k m r : ℕ} (A : Fin m → Vc k) (a b : Vc k)
    (wa : weight (fun i => dotProduct (A i) a) = 1)
    (wb : weight (fun i => dotProduct (A i) b) = 1)
    (wab : weight (fun i => dotProduct (A i) (a+b)) = 2) :
    let U := Vc m × (Vc m × Vc r)
    let sel := choose2 a b
    let score (w : (K × K) × U) := sign (∑ i, dotProduct (A i) (sel w.1) * w.2.1 i * w.2.2.1 i)
    (∑ w, score w) = 9*2^(2*m+r-2) := by
  classical
  intro U sel score
  change (∑ w : (K × K) × U, score w) = _
  rw [Fintype.sum_prod_type]
  have sc (v : K × K) : (∑ t : U, score (v,t)) = 2^(2*m+r-weight (fun i => dotProduct (A i) (sel v))) :=
    dataSum (r := r) (m := m) (fun i => dotProduct (A i) (sel v))
  trans ∑ v : K × K, (2:ℤ)^(2*m+r-weight (fun i => dotProduct (A i) (sel v)))
  · exact Finset.sum_congr rfl (fun v _ => sc v)
  rw [Fintype.sum_prod_type]
  have z : weight (fun i : Fin m => dotProduct (A i) (0 : Vc k)) = 0 := by simp [weight]
  have univ : (Finset.univ : Finset K) = {0,1} := by decide
  have enumerate (F : K → ℤ) : (∑ i, F i) = F 0 + F 1 := by rw [univ,Finset.sum_insert (by decide),Finset.sum_singleton]
  rw [enumerate,enumerate,enumerate]
  change 2^(2*m+r - weight (fun i => dotProduct (A i) (choose2 a b (0,0)))) + 2^(2*m+r-weight (fun i => dotProduct (A i) (choose2 a b (0,1)))) +
       (2^(2*m+r-weight (fun i => dotProduct (A i) (choose2 a b (1,0)))) + 2^(2*m+r-weight (fun i => dotProduct (A i) (choose2 a b (1,1))))) = _
  have h00 : choose2 a b (0,0) = 0 := by change (0:K) • a + (0:K) • b = _; simp
  have h01 : choose2 a b (0,1) = b := by change (0:K) • a + (1:K) • b = _; simp
  have h10 : choose2 a b (1,0) = a := by change (1:K) • a + (0:K) • b = _; simp
  have h11 : choose2 a b (1,1) = a+b := by change (1:K) • a + (1:K) • b = _; simp
  rw [h00,h01,h10,h11,z,wa,wb,wab,Nat.sub_zero]
  have hm : 2 ≤ m := by rw [← wab]; exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  have e0 : 2*m+r = (2*m+r-2)+2 := by omega
  have e1 : 2*m+r-1 = (2*m+r-2)+1 := by omega
  calc
    _ = (2:ℤ)^((2*m+r-2)+2) + 2^((2*m+r-2)+1) + (2^((2*m+r-2)+1) + 2^(2*m+r-2)) := by rw [← e0,← e1]
    _ = _ := by ring

set_option maxHeartbeats 350000 in
theorem planeScore {k m r n : ℕ} (e : Vc n ≃ₗ[K] Vc k × (Vc m × (Vc m × Vc r)))
    (A : Fin m → Vc k) (h : Vc k → K) (a b : Vc k) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (wa : weight (fun i => dotProduct (A i) a) = 1)
    (wb : weight (fun i => dotProduct (A i) b) = 1)
    (wab : weight (fun i => dotProduct (A i) (a+b)) = 2) :
    let s := 2*m+r+2
    let g (y : Vc n) := h (e y).1 + ∑ i, dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
    ∃ (B : Vc s →ₗ[K] Vc n) (q : Vc s → K), Function.Injective B ∧ isQuad q ∧
      (∑ v : Vc s, if g (B v) = q v then (1:ℤ) else -1) = 9*2^(2*m+r-2) := by
  classical
  intro s g
  let U := Vc m × (Vc m × Vc r)
  let W := (K × K) × U
  let f : Vc s ≃ₗ[K] W := LinearEquiv.ofFinrankEq _ _ (by
    simp [s,W,U,Vc,Module.finrank_prod,Module.finrank_pi]; omega)
  let sel : (K × K) →ₗ[K] Vc k := (LinearMap.fst K K K).smulRight a + (LinearMap.snd K K K).smulRight b
  let lift : W →ₗ[K] Vc k × U := (sel.comp (LinearMap.fst K (K × K) U)).prod (LinearMap.snd K (K × K) U)
  let B := e.symm.toLinearMap.comp (lift.comp f.toLinearMap)
  have sinj : Function.Injective sel := choose2_inj a b ha hb hab
  have linj : Function.Injective lift := by
    rintro ⟨v,x⟩ ⟨w,y⟩ h
    change (sel v,x) = (sel w,y) at h
    exact Prod.ext (sinj (congrArg Prod.fst h)) (congrArg (fun p : Vc k × U => p.2) h)
  let u := (LinearMap.fst K K K).comp ((LinearMap.fst K (K × K) U).comp f.toLinearMap)
  let v := (LinearMap.snd K K K).comp ((LinearMap.fst K (K × K) U).comp f.toLinearMap)
  let q (x : Vc s) := h (sel (f x).1)
  refine ⟨B,q,e.symm.injective.comp (linj.comp f.injective),affine_two u v (fun i j => h (i • a+j • b)),?_⟩
  let score (w : W) := sign (∑ i, dotProduct (A i) (sel w.1) * w.2.1 i * w.2.2.1 i)
  have eq (x : Vc s) : (if g (B x) = q x then (1:ℤ) else -1) = score (f x) := by
    have he : e (B x) = (sel (f x).1,(f x).2) := by change e (e.symm _) = _; rw [e.apply_symm_apply]; rfl
    simp [g,q,score,sign,he]
  simp_rw [eq]
  trans ∑ w : W, score w
  · exact f.toEquiv.sum_comp score
  exact planeSum A a b wa wb wab
end Code32052

namespace Code32052
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover Previous
theorem exact_lift (k s : ℕ) (g : (Fin k → F2) → F2) (T : ℕ)
    (B : (Fin s → F2) →ₗ[F2] (Fin k → F2)) (a : Fin k → F2) (q : (Fin s → F2) → F2)
    (hB : Function.Injective B) (hq : isQuad q)
    (hT : T = 2 ^ k * (∑ v : Fin s → F2, if g (a + B v) = q v then (1 : ℤ) else -1).natAbs) :
    ∃ C : Circuit, legalGates (2 * k) C.gates ∧ costGates C.gates ≤ s ∧
      T = (∑ x : Fin k → F2, ∑ y : Fin k → F2,
        if C.eval (bitsOf k x ++ bitsOf k y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs := by
  classical
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

end Code32052

namespace Code32052
theorem one_exact : ∀ (k m r d : ℕ), 0 < k → 0 < d →
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
  ∀ (e : V ≃ₗ[F] S × (D × (D × Z))) (A : Fin m → S),
    let wt := fun (a : S) => ((Finset.univ : Finset (Fin m)).filter
      (fun i => dotProduct (A i) a ≠ 0)).card
    (∀ a : S, a ≠ 0 → d ≤ wt a) → (∃ a : S, a ≠ 0 ∧ wt a = d) →
    ∀ h : S → F,
      let g := fun (y : V) => h (e y).1 + ∑ i : Fin m,
        dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
      let raw := fun (C : Circ) => (∑ x : V, ∑ y : V,
        if C.eval (bits n x ++ bits n y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs
      let upper := fun (s p q : ℕ) => ∀ C : Circ, legal (2*n) C → cost C ≤ s →
        q * raw C ≤ p * 2^(n+s)
      let opt := fun (s p q : ℕ) => upper s p q ∧
        ∃ C : Circ, legal (2*n) C ∧ cost C ≤ s ∧ q * raw C = p * 2^(n+s)
      let two := ∃ a b : S, a ≠ b ∧ wt a = 1 ∧ wt b = 1
      ∃ C : Circ, legal (2*n) C ∧ cost C ≤ base+1 ∧
        (2^d+1)*2^(n+(base+1)) = 2^(d+1)*raw C := by
  classical
  intro k m r d hk hd n Circ FF legal cost bits V S D Z base e A wt hdist hex h g raw upper opt two
  obtain ⟨a, ha,hw⟩ := hex
  obtain ⟨B,q,hinj,hquad,hscore⟩ := lineScore e A h a ha
  have hs : base+1 ≤ n := by dsimp [base,n]; omega
  have hd' : d ≤ m := by
    rw [← hw]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  let T := 2^n * (2^(base-d)*(2^d+1))
  have score : (∑ v : Vc (base+1), if g (B v) = q v then (1:ℤ) else -1) =
      2^(base-d)*(2^d+1) := by rw [← hw]; exact hscore
  obtain ⟨C,hl,hc,hb⟩ := exact_lift n (base+1) g T B 0 q hinj hquad (by
    simp only [zero_add]
    rw [score]
    have cast : (2:ℤ)^(base-d)*(2^d+1) = ((2^(base-d)*(2^d+1) : ℕ) : ℤ) := by push_cast; rfl
    rw [cast,Int.natAbs_natCast])
  refine ⟨C,hl,hc,?_⟩
  change T = raw C at hb
  rw [← hb]
  suffices (2^d+1)*2^(n+(base+1)) = 2^(d+1)*T from this
  have exp_eq : d+1+(n+(base-d)) = n+(base+1) := by dsimp [base]; omega
  unfold T
  rw [← exp_eq, pow_add (2:ℕ) (d+1), pow_add (2:ℕ) n]
  ring

end Code32052

namespace Code32052
theorem two_exact : ∀ (k m r d : ℕ), 0 < k → 0 < d →
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
  ∀ (e : V ≃ₗ[F] S × (D × (D × Z))) (A : Fin m → S),
    let wt := fun (a : S) => ((Finset.univ : Finset (Fin m)).filter
      (fun i => dotProduct (A i) a ≠ 0)).card
    (∀ a : S, a ≠ 0 → d ≤ wt a) → (∃ a : S, a ≠ 0 ∧ wt a = d) →
    ∀ h : S → F,
      let g := fun (y : V) => h (e y).1 + ∑ i : Fin m,
        dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
      let raw := fun (C : Circ) => (∑ x : V, ∑ y : V,
        if C.eval (bits n x ++ bits n y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs
      let upper := fun (s p q : ℕ) => ∀ C : Circ, legal (2*n) C → cost C ≤ s →
        q * raw C ≤ p * 2^(n+s)
      let opt := fun (s p q : ℕ) => upper s p q ∧
        ∃ C : Circ, legal (2*n) C ∧ cost C ≤ s ∧ q * raw C = p * 2^(n+s)
      let two := ∃ a b : S, a ≠ b ∧ wt a = 1 ∧ wt b = 1
      2 ≤ k → two → ∃ C : Circ, legal (2*n) C ∧ cost C ≤ base+2 ∧
        9*2^(n+(base+2)) = 16*raw C := by
  classical
  intro k m r d hk hd n Circ FF legal cost bits V S D Z base e A wt hdist hex h g raw upper opt two
  intro hk2 ht
  rcases ht with ⟨a,b,ab,wa,wb⟩
  have aw : weight (fun i => dotProduct (A i) a) = 1 := wa
  have bw : weight (fun i => dotProduct (A i) b) = 1 := wb
  have inj (x : S) (hx : ∀ i, dotProduct (A i) x = 0) : x = 0 := by
    by_contra ne
    have low := hdist x ne
    have : wt x = 0 := by simp [wt,hx]
    omega
  have an : a ≠ 0 := by rintro rfl; simp [weight] at aw
  have bn : b ≠ 0 := by rintro rfl; simp [weight] at bw
  have wab := two_units A inj ab aw bw
  obtain ⟨B,q,hi,hq,score⟩ := planeScore e A h a b an bn ab aw bw wab
  have hm : 2 ≤ m := by rw [← wab]; exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  have hs : base+2 ≤ n := by dsimp [base,n]; omega
  let T := 2^n * (9*2^(base-2))
  have sc : (∑ v : Vc (base+2), if g (B v) = q v then (1:ℤ) else -1) = 9*2^(base-2) := score
  obtain ⟨C,hl,hc,hb⟩ := exact_lift n (base+2) g T B 0 q hi hq (by
    simp only [zero_add]
    rw [sc]
    have cast : (9:ℤ)*2^(base-2) = ((9*2^(base-2) : ℕ) : ℤ) := by push_cast; rfl
    rw [cast,Int.natAbs_natCast])
  refine ⟨C,hl,hc,?_⟩
  change T = raw C at hb
  rw [← hb]
  suffices 9*2^(n+(base+2)) = 16*T from this
  have ex : n+(base+2) = (n+(base-2))+4 := by dsimp [base]; omega
  rw [ex,pow_add,pow_add]
  dsimp [T]
  ring

end Code32052

theorem Code32052.upper_iff_flat :
∀ (k s p q : ℕ),
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
  s ≤ k → 0 < q → q ≤ 2*p → ∀ g : V → F,
    (∀ C : Circ, legal (2*k) C → cost C ≤ s → q * raw g C ≤ p * 2^(k+s)) ↔
    ∀ (B : E →ₗ[F] V) (a : V) (f : E → F), Function.Injective B → quad f →
       q * (∑ v : E, if g (a+B v) = f v then (1:ℤ) else -1).natAbs ≤ p * 2^s := by
  classical
  intro k s p q Circ F legal cost bits V E quad raw hs hq hh g
  let red := previousReduction k s hs g
  have pos : 0 < 2^k := by positivity
  constructor
  · intro hu B a f hi hf
    let mass := (∑ v : E, if g (a+B v) = f v then (1:ℤ) else -1).natAbs
    obtain ⟨C,hl,hc,att⟩ := (red (2^k*mass)).1 ⟨B,a,f,hi,hf,le_rfl⟩
    change 2^k*mass ≤ raw g C at att
    have ub := hu C hl hc
    have cmp : 2^k*(q*mass) ≤ 2^k*(p*2^s) := calc
      _ = q*(2^k*mass) := by ring
      _ ≤ q*raw g C := Nat.mul_le_mul_left _ att
      _ ≤ p*2^(k+s) := ub
      _ = _ := by rw [pow_add]; ring
    exact Nat.le_of_mul_le_mul_left cmp pos
  · intro hu C hl hc
    by_contra! bad
    have big : 2^(k+s) < 2*raw g C := by
      apply Nat.lt_of_mul_lt_mul_left (a := q)
      calc
        q*2^(k+s) ≤ (2*p)*2^(k+s) := Nat.mul_le_mul_right _ hh
        _ = 2*(p*2^(k+s)) := by ring
        _ < 2*(q*raw g C) := by omega
        _ = _ := by ring
    obtain ⟨B,a,f,hi,hf,corr⟩ := ((red (raw g C)).2.1 big).mp ⟨C,hl,hc,le_rfl⟩
    apply (not_le.mpr bad)
    calc
      q * raw g C ≤ q * (2^k * _) := Nat.mul_le_mul_left _ corr
      _ = 2^k * (q * _) := by ac_rfl
      _ ≤ 2^k * (p * 2^s) := Nat.mul_le_mul_left _ (hu B a f hi hf)
      _ = p*2^(k+s) := by rw [pow_add]; ring

namespace Code32052
theorem affine_diag_abs {m : ℕ} (c a b : Vc m) :
    |∑ x : Vc m, ∑ y : Vc m, sign (∑ i : Fin m, (c i*x i*y i + a i*x i + b i*y i))| ≤
      (2:ℤ)^(2*m-(Finset.univ.filter fun i => c i ≠ 0).card) := by
  classical
  let t (w : Vc m × Vc m) := ∏ i, sign (c i*w.1 i*w.2 i + a i*w.1 i + b i*w.2 i)
  let e : (Fin m → K × K) ≃ Vc m × Vc m :=
    ⟨fun f => (fun i => (f i).1, fun i => (f i).2),
     fun f i => (f.1 i, f.2 i), by intro f; rfl, by intro f; rfl⟩
  let loc (i : Fin m) := ∑ w : K × K, sign (c i*w.1*w.2 + a i*w.1 + b i*w.2)
  have fac := Finset.prod_univ_sum (ι := Fin m) (fun _ => (Finset.univ : Finset (K × K)))
    (fun i w => sign (c i*w.1*w.2 + a i*w.1 + b i*w.2))
  have eq : (∑ x : Vc m, ∑ y : Vc m, sign (∑ i : Fin m, (c i*x i*y i + a i*x i + b i*y i))) = ∏ i, loc i := calc
    _ = ∑ w : Vc m × Vc m, t w := by simp [t,Fintype.sum_prod_type,sign_sum]
    _ = ∑ f : Fin m → K × K, t (e f) := (e.sum_comp t).symm
    _ = _ := by simpa [e,t,loc] using fac.symm
  have each : ∀ x a b : K, |∑ w : K × K, sign (x*w.1*w.2 + a*w.1 + b*w.2)| ≤ if x=0 then 4 else 2 := by decide
  rw [eq,Finset.abs_prod]
  calc
    _ ≤ ∏ i, (if c i=0 then (4:ℤ) else 2) :=
      by
        have mono (S : Finset (Fin m)) : (∏ i ∈ S, |loc i|) ≤ ∏ i ∈ S, (if c i=0 then (4:ℤ) else 2) := by
          induction S using Finset.induction_on with
          | empty => simp
          | insert i S hi ih =>
            rw [Finset.prod_insert hi, Finset.prod_insert hi]
            exact mul_le_mul (each _ _ _) ih (Finset.prod_nonneg (fun _ _ => abs_nonneg _)) (by split <;> norm_num)
        exact mono _
    _ = _ := by
      rw [Finset.prod_ite]
      simp only [Finset.prod_const]
      have ht : (Finset.univ.filter fun i => c i ≠ 0).card + (Finset.univ.filter fun i => c i = 0).card = m := by
        simpa using Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => c i ≠ 0)
      have ex : 2*m - (Finset.univ.filter fun i => c i ≠ 0).card =
          2*(Finset.univ.filter fun i => c i = 0).card + (Finset.univ.filter fun i => c i ≠ 0).card := by omega
      rw [ex,pow_add,pow_mul]
      norm_num

theorem pair_cancel : ∀ u v : K, |sign u + sign v| = 1 + sign (u+v) := by decide

theorem pair_bound {ι : Type*} [Fintype ι] (u v : ι → K) :
    |∑ x : ι, (sign (u x) + sign (v x))| ≤ Fintype.card ι + |∑ x, sign (u x+v x)| := by
  calc
    _ ≤ ∑ x, |sign (u x) + sign (v x)| := Finset.abs_sum_le_sum_abs _ _
    _ = (Fintype.card ι : ℤ) + ∑ x, sign (u x+v x) := by simp [pair_cancel,Finset.sum_add_distrib]
    _ ≤ (Fintype.card ι : ℤ) + |∑ x, sign (u x+v x)| := by gcongr; exact le_abs_self _
end Code32052

namespace Code32052

theorem fibre_bound {m : ℕ} (c a b : Vc m) (offset : K) (P Q : Vc m × Vc m → K)
    (diff : ∀ w : Vc m × Vc m,
      P w + Q w = offset + ∑ i : Fin m, (c i*w.1 i*w.2 i + a i*w.1 i + b i*w.2 i)) :
    |∑ w : Vc m × Vc m, (sign (P w) + sign (Q w))| ≤
      2^(2*m) + 2^(2*m-(Finset.univ.filter fun i => c i ≠ 0).card) := by
  classical
  have bound := pair_bound P Q
  have tot : (∑ w : Vc m × Vc m, sign (P w + Q w)) =
      sign offset * (∑ x : Vc m, ∑ y : Vc m, sign (∑ i : Fin m, (c i*x i*y i + a i*x i + b i*y i))) := by
    simp_rw [diff, sign_add]
    rw [← Finset.mul_sum, Fintype.sum_prod_type]
  have u : ∀ o : K, |sign o| = 1 := by decide
  rw [tot,abs_mul,u,one_mul] at bound
  have cardinal : (Fintype.card (Vc m × Vc m) : ℤ) = 2^(2*m) := by
    simp [Vc,Fintype.card_prod,ZMod.card,two_mul,pow_add]
  rw [cardinal] at bound
  exact bound.trans (by gcongr; exact affine_diag_abs c a b)

end Code32052

namespace Code32052
open Previous

def second {n : ℕ} (Q : Vc n → K) (u v x : Vc n) :=
  Q (x+u+v) - Q (x+u) - Q (x+v) + Q x

def Stable {n : ℕ} (Q : Vc n → K) :=
  ∀ u v x, second Q u v x = second Q u v 0

theorem stable_add {n : ℕ} {f g : Vc n → K} (hf : Stable f) (hg : Stable g) :
    Stable (fun x => f x + g x) := by
  intro u v x
  unfold second
  have h1 := hf u v x
  have h2 := hg u v x
  unfold second at h1 h2
  linear_combination h1 + h2

theorem stable_sum {n : ℕ} {ι : Type*} (I : Finset ι) (f : ι → Vc n → K)
    (h : ∀ i, Stable (f i)) : Stable (fun x => ∑ i ∈ I, f i x) := by
  classical
  induction I using Finset.induction_on with
  | empty => intro u v x; simp [second]
  | insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact stable_add (h i) ih

theorem quad_stable {n : ℕ} {Q : Vc n → K} (hq : isQuad Q) : Stable Q := by
  obtain ⟨b,a,M,eq⟩ := hq
  rw [show Q = _ from funext eq]
  apply stable_add
  · intro u v x
    simp only [second,zero_add,dotProduct_add,dotProduct_zero]
    ring
  · apply stable_sum
    intro i
    apply stable_sum
    intro j u v x
    simp [second]
    ring

theorem square_four : ∀ a b c d : K, d-b-c+a ≠ 0 → |sign a+sign b+sign c+sign d| = 2 := by decide

theorem high_implies_affine {n : ℕ} {Q : Vc n → K} (hq : Stable Q)
    (big : (2:ℤ)^n < 2*|∑ x, sign (Q x)|) :
    ∃ (a : Vc n) (b : K), ∀ x, Q x = dotProduct a x + b := by
  classical
  have van (u v : Vc n) : second Q u v 0 = 0 := by
    by_contra ne
    have hh (x : Vc n) := square_four (Q x) (Q (x+u)) (Q (x+v)) (Q (x+u+v))
      (show second Q u v x ≠ 0 by rw [hq u v x]; exact ne)
    let T := ∑ x, sign (Q x)
    have shift (w : Vc n) : (∑ x, sign (Q (x+w))) = T := Equiv.sum_comp (Equiv.addRight w) (fun x => sign (Q x))
    have doubleShift : (∑ x, sign (Q (x+u+v))) = T := by simpa only [add_assoc] using shift (u+v)
    have bound := Finset.abs_sum_le_sum_abs
      (fun x : Vc n => sign (Q x)+sign (Q (x+u))+sign (Q (x+v))+sign (Q (x+u+v))) Finset.univ
    simp_rw [hh] at bound
    simp only [Finset.sum_add_distrib,shift,doubleShift] at bound
    change |T+T+T+T| ≤ _ at bound
    rw [show T+T+T+T = 4*T by ring, abs_mul] at bound
    have card : (∑ _x : Vc n, (2 : ℤ)) = 2^n*2 := by simp [Vc,ZMod.card]
    rw [card] at bound
    change (2:ℤ)^n < 2*|T| at big
    norm_num at bound
    omega
  let L : Vc n →ₗ[K] K := {
    toFun := fun x => Q x - Q 0
    map_add' := by
      intro x y
      have h := van x y
      simp only [second,zero_add] at h
      linear_combination h
    map_smul' := by
      intro t x
      rcases cases_two t with rfl|rfl <;> simp }
  obtain ⟨a,ha⟩ := linear_coord_dot L
  exact ⟨a,Q 0,fun x => by rw [← ha]; change _ = (Q x - Q 0) + Q 0; ring⟩

end Code32052

namespace Code32052
theorem geom_mass (j : ℕ) :
    (∑ v : Vc j, (1/2 : ℚ) ^ (Finset.univ.filter fun i => v i ≠ 0).card) = (3/2 : ℚ)^j := by
  classical
  let factor (t : K) : ℚ := if t = 0 then 1 else 1/2
  have fac (v : Vc j) : (1/2 : ℚ)^(Finset.univ.filter fun i => v i ≠ 0).card =
      ∏ i, factor (v i) := by
    unfold factor
    rw [Finset.prod_ite]
    simp
  simp_rw [fac]
  have h := Finset.prod_univ_sum (ι := Fin j) (fun _ => (Finset.univ : Finset K)) (fun _ t => factor t)
  have enum : (Finset.univ : Finset K) = {0,1} := by decide
  have local_sum : (∑ t : K, factor t) = 3/2 := by rw [enum]; norm_num [factor]
  simpa [local_sum,div_pow] using h.symm

theorem info_bound {j : ℕ} {H : Type*} [Fintype H] (coord : H ≃ Vc j)
    (w : H → ℕ) (hw : ∀ u, (Finset.univ.filter fun i => coord u i ≠ 0).card ≤ w u) :
    (∑ u, (1/2 : ℚ)^(w u)) ≤ (3/2 : ℚ)^j := by
  calc
    _ ≤ ∑ u, (1/2 : ℚ)^(Finset.univ.filter fun i => coord u i ≠ 0).card := by
      apply Finset.sum_le_sum
      intro u _
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hw u)
    _ = _ := (coord.sum_comp (fun v => (1/2 : ℚ)^(Finset.univ.filter fun i => v i ≠ 0).card)).trans (geom_mass j)

theorem dim_three_bound {j : ℕ} (hj : 3 ≤ j) :
    (3/2 : ℚ)^j ≤ (2:ℚ)^j/2 := by
  have a : (3/4 : ℚ)^j ≤ (3/4 : ℚ)^3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
  have h : (3/4 : ℚ)^j ≤ 1/2 := a.trans (by norm_num)
  have p : (0:ℚ) < 2^j := by positivity
  have eq : (3/2 : ℚ)^j = (3/4 : ℚ)^j * 2^j := by rw [← mul_pow]; norm_num
  rw [eq]
  linarith [mul_le_mul_of_nonneg_right h p.le]
end Code32052

namespace Code32052
theorem information_set {m n : ℕ} (B : Vc n →ₗ[K] Vc m) (inj : Function.Injective B) :
    ∃ I : Finset (Fin m), I.card = n ∧ Function.Bijective (fun x : Vc n => fun i : ↥I => B x i) := by
  classical
  let f (i : Fin m) := (LinearMap.proj (R := K) (φ := fun _ : Fin m => K) i).comp B
  obtain ⟨T,_,_,span,ind⟩ := exists_linearIndepOn_extension (linearIndepOn_empty K f) (Set.empty_subset Set.univ)
  let I := T.toFinset
  let proj : Vc n →ₗ[K] (↥I → K) := LinearMap.pi (fun i => f i)
  have pinj : Function.Injective proj := by
    rw [← LinearMap.ker_eq_bot]
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply inj
    rw [map_zero]
    ext i
    change f i x = 0
    have van : Submodule.span K (f '' T) ≤ LinearMap.ker (LinearMap.applyₗ (R := K) x : (Vc n →ₗ[K] K) →ₗ[K] K) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,hj,rfl⟩
      exact congrFun hx ⟨j,by simpa [I] using hj⟩
    exact van (span ⟨i,Set.mem_univ _,rfl⟩)
  have hle := ind.fintype_card_le_finrank
  have h1 : I.card ≤ n := by simpa [I,Vc,Subspace.dual_finrank_eq,Module.finrank_pi] using hle
  have h2 : n ≤ I.card := by
    simpa [Vc,Module.finrank_pi] using LinearMap.finrank_le_finrank_of_injective pinj
  have eq := Nat.le_antisymm h1 h2
  refine ⟨I,eq,pinj,?_⟩
  have card : Fintype.card (Vc n) = Fintype.card (↥I → K) := by simp [Vc,eq]
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨pinj,card⟩ |>.surjective
end Code32052

namespace Code32052
theorem invisible_directions {m k p j : ℕ} (A : Fin m → Vc k)
    (M : Vc p →ₗ[K] Vc k) (bad : Finset (Fin m)) (hs : j+bad.card ≤ p) :
    ∃ R : Vc j →ₗ[K] Vc p, Function.Injective R ∧
      ∀ v i, i ∈ bad → dotProduct (A i) (M (R v)) = 0 := by
  classical
  let obs (i : ↥bad) : Vc p →ₗ[K] K := {
    toFun := fun x => dotProduct (A i) (M x)
    map_add' := by intro; simp [dotProduct_add]
    map_smul' := by intro; simp [dotProduct_smul] }
  let O := LinearMap.pi obs
  let ker := LinearMap.ker O
  let dim := Module.finrank K ker
  have hn : j ≤ dim := by
    have sum : Module.finrank K O.range + dim = p := by
      calc
        _ = Module.finrank K (Vc p) := O.finrank_range_add_finrank_ker
        _ = p := by simp [Vc,Module.finrank_pi]
    have bound : Module.finrank K O.range ≤ bad.card := calc
      _ ≤ Module.finrank K (↥bad → K) := Submodule.finrank_le O.range
      _ = bad.card := by simp [Module.finrank_pi]
    omega
  let e : Vec dim ≃ₗ[K] ker := LinearEquiv.ofFinrankEq _ _ (by simp [Vec,Module.finrank_pi,dim])
  let R := ker.subtype.comp (e.toLinearMap.comp (extendByZero hn))
  refine ⟨R,ker.subtype_injective.comp (e.injective.comp (inject_extend hn)),?_⟩
  intro v i hi
  exact congrFun (e (extendByZero hn v)).property ⟨i,hi⟩

noncomputable def code {m k : ℕ} (A : Fin m → Vc k) : Vc k →ₗ[K] Vc m where
  toFun v i := dotProduct (A i) v
  map_add' x y := by ext; simp [dotProduct_add]
  map_smul' a x := by ext; simp [dotProduct_smul]

theorem code_mass {m k j : ℕ} (A : Fin m → Vc k) (M : Vc j →ₗ[K] Vc k)
    (inj : Function.Injective M) (dist : ∀ a : Vc k, a ≠ 0 → 0 < weight (code A a)) :
    (∑ u : Vc j, (1/2 : ℚ) ^ weight (code A (M u))) ≤ (3/2 : ℚ)^j := by
  classical
  have ci : Function.Injective (code A) := by
    rw [← LinearMap.ker_eq_bot]
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    by_contra ne
    have h := dist x ne
    simp [hx,weight] at h
  let B := (code A).comp M
  obtain ⟨I,hI,hproj⟩ := information_set B (ci.comp inj)
  let idx : ↥I ≃ Fin j := Fintype.equivFinOfCardEq (by simpa using hI)
  let project (v : Vc j) (i : ↥I) := B v i
  let coord : Vc j ≃ Vc j := (Equiv.ofBijective project hproj).trans (Equiv.arrowCongr idx (Equiv.refl K))
  apply info_bound coord
  intro u
  let emb : Fin j ↪ Fin m := idx.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have pt (i : Fin j) : coord u i = B u (emb i) := rfl
  have hset : (Finset.univ.filter (fun i => coord u i ≠ 0)).map emb ⊆ (Finset.univ.filter fun i => B u i ≠ 0) := by
    intro i hi
    obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
  simpa [weight,B] using (Finset.card_le_card hset)

end Code32052

namespace Code32052
theorem split_flat {s k t : ℕ} (L : Vc s →ₗ[K] Vc k) (D : Vc s →ₗ[K] Vc t)
    (hLD : Function.Injective (L.prod D)) :
    let p := Module.finrank K (LinearMap.range L)
    ∃ (I : Finset (Fin t)) (M : Vc p →ₗ[K] Vc k)
      (E : (Vc p × (↥I → K)) ≃ₗ[K] Vc s),
      I.card + p = s ∧ Function.Injective M ∧
      (∀ u v, L (E (u,v)) = M u) ∧ ∀ u v (i : ↥I), D (E (u,v)) i = v i := by
  classical
  intro p
  let h := Module.finrank K (LinearMap.ker L)
  let ei : Vc h ≃ₗ[K] LinearMap.ker L := LinearEquiv.ofFinrankEq _ _ (by simp [Vc,h,Module.finrank_pi])
  let er : Vc p ≃ₗ[K] LinearMap.range L := LinearEquiv.ofFinrankEq _ _ (by simp [Vc,p,Module.finrank_pi])
  let DK := D.comp ((LinearMap.ker L).subtype.comp ei.toLinearMap)
  have dki : Function.Injective DK := by
    intro u v eq
    apply ei.injective
    apply Subtype.ext
    apply hLD
    apply Prod.ext
    · exact (ei u).property.trans (ei v).property.symm
    · exact eq
  obtain ⟨I,hI,bij⟩ := information_set DK dki
  let di : Vc s →ₗ[K] (↥I → K) := LinearMap.pi (fun i => (LinearMap.proj (R := K) (φ := fun _ : Fin t => K) i.val).comp D)
  let P := (er.symm.toLinearMap.comp L.rangeRestrict).prod di
  have pinj : Function.Injective P := by
    rw [← LinearMap.ker_eq_bot]
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have e1 : er.symm (L.rangeRestrict x) = 0 := congrArg Prod.fst hx
    have e2 : di x = 0 := congrArg Prod.snd hx
    have lx : L x = 0 := congrArg Subtype.val (er.symm.injective (e1.trans er.symm.map_zero.symm))
    let z : LinearMap.ker L := ⟨x,lx⟩
    have eq : ei.symm z = 0 := by
      apply bij.1
      funext i
      change D (ei (ei.symm z)).val i = D (ei 0).val i
      rw [ei.apply_symm_apply, ei.map_zero]
      change D x i = D 0 i
      rw [map_zero]
      exact congrFun e2 i
    have eqz : z = 0 := ei.symm.injective (eq.trans ei.symm.map_zero.symm)
    exact congrArg Subtype.val eqz
  have hp : I.card + p = s := by
    rw [hI, Nat.add_comm]
    calc
      _ = Module.finrank K (Vc s) := L.finrank_range_add_finrank_ker
      _ = s := by simp [Vc,Module.finrank_pi]
  have cc : Fintype.card (Vc s) = Fintype.card (Vc p × (↥I → K)) := by
    simp [Vc,← hp,pow_add,mul_comm]
  let equiv := LinearEquiv.ofBijective P ((Fintype.bijective_iff_injective_and_card _).mpr ⟨pinj,cc⟩)
  let E := equiv.symm
  have inv (w) : P (E w) = w := equiv.apply_symm_apply w
  refine ⟨I,(LinearMap.range L).subtype.comp er.toLinearMap,E,hp,
    (LinearMap.range L).subtype_injective.comp er.injective,?_,?_⟩
  · intro u v
    have eq : er.symm (L.rangeRestrict (E (u,v))) = u := congrArg Prod.fst (inv (u,v))
    exact congrArg Subtype.val (er.symm_apply_eq.mp eq)
  · intro u v i
    exact congrFun (congrArg Prod.snd (inv (u,v))) i
end Code32052
namespace Code32052
noncomputable def avg {X : Type*} [Fintype X] (f : X → ℚ) : ℚ :=
  (∑ x, f x) / (Fintype.card X : ℚ)

theorem avg_const {X : Type*} [Fintype X] [Nonempty X] (c : ℚ) : avg (fun _ : X => c) = c := by
  simp [avg, Fintype.card_ne_zero]
theorem avg_mono {X : Type*} [Fintype X] {f g : X → ℚ} (h : ∀ x, f x ≤ g x) : avg f ≤ avg g := by
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x))
  positivity
theorem avg_shift {n} (a : Vc n) (f : Vc n → ℚ) : avg (fun x => f (a+x)) = avg f := by
  unfold avg
  rw [show (∑ x, f (a+x)) = ∑ x, f x from Equiv.sum_comp (Equiv.addLeft a) f]
theorem abs_avg {X : Type*} [Fintype X] (f : X → ℚ) : |avg f| ≤ avg (fun x => |f x|) := by
  simp only [avg,abs_div,abs_of_nonneg (Nat.cast_nonneg (Fintype.card X) : (0:ℚ) ≤ _) ]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
theorem avg_swap {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → ℚ) :
    avg (fun x => avg (f x)) = avg (fun y => avg (fun x => f x y)) := by
  simp only [avg,div_eq_mul_inv,← Finset.sum_mul]
  rw [Finset.sum_comm]; ring

theorem remove_cosets {p j : ℕ} (R : Vc j → Vc p) (f : Vc p → ℚ) (t : ℚ)
    (h : ∀ x : Vc p, |avg (fun v => f (x+R v))| ≤ t) : |avg f| ≤ t := by
  have eq : avg f = avg (fun x : Vc p => avg (fun v => f (x+R v))) := by
    rw [avg_swap]
    simp_rw [show ∀ v : Vc j, avg (fun x => f (x+R v)) = avg f from fun v => by simpa only [add_comm] using avg_shift (R v) f]
    exact (avg_const _).symm
  rw [eq]
  exact (abs_avg _).trans ((avg_mono h).trans_eq (avg_const t))

theorem anchor_bound {j : ℕ} (v : Vc j → ℚ) (w : Vc j → ℕ) (target : ℚ) (ht : 1/2 ≤ target)
    (hw : avg (fun z => (1/2:ℚ)^w z) ≤ target)
    (h : ∀ anchor, 1/2 < |v anchor| → ∀ z, |v (anchor+z)| ≤ (1/2:ℚ)^w z) : |avg v| ≤ target := by
  by_cases low : ∀ x, |v x| ≤ 1/2
  · exact (abs_avg v).trans ((avg_mono low).trans ((avg_const (1/2 : ℚ)).le.trans ht))
  · push_neg at low
    obtain ⟨a,ha⟩ := low
    rw [← avg_shift a v]
    exact (abs_avg _).trans ((avg_mono (h a ha)).trans hw)

theorem many_mass {j k m : ℕ} (A : Fin m → Vc k) (M : Vc j →ₗ[K] Vc k)
    (inj : Function.Injective M) (dist : ∀ a : Vc k, a ≠ 0 → 0 < weight (code A a))
    (hj : 3 ≤ j) : avg (fun u : Vc j => (1/2:ℚ)^weight (code A (M u))) ≤ 1/2 := by
  unfold avg
  have card : (Fintype.card (Vc j) : ℚ) = 2^j := by simp [Vc,ZMod.card]
  rw [card,div_le_iff₀ (by positivity)]
  exact (code_mass A M inj dist).trans ((dim_three_bound hj).trans_eq (by ring))

end Code32052
namespace Code32052
open Previous

theorem shifted_bound {X : Type*} [Fintype X] [Nonempty X] {p : ℕ}
    (R : X → Vc p) (f : Vc p → ℚ) (t : ℚ)
    (h : ∀ z, |avg (fun v => f (z+R v))| ≤ t) : |avg f| ≤ t := by
  have eq : avg f = avg (fun z : Vc p => avg (fun v => f (z+R v))) := by
    rw [avg_swap]
    simp_rw [show ∀ v : X, avg (fun z => f (z+R v)) = avg f from fun v => by simpa only [add_comm] using avg_shift (R v) f]
    exact (avg_const _).symm
  rw [eq]
  exact (abs_avg _).trans ((avg_mono h).trans_eq (avg_const t))

theorem independent_pairs {m h : ℕ}
    (X Y : Vc h →ₗ[K] Vc m) (R : (Vc m × Vc m) →ₗ[K] Vc h)
    (hx : ∀ u v, X (R (u,v)) = u) (hy : ∀ u v, Y (R (u,v)) = v)
    (L : Vc h →ₗ[K] K) (b : K) :
    |avg (fun z : Vc h => (sign (b + L z + dotProduct (X z) (Y z)) : ℚ))| ≤ (1/2 : ℚ)^m := by
  classical
  apply shifted_bound R
  intro z
  let Lu := L.comp (R.comp (LinearMap.inl K (Vc m) (Vc m)))
  let Lv := L.comp (R.comp (LinearMap.inr K (Vc m) (Vc m)))
  obtain ⟨a,ha⟩ := linear_coord_dot Lu
  obtain ⟨c,hc⟩ := linear_coord_dot Lv
  have lr (u v : Vc m) : L (R (u,v)) = dotProduct a u + dotProduct c v := by
    rw [← ha, ← hc]
    change L (R (u,v)) = L (R (u,0)) + L (R (0,v))
    rw [← L.map_add, ← R.map_add]; simp
  let offset := b + L z + dotProduct (X z) (Y z)
  let a' : Vc m := a + Y z
  let c' : Vc m := c + X z
  let q (w : Vc m × Vc m) : K := ∑ i : Fin m, ((1:K)*w.1 i*w.2 i + a' i*w.1 i + c' i*w.2 i)
  have point (w : Vc m × Vc m) :
      sign (b+L (z+R w)+dotProduct (X (z+R w)) (Y (z+R w))) = sign offset * sign (q w) := by
    obtain ⟨u,v⟩ := w
    rw [← sign_add]
    congr 1
    simp only [map_add,hx,hy,lr,offset,q,a',c',dotProduct_add,add_dotProduct]
    simp only [dotProduct,Pi.add_apply,one_mul,add_mul,Finset.sum_add_distrib]
    rw [show (∑ i, u i * Y z i) = ∑ i, Y z i * u i by apply Finset.sum_congr rfl; intro i _; ring]
    ring
  have norm : |∑ w, sign (q w)| ≤ (2:ℤ)^m := by
    rw [Fintype.sum_prod_type]
    have bound := affine_diag_abs (fun _ : Fin m => (1:K)) a' c'
    simpa [q,two_mul] using bound
  have sgn : ∀ u : K, |sign u| = 1 := by decide
  have bound : |∑ w : Vc m × Vc m, sign (b+L (z+R w)+dotProduct (X (z+R w)) (Y (z+R w)))| ≤ (2:ℤ)^m := by
    simp_rw [point]
    rw [← Finset.mul_sum,abs_mul,sgn,one_mul]
    exact norm
  have card : (Fintype.card (Vc m × Vc m) : ℚ) = (2:ℚ)^m*2^m := by simp [Vc,ZMod.card]
  unfold avg
  rw [card,abs_div,abs_of_nonneg (by positivity : (0:ℚ) ≤ 2^m*2^m),div_le_iff₀ (by positivity)]
  have rat : |∑ w : Vc m × Vc m, (sign (b+L (z+R w)+dotProduct (X (z+R w)) (Y (z+R w))) : ℚ)| ≤ (2:ℚ)^m := by
    exact_mod_cast bound
  convert rat using 1
  rw [div_pow,one_pow]
  field_simp
end Code32052
namespace Code32052
noncomputable def writePairs {m h : ℕ} (e : (Fin m ⊕ Fin m) ↪ Fin h) :
    (Vc m × Vc m) →ₗ[K] Vc h := by
  classical
  let idx (i : Fin h) : Option (Fin m ⊕ Fin m) :=
    if hp : ∃ j, e j = i then some hp.choose else none
  let slot (i : Fin h) : (Vc m × Vc m) →ₗ[K] K :=
    match idx i with
    | some (.inl j) => (LinearMap.proj j).comp (LinearMap.fst K _ _)
    | some (.inr j) => (LinearMap.proj j).comp (LinearMap.snd K _ _)
    | none => 0
  exact LinearMap.pi slot

theorem writePairs_at {m h : ℕ} (e : (Fin m ⊕ Fin m) ↪ Fin h) (j : Fin m ⊕ Fin m)
    (x y : Vc m) : writePairs e (x,y) (e j) = Sum.elim x y j := by
  classical
  have eq (hp : ∃ i, e i = e j) : hp.choose = j := e.injective hp.choose_spec
  have hp : ∃ i, e i = e j := ⟨j,rfl⟩
  cases j <;> simp [writePairs,hp,eq]

noncomputable def readSide {m h : ℕ} (e : Fin m → Fin h) : Vc h →ₗ[K] Vc m :=
  LinearMap.pi (fun i => LinearMap.proj (e i))

theorem disjoint_pairs {m h : ℕ} (e : (Fin m ⊕ Fin m) ↪ Fin h) (L : Vc h →ₗ[K] K) (b : K) :
    |avg (fun z : Vc h => (sign (b + L z + ∑ i, z (e (.inl i))*z (e (.inr i))) : ℚ))| ≤ (1/2 : ℚ)^m := by
  apply independent_pairs (readSide (fun i => e (.inl i))) (readSide (fun i => e (.inr i))) (writePairs e)
  · intro u v; ext i; exact writePairs_at e (.inl i) u v
  · intro u v; ext i; exact writePairs_at e (.inr i) u v

end Code32052
namespace Code32052
open Previous

def Affine {n : ℕ} (f : Vc n → K) := ∃ (L : Vc n →ₗ[K] K) (b : K), ∀ x, f x = L x + b

theorem affine_of_van {n} (f : Vc n → K) (van : ∀ u v, second f u v 0 = 0) : Affine f := by
  let L : Vc n →ₗ[K] K := {
    toFun x := f x - f 0
    map_add' x y := by
      have h := van x y
      simp only [second,zero_add] at h
      linear_combination h
    map_smul' t x := by rcases cases_two t with rfl|rfl <;> simp }
  exact ⟨L,f 0,fun x => by change _ = (f x-f 0)+f 0; ring⟩
theorem diff_affine {m n} (f : Vc n → K) (hf : Stable f) (J : Vc m →ₗ[K] Vc n) (a b : Vc n) :
    Affine (fun z => f (a+J z) - f (b+J z)) := by
  apply affine_of_van
  intro u v
  have h := (hf (J u) (J v) a).trans (hf (J u) (J v) b).symm
  simp only [second,add_assoc] at h
  simp only [second,zero_add,map_zero,map_add,add_zero]
  linear_combination h

theorem stable_comp {m n} {f : Vc n → K} (hf : Stable f) (J : Vc m →ₗ[K] Vc n) (a : Vc n) :
    Stable (fun z => f (a+J z)) := by
  intro u v x
  have h := (hf (J u) (J v) (a+J x)).trans (hf (J u) (J v) a).symm
  simpa only [second,map_zero,map_add,zero_add,add_zero,add_assoc] using h

theorem affine_add {n} {f g : Vc n → K} (hf : Affine f) (hg : Affine g) :
    Affine (fun x => f x + g x) := by
  obtain ⟨L,b,hu⟩ := hf
  obtain ⟨M,c,hv⟩ := hg
  exact ⟨L+M,b+c,fun x => by simp [hu,hv]; ring⟩

theorem stable_product {n} (L M : Vc n →ₗ[K] K) (a b : K) :
    Stable (fun z => (a+L z)*(b+M z)) := by
  intro u v x
  simp only [second,map_zero,map_add,zero_add]
  ring

end Code32052
namespace Code32052
theorem affine_const {n} (c : K) : Affine (fun _ : Vc n => c) :=
  ⟨0,c,by simp⟩

theorem affine_sub {n} {f g : Vc n → K} (hf : Affine f) (hg : Affine g) :
    Affine (fun x => f x - g x) := by
  obtain ⟨L,b,hu⟩ := hf
  obtain ⟨M,c,hv⟩ := hg
  exact ⟨L-M,b-c,fun x => by simp [hu,hv]; ring⟩

theorem affine_sum {n} {ι : Type*} (I : Finset ι) (f : ι → Vc n → K) (H : ∀ i, Affine (f i)) :
    Affine (fun x => ∑ i ∈ I, f i x) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using (affine_const (n := n) 0)
  | insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact affine_add (H i) ih

theorem stable_sub {n} {f g : Vc n → K} (hf : Stable f) (hg : Stable g) :
    Stable (fun x => f x - g x) := by
  intro u v x
  have h₁ := hf u v x
  have h₂ := hg u v x
  unfold second at *
  linear_combination h₁ - h₂

theorem stable_scaled {n} {f : Vc n → K} (hf : Stable f) (a : K) :
    Stable (fun x => a*f x) := by
  intro u v x
  have h := hf u v x
  unfold second at *
  linear_combination a*h

theorem atom_diff {n} (c d a b a' b' : K) (L M : Vc n →ₗ[K] K) :
    Affine (fun z => c*(a+L z)*(b+M z)-d*(a'+L z)*(b'+M z)-(c-d)*L z*M z) := by
  refine ⟨(c*b-d*b') • L + (c*a-d*a') • M,c*a*b-d*a'*b',?_⟩
  intro z
  simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  ring

def fibreError {h m s : ℕ} (f : Vc s → K) (a : Vc s) (J : Vc h →ₗ[K] Vc s)
    (constant : K) (c x y : Vc m) (L M : Fin m → Vc h →ₗ[K] K) (z : Vc h) : K :=
  constant + ∑ i, c i*(x i+L i z)*(y i+M i z) - f (a+J z)

theorem fibre_stable {h m s : ℕ} (f : Vc s → K) (hf : Stable f) (a : Vc s) (J : Vc h →ₗ[K] Vc s)
    (constant : K) (c x y : Vc m) (L M : Fin m → Vc h →ₗ[K] K) :
    Stable (fibreError f a J constant c x y L M) := by
  apply stable_sub _ (stable_comp hf J a)
  apply stable_add (show Stable (fun _ : Vc h => constant) by intro _ _ _; rfl)
  apply stable_sum
  intro i
  simpa only [mul_assoc] using stable_scaled (stable_product (L i) (M i) (x i) (y i)) (c i)

theorem fibre_difference {h m s : ℕ} (f : Vc s → K) (hf : Stable f) (a b : Vc s) (J : Vc h →ₗ[K] Vc s)
    (u v : K) (c d x y x' y' : Vc m) (L M : Fin m → Vc h →ₗ[K] K) :
    Affine (fun z => fibreError f a J u c x y L M z - fibreError f b J v d x' y' L M z -
      ∑ i, (c i-d i)*L i z*M i z) := by
  have atms := affine_sum Finset.univ _ (fun i => atom_diff (c i) (d i) (x i) (y i) (x' i) (y' i) (L i) (M i))
  have res := affine_sub (affine_add (affine_const (u-v)) atms) (diff_affine f hf J a b)
  convert res using 1
  funext z
  simp only [fibreError,Finset.sum_sub_distrib]
  ring
end Code32052
namespace Code32052
def b1 (x : K) : Vc 1 := fun _ => x
def b2 (x y : K) : Vc 2 := ![x,y]

theorem sum_two (f : K → ℚ) : (∑ x, f x) = f 0 + f 1 := by
  have all : (Finset.univ : Finset K) = {0,1} := by decide
  rw [all,Finset.sum_insert (by decide),Finset.sum_singleton]

theorem mass_one {m k d : ℕ} (A : Fin m → Vc k) (M : Vc 1 →ₗ[K] Vc k)
    (inj : Function.Injective M) (dist : ∀ a : Vc k, a ≠ 0 → d ≤ weight (code A a)) :
    avg (fun u => (1/2 : ℚ)^weight (code A (M u))) ≤ (1+(1/2:ℚ)^d)/2 := by
  let e : K ≃ Vc 1 := ⟨b1,fun v => v 0,fun _ => rfl,by intro v; ext i; fin_cases i; rfl⟩
  let f (v : Vc 1) := (1/2:ℚ)^weight (code A (M v))
  have bound : f (b1 1) ≤ (1/2:ℚ)^d := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    apply dist
    intro h
    have eq := inj (h.trans M.map_zero.symm)
    exact (show b1 1 ≠ 0 by decide) eq
  change avg f ≤ _
  unfold avg
  rw [← e.sum_comp f,sum_two]
  change (f 0 + f (b1 1)) / _ ≤ _
  have z : f 0 = 1 := by simp [f,weight]
  have card : Fintype.card (Vc 1) = 2 := by simp [Vc,ZMod.card]
  rw [z,card]; push_cast; linarith

theorem two_numeric (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h3 : ¬(p=1 ∧ q=1 ∧ r=1)) :
    let s := (1+(1/2:ℚ)^p+(1/2:ℚ)^q+(1/2:ℚ)^r)/4
    s ≤ 9/16 ∧ (¬((p=1 ∧ q=1) ∨ (p=1 ∧ r=1) ∨ (q=1 ∧ r=1)) → s ≤ 1/2) := by
  intro s
  have small (i : ℕ) (h : 1 ≤ i) : (1/2 : ℚ)^i ≤ 1/2 := calc
    _ ≤ (1/2:ℚ)^1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) h
    _ = _ := by ring
  have tiny (i : ℕ) (h : i ≠ 1) (pos : 0 < i) : (1/2 : ℚ)^i ≤ 1/4 := calc
    _ ≤ (1/2:ℚ)^2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = _ := by norm_num
  have a := small p hp
  have b := small q hq
  have c := small r hr
  have low₁ : p≠1 ∨ q≠1 ∨ r≠1 := by tauto
  constructor
  · dsimp [s]
    rcases low₁ with non | non | non
    · linarith [tiny p non hp]
    · linarith [tiny q non hq]
    · linarith [tiny r non hr]
  · intro one
    have low₂ : (p≠1 ∧ q≠1) ∨ (p≠1 ∧ r≠1) ∨ (q≠1 ∧ r≠1) := by tauto
    dsimp [s]
    rcases low₂ with ⟨x,y⟩ | ⟨x,y⟩ | ⟨x,y⟩
    · linarith [tiny p x hp,tiny q y hq]
    · linarith [tiny p x hp,tiny r y hr]
    · linarith [tiny q x hq,tiny r y hr]
end Code32052
namespace Code32052
theorem affine_of_large_avg {h} {F : Vc h → K} (st : Stable F)
    (big : (1/2:ℚ) < |avg (fun z => (sign (F z) : ℚ))|) : Affine F := by
  classical
  have cd : (Fintype.card (Vc h) : ℚ) = 2^h := by simp [Vc,ZMod.card]
  unfold avg at big
  rw [cd,abs_div,abs_of_nonneg (by positivity : (0:ℚ) ≤ 2^h),lt_div_iff₀ (by positivity)] at big
  have rat : (2:ℚ)^h < 2*|∑ z, (sign (F z) : ℚ)| := by linarith
  have ints : (2:ℤ)^h < 2*|∑ z, sign (F z)| := by exact_mod_cast rat
  obtain ⟨a,b,ha⟩ := high_implies_affine st ints
  let L : Vc h →ₗ[K] K := {
    toFun z := dotProduct a z
    map_add' x y := dotProduct_add a x y
    map_smul' t x := dotProduct_smul t a x }
  exact ⟨L,b,ha⟩

theorem anchor_slice {h s m w : ℕ} (q : Vc s → K) (qs : Stable q)
    (a b : Vc s) (J : Vc h →ₗ[K] Vc s) (u v : K) (c d x y x' y' : Vc m)
    (L M : Fin m → Vc h →ₗ[K] K) (e : (Fin w ⊕ Fin w) ↪ Fin h)
    (free : ∀ z, (∑ i, (c i-d i)*L i z*M i z) = ∑ i, z (e (.inl i))*z (e (.inr i)))
    (big : (1/2:ℚ) < |avg (fun z => (sign (fibreError q b J v d x' y' L M z) : ℚ))|) :
    |avg (fun z => (sign (fibreError q a J u c x y L M z) : ℚ))| ≤ (1/2:ℚ)^w := by
  have anch := affine_of_large_avg (fibre_stable q qs b J v d x' y' L M) big
  have dif := fibre_difference q qs a b J u v c d x y x' y' L M
  obtain ⟨ell,t,he⟩ := affine_add dif anch
  have shape (z : Vc h) : fibreError q a J u c x y L M z = t + ell z + ∑ i, z (e (.inl i))*z (e (.inr i)) := by
    have hz := he z
    rw [← free]
    linear_combination hz
  simp_rw [shape]
  exact disjoint_pairs e ell t

end Code32052
namespace Code32052
def marked {m t : ℕ} (xy : (Fin m ⊕ Fin m) ↪ Fin t) (I : Finset (Fin t)) :=
  Finset.univ.filter fun i => xy (.inl i) ∉ I ∨ xy (.inr i) ∉ I

theorem marked_count {m t} (xy : (Fin m ⊕ Fin m) ↪ Fin t) (I : Finset (Fin t)) :
    (marked xy I).card ≤ t-I.card := by
  classical
  let pick (i : Fin m) := if xy (.inl i) ∈ I then xy (.inr i) else xy (.inl i)
  have has {i} (hi : i ∈ marked xy I) : pick i ∈ Iᶜ := by
    have hm := (Finset.mem_filter.mp hi).2
    by_cases h : xy (.inl i) ∈ I <;> simp_all [pick]
  have inj : Function.Injective pick := by
    intro i j eq
    unfold pick at eq
    split at eq <;> split at eq <;> simpa using xy.injective eq
  have bound := Finset.card_le_card_of_injOn pick (fun i hi => has hi) inj.injOn
  simpa [Finset.card_compl] using bound

theorem free_pairs {m t : ℕ} (xy : (Fin m ⊕ Fin m) ↪ Fin t) (I : Finset (Fin t))
    (idx : ↥I ≃ Fin I.card) (c : Vc m) (hc : ∀ i ∈ marked xy I, c i = 0)
    (L M : Fin m → Vc I.card → K)
    (left : ∀ i (hi : xy (.inl i) ∈ I) z, L i z = z (idx ⟨_,hi⟩))
    (right : ∀ i (hi : xy (.inr i) ∈ I) z, M i z = z (idx ⟨_,hi⟩)) :
    ∃ e : (Fin (weight c) ⊕ Fin (weight c)) ↪ Fin I.card,
      ∀ z, (∑ i, c i * L i z * M i z) = ∑ i, z (e (.inl i))*z (e (.inr i)) := by
  classical
  let S := Finset.univ.filter fun i => c i ≠ 0
  let enum : Fin (weight c) ≃ ↥S := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; rfl)).symm
  have good (i : ↥S) : xy (.inl i.val) ∈ I ∧ xy (.inr i.val) ∈ I := by
    have hn := (Finset.mem_filter.mp i.property).2
    by_contra! h
    exact hn (hc _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by tauto⟩))
  let ix : (Fin (weight c) ⊕ Fin (weight c)) → ↥I :=
    Sum.elim (fun j => ⟨xy (.inl (enum j).val),(good _).1⟩)
             (fun j => ⟨xy (.inr (enum j).val),(good _).2⟩)
  have ii : Function.Injective ix := by
    intro i j eq
    have ev := congrArg Subtype.val eq
    cases i <;> cases j <;> simp [ix] at ev ⊢ <;> grind
  let e := (⟨ix,ii⟩ : _ ↪ _).trans idx.toEmbedding
  refine ⟨e,fun z => ?_⟩
  have on (i : ↥S) : c i = 1 := (cases_two _).resolve_left (Finset.mem_filter.mp i.property).2
  calc
    _ = ∑ i ∈ S, c i * L i z * M i z := by
      apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro i hi hn
      have hzero : c i = 0 := by simpa [S] using hn
      simp [hzero]
    _ = ∑ i : ↥S, L i z * M i z := by rw [← Finset.sum_attach]; simp [on]
    _ = ∑ i : Fin (weight c), L (enum i) z * M (enum i) z := (Equiv.sum_comp enum _).symm
    _ = _ := Finset.sum_congr rfl (fun i _ => by rw [left _ (good _).1,right _ (good _).2]; rfl)
end Code32052
namespace Code32052
theorem plane_mass {k m : ℕ} (A : Fin m → Vc k) (M : Vc 2 →ₗ[K] Vc k)
    (hi : Function.Injective M)
    (dist : ∀ a : Vc k, a ≠ 0 → 0 < weight (code A a)) :
    let hasTwo := ∃ a b : Vc k, a ≠ b ∧ weight (code A a) = 1 ∧ weight (code A b) = 1
    let mass := avg (fun v : Vc 2 => (1/2:ℚ)^weight (code A (M v)))
    mass ≤ 9/16 ∧ (¬hasTwo → mass ≤ 1/2) := by
  intro hasTwo mass
  classical
  let e : (K × K) ≃ Vc 2 :=
    ⟨fun w => b2 w.1 w.2,fun f => (f 0,f 1),by intro w; cases w; rfl,by intro f; ext i; fin_cases i <;> rfl⟩
  let P := M (b2 0 1)
  let Q := M (b2 1 0)
  let R := M (b2 1 1)
  have nP : P ≠ 0 := fun h => (show b2 0 1 ≠ 0 by decide) (hi (h.trans M.map_zero.symm))
  have nQ : Q ≠ 0 := fun h => (show b2 1 0 ≠ 0 by decide) (hi (h.trans M.map_zero.symm))
  have nR : R ≠ 0 := fun h => (show b2 1 1 ≠ 0 by decide) (hi (h.trans M.map_zero.symm))
  have pq : P ≠ Q := fun h => (show b2 0 1 ≠ b2 1 0 by decide) (hi h)
  have pr : P ≠ R := fun h => (show b2 0 1 ≠ b2 1 1 by decide) (hi h)
  have qr : Q ≠ R := fun h => (show b2 1 0 ≠ b2 1 1 by decide) (hi h)
  have eqr : P + Q = R := by
    change M _ + M _ = M _
    rw [← M.map_add]; congr 1; decide
  have ci (v : Vc k) (hv : ∀ i, dotProduct (A i) v = 0) : v=0 := by
    by_contra ne
    have low := dist v ne
    simp [weight,code,hv] at low
  let w := fun v : Vc k => weight (code A v)
  have no3 : ¬(w P = 1 ∧ w Q = 1 ∧ w R = 1) := by
    rintro ⟨hp,hq,hr⟩
    have t : w (P+Q) = 2 := two_units A ci pq hp hq
    rw [eqr,hr] at t
    contradiction
  have val : mass = (1+(1/2:ℚ)^w P+(1/2:ℚ)^w Q+(1/2:ℚ)^w R)/4 := by
    let f (u : Vc 2) := (1/2:ℚ)^w (M u)
    change (∑ x, f x) / _ = _
    rw [← Equiv.sum_comp e f,Fintype.sum_prod_type,sum_two,sum_two,sum_two]
    change (f (b2 0 0)+f (b2 0 1)+(f (b2 1 0)+f (b2 1 1))) / _ = _
    have z : f (b2 0 0) = 1 := by rw [show b2 0 0 = 0 by decide]; simp [f,w,weight]
    have cd : Fintype.card (Vc 2) = 4 := by simp [Vc,ZMod.card]
    rw [z,cd]
    dsimp [f,P,Q,R]
    ring
  have num := two_numeric (w P) (w Q) (w R) (dist P nP) (dist Q nQ) (dist R nR) no3
  rw [val]
  refine ⟨num.1,fun h => num.2 ?_⟩
  rintro (⟨p,q⟩ | ⟨p,r⟩ | ⟨q,r⟩)
  · exact h ⟨P,Q,pq,p,q⟩
  · exact h ⟨P,R,pr,p,r⟩
  · exact h ⟨Q,R,qr,q,r⟩
end Code32052
namespace Code32052
theorem coset_upper {m k p h s j t : ℕ} (A : Fin m → Vc k) (M : Vc p →ₗ[K] Vc k)
    (R : Vc j →ₗ[K] Vc p) (xy : (Fin m ⊕ Fin m) ↪ Fin t) (I : Finset (Fin t))
    (idx : ↥I ≃ Fin h) (s₀ : Vc k) (q : Vc s → K) (qs : Stable q)
    (a : Vc p → Vc s) (J : Vc h →ₗ[K] Vc s) (val : Vc p → K) (x y : Vc p → Vc m)
    (X Y : Fin m → Vc h →ₗ[K] K)
    (freeX : ∀ i (hi : xy (.inl i) ∈ I) z, X i z = z (idx ⟨_,hi⟩))
    (freeY : ∀ i (hi : xy (.inr i) ∈ I) z, Y i z = z (idx ⟨_,hi⟩))
    (invis : ∀ v i, i ∈ marked xy I → code A (M (R v)) i = 0)
    (target : ℚ) (half : 1/2 ≤ target)
    (weights : avg (fun v : Vc j => (1/2:ℚ)^weight (code A (M (R v)))) ≤ target) :
    let f (u : Vc p) := fibreError q (a u) J (val u) (code A (s₀+M u)) (x u) (y u) X Y
    |avg (fun u => avg (fun z => (sign (f u z) : ℚ)))| ≤ target := by
  classical
  intro f
  apply remove_cosets R
  intro u
  apply anchor_bound _ _ target half weights
  intro anchor big v
  let v₁ := u + R anchor
  let v₂ := u + R (anchor+v)
  let c := code A (s₀+M v₂)
  let d := code A (s₀+M v₁)
  let w := code A (M (R v))
  have dif (i : Fin m) : c i - d i = w i := by
    simp only [c,d,w,v₁,v₂,map_add,Pi.add_apply]
    abel
  have card : I.card = h := by simpa using Fintype.card_congr idx
  subst h
  obtain ⟨emb,heq⟩ := free_pairs xy I idx w (invis v) (fun i z => X i z) (fun i z => Y i z) freeX freeY
  apply anchor_slice q qs (a v₂) (a v₁) J (val v₂) (val v₁) c d (x v₂) (y v₂) (x v₁) (y v₁) X Y emb _ big
  intro z
  simp_rw [dif]
  exact heq z
end Code32052

namespace Code32052
abbrev DataV (m r : ℕ) := Vc m × (Vc m × Vc r)
noncomputable def address (m r : ℕ) : ((Fin m ⊕ Fin m) ⊕ Fin r) ≃ Fin (2*m+r) :=
  Fintype.equivFinOfCardEq (by simp [two_mul])

noncomputable def pack (m r : ℕ) : DataV m r ≃ₗ[K] Vc (2*m+r) where
  toFun w i := Sum.elim (Sum.elim w.1 w.2.1) w.2.2 ((address m r).symm i)
  invFun v := (fun i => v (address m r (.inl (.inl i))), fun i => v (address m r (.inl (.inr i))), fun i => v (address m r (.inr i)))
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

noncomputable def wires (m r : ℕ) : (Fin m ⊕ Fin m) ↪ Fin (2*m+r) :=
  (⟨Sum.inl,Sum.inl_injective⟩ : (Fin m ⊕ Fin m) ↪ ((Fin m ⊕ Fin m) ⊕ Fin r)).trans (address m r).toEmbedding

theorem pack_left (w : DataV m r) (i : Fin m) : pack m r w (wires m r (.inl i)) = w.1 i := by
  simp [pack,wires]
theorem pack_right (w : DataV m r) (i : Fin m) : pack m r w (wires m r (.inr i)) = w.2.1 i := by
  simp [pack,wires]

theorem avg_equiv {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (f : Y → ℚ) :
    avg (fun x => f (e x)) = avg f := by
  unfold avg
  rw [e.sum_comp f, Fintype.card_congr e]

theorem avg_product {X Y : Type*} [Fintype X] [Fintype Y] (f : X × Y → ℚ) :
    avg f = avg (fun x => avg (fun y => f (x,y))) := by
  simp only [avg, Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,div_eq_mul_inv,
    ← Finset.sum_mul, mul_inv_rev]
  ring

noncomputable def retag {I : Finset (Fin t)} (idx : ↥I ≃ Fin I.card) : Vc I.card ≃ₗ[K] (↥I → K) :=
  LinearEquiv.piCongrLeft K (fun _ => K) idx.symm

end Code32052

namespace Code32052
open Previous
theorem flat_upper {k m r n s j : ℕ}
    (e : Vc n ≃ₗ[K] Vc k × DataV m r) (A : Fin m → Vc k) (h : Vc k → K)
    (B : Vc s →ₗ[K] Vc n) (a : Vc n) (q : Vc s → K) (bi : Function.Injective B) (hq : isQuad q)
    (dim : s = 2*m+r+j) (target : ℚ) (half : 1/2 ≤ target)
    (cost : ∀ T : Vc j →ₗ[K] Vc k, Function.Injective T →
      avg (fun v : Vc j => (1/2:ℚ)^weight (code A (T v))) ≤ target) :
    let g (y : Vc n) := h (e y).1 + ∑ i, dotProduct (A i) (e y).1*(e y).2.1 i*(e y).2.2.1 i
    |avg (fun v : Vc s => (sign (g (a+B v)-q v) : ℚ))| ≤ target := by
  classical
  intro g
  let eb := e.toLinearMap.comp B
  let L := (LinearMap.fst K (Vc k) (DataV m r)).comp eb
  let D₀ := (LinearMap.snd K (Vc k) (DataV m r)).comp eb
  let D := (pack m r).toLinearMap.comp D₀
  have inj : Function.Injective (L.prod D) := by
    intro u v eq
    apply bi
    apply e.injective
    apply Prod.ext
    · exact congrArg (fun w : Vc k × Vc (2*m+r) => w.1) eq
    · exact (pack m r).injective (congrArg (fun w : Vc k × Vc (2*m+r) => w.2) eq)
  let p := Module.finrank K L.range
  obtain ⟨I,M,E,size,mi,sel,dat⟩ := split_flat L D inj
  let idx : ↥I ≃ Fin I.card := Fintype.equivFinOfCardEq (by simp)
  let J₀ := E.toLinearMap.comp (LinearMap.inl K (Vc p) (↥I → K))
  let J := E.toLinearMap.comp ((LinearMap.inr K (Vc p) (↥I → K)).comp (retag idx).toLinearMap)
  let xy := wires m r
  have se (u : Vc p) (z : Vc I.card) : L (J₀ u + J z) = M u := by
    change L (E (u,0) + E (0,retag idx z)) = M u
    rw [← E.map_add]; simpa using sel u (retag idx z)
  let X (i : Fin m) := (LinearMap.proj (R := K) (φ := fun _ : Fin (2*m+r) => K) (xy (.inl i))).comp (D.comp J)
  let Y (i : Fin m) := (LinearMap.proj (R := K) (φ := fun _ : Fin (2*m+r) => K) (xy (.inr i))).comp (D.comp J)
  have free (w : ↥I) (z : Vc I.card) : D (J z) w = z (idx w) := by
    change D (E (0, retag idx z)) w = _
    rw [dat]
    simp [retag, LinearEquiv.piCongrLeft]
  have nc : I.card ≤ 2*m+r := I.card_le_univ.trans_eq (by simp)
  have count := marked_count xy I
  have small : j+(marked xy I).card ≤ p := by
    change I.card + p = s at size
    omega
  obtain ⟨R,ri,invis⟩ := invisible_directions A M (marked xy I) small
  let S₀ := (e a).1
  let sx u := (e a).2.1 + (D₀ (J₀ u)).1
  let sy u := (e a).2.2.1 + (D₀ (J₀ u)).2.1
  let val u := h (S₀+M u)
  let err u := fibreError q (J₀ u) J (val u) (code A (S₀+M u)) (sx u) (sy u) X Y
  have ub := coset_upper A M R xy I idx S₀ q (quad_stable hq) J₀ J val sx sy X Y
    (fun i hi z => free ⟨_,hi⟩ z) (fun i hi z => free ⟨_,hi⟩ z) invis target half
    (cost (M.comp R) (mi.comp ri))
  let F (v : Vc s) : ℚ := sign (g (a+B v)-q v)
  have values (u : Vc p) (z : Vc I.card) : F (E (u,retag idx z)) = (sign (err u z) : ℚ) := by
    have eq : E (u,retag idx z) = J₀ u+J z := by change _ = E (u,0)+E (0,retag idx z); rw [← E.map_add]; simp
    rw [eq]
    have sel_eq : (e (a + B (J₀ u + J z))).1 = S₀ + M u := by
      rw [e.map_add]; exact congrArg ((S₀ + ·)) (se u z)
    have dx (i : Fin m) : (e (a+B (J₀ u+J z))).2.1 i = sx u i + X i z := by
      have hx := pack_left (D₀ (J z)) i
      change _ = sx u i + pack m r (D₀ (J z)) (wires m r (.inl i))
      rw [hx]
      simp [sx,D₀,eb,map_add,add_assoc]
    have dy (i : Fin m) : (e (a+B (J₀ u+J z))).2.2.1 i = sy u i + Y i z := by
      have hy := pack_right (D₀ (J z)) i
      change _ = sy u i + pack m r (D₀ (J z)) (wires m r (.inr i))
      rw [hy]
      simp [sy,D₀,eb,map_add,add_assoc]
    simp only [F,g,sel_eq,dx,dy,err,fibreError,val,code,LinearMap.coe_mk,AddHom.coe_mk]
  change |avg F| ≤ target
  rw [← avg_equiv E.toEquiv F, avg_product]
  have inner (u : Vc p) : avg (fun y : ↥I → K => F (E (u,y))) =
      avg (fun z : Vc I.card => (sign (err u z) : ℚ)) := by
    rw [← avg_equiv (retag idx).toEquiv (fun y => F (E (u,y)))]
    exact congrArg avg (funext (values u))
  change |avg (fun u : Vc p => avg (fun y : ↥I → K => F (E (u,y))))| ≤ target
  simp_rw [inner]
  exact ub
end Code32052

namespace Code32052
theorem scaled_of_avg {s : ℕ} (u v : Vc s → K) (p q : ℕ) (hq : 0 < q)
    (h : |avg (fun z => (sign (u z - v z) : ℚ))| ≤ (p:ℚ)/q) :
    q*(∑ z, if u z=v z then (1:ℤ) else -1).natAbs ≤ p*2^s := by
  classical
  let X := ∑ z, if u z = v z then (1:ℤ) else -1
  have sum_eq : (∑ z, (sign (u z - v z) : ℚ)) = (X:ℚ) := by
    rw [← Int.cast_sum]
    congr 1
    simp [X, sign, sub_eq_zero]
  have hcard : (Fintype.card (Vc s):ℚ) = 2^s := by simp [Vc,ZMod.card]
  rw [avg,sum_eq,hcard,abs_div,abs_of_nonneg (by positivity : (0:ℚ) ≤ 2^s)] at h
  have pos : (0:ℚ) < q := by exact_mod_cast hq
  have sc := (div_le_div_iff₀ (by positivity : (0:ℚ)<2^s) pos).mp h
  change q*X.natAbs ≤ _
  have cast : ((X.natAbs:ℕ):ℚ) = |(X:ℚ)| := by rw [← Int.cast_abs, ← Int.natCast_natAbs]; simp
  exact_mod_cast (show (q:ℚ)*(X.natAbs:ℚ) ≤ (p:ℚ)*2^s by rw [cast,mul_comm]; exact sc)
end Code32052
end PEqualNP.Outside.L_meta_32052_aux
open PEqualNP.Outside.L_meta_32052_aux.Code32052 in
theorem PEqualNP.Outside.L_meta_32052 : (∀ (k m r d : ℕ), 0 < k → 0 < d →
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
  ∀ (e : V ≃ₗ[F] S × (D × (D × Z))) (A : Fin m → S),
    let wt := fun (a : S) => ((Finset.univ : Finset (Fin m)).filter
      (fun i => dotProduct (A i) a ≠ 0)).card
    (∀ a : S, a ≠ 0 → d ≤ wt a) → (∃ a : S, a ≠ 0 ∧ wt a = d) →
    ∀ h : S → F,
      let g := fun (y : V) => h (e y).1 + ∑ i : Fin m,
        dotProduct (A i) (e y).1 * (e y).2.1 i * (e y).2.2.1 i
      let raw := fun (C : Circ) => (∑ x : V, ∑ y : V,
        if C.eval (bits n x ++ bits n y) = decide (dotProduct x y + g y = 1)
        then (1 : ℤ) else -1).natAbs
      let upper := fun (s p q : ℕ) => ∀ C : Circ, legal (2*n) C → cost C ≤ s →
        q * raw C ≤ p * 2^(n+s)
      let opt := fun (s p q : ℕ) => upper s p q ∧
        ∃ C : Circ, legal (2*n) C ∧ cost C ≤ s ∧ q * raw C = p * 2^(n+s)
      let two := ∃ a b : S, a ≠ b ∧ wt a = 1 ∧ wt b = 1
      (∀ s : ℕ, s ≤ base → opt s 1 1) ∧
        opt (base+1) (2^d+1) (2^(d+1)) ∧
        (2 ≤ k → (two → opt (base+2) 9 16) ∧ (¬two → upper (base+2) 1 2)) ∧
        (∀ s : ℕ, base+3 ≤ s → s ≤ n → upper s 1 2)) := by
  classical
  intro k m r d hk hd n Circ FF legal cost bits V S D Z base e A wt hdist hex h g raw upper opt two
  have dist : ∀ a : Vc k, a ≠ 0 → 0 < weight (code A a) :=
    fun a ha => lt_of_lt_of_le hd (hdist a ha)
  have up {j num den : ℕ} (hs : base+j ≤ n) (hden : 0 < den) (hhalf : den ≤ 2*num)
      (hmass : ∀ T : Vc j →ₗ[K] Vc k, Function.Injective T →
        avg (fun v => (1/2:ℚ)^weight (code A (T v))) ≤ (num:ℚ)/den) :
      upper (base+j) num den := by
    apply (upper_iff_flat n (base+j) num den hs hden hhalf g).mpr
    intro B a f bi hq
    apply scaled_of_avg _ _ _ _ hden
    apply flat_upper e A h B a f bi hq rfl _ _ hmass
    apply (le_div_iff₀ (by exact_mod_cast hden : (0:ℚ)<den)).mpr
    have hh : (den:ℚ) ≤ 2*num := by exact_mod_cast hhalf
    linarith
  refine ⟨base_opt k m r d hk hd e A hdist hex h, ?_, ?_, ?_⟩
  · obtain ⟨C,hl,hc,eq⟩ := one_exact k m r d hk hd e A hdist hex h
    refine ⟨up (j:=1) (by dsimp [base,n]; omega) (by positivity) (by rw [pow_succ]; omega) ?_, C,hl,hc,eq.symm⟩
    intro T hi
    refine (mass_one A T hi hdist).trans_eq ?_
    push_cast
    rw [pow_succ,div_pow,one_pow]
    field_simp
  · intro hk2
    have hs : base+2 ≤ n := by dsimp [base,n]; omega
    constructor
    · intro ht
      obtain ⟨C,hl,hc,eq⟩ := two_exact k m r d hk hd e A hdist hex h hk2 ht
      exact ⟨up hs (by decide) (by decide) (fun T hi => (plane_mass A T hi dist).1),C,hl,hc,eq.symm⟩
    · intro ht
      exact up hs (by decide) (by decide) (fun T hi => (plane_mass A T hi dist).2 ht)
  · intro s hlo hhi
    let j := s-base
    have hj : 3 ≤ j := by dsimp [j]; omega
    have eq : base+j=s := by dsimp [j]; omega
    rw [← eq]
    exact up (eq ▸ hhi) (by decide) (by decide) (fun T hi => many_mass A T hi dist hj)
