import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29764_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

abbrev F := ZMod 2

def b2f (b : Bool) : F :=
  if b then 1 else 0

def f2b (a : F) : Bool :=
  decide (a = 1)

lemma f_cases (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma b2f_f2b (a : F) : b2f (f2b a) = a := by
  rcases f_cases a with rfl | rfl <;> rfl

lemma b2f_decide_eq_one (a : F) : b2f (decide (a = 1)) = a :=
  b2f_f2b a

lemma f2b_b2f (b : Bool) : f2b (b2f b) = b := by
  cases b <;> rfl

lemma f_add_self (a : F) : a + a = 0 := by
  rcases f_cases a with rfl | rfl <;> decide

lemma f_ne_zero_eq_one {a : F} (h : a ≠ 0) : a = 1 := by
  rcases f_cases a with rfl | rfl
  · exact absurd rfl h
  · rfl

lemma f_eq_of_add_eq_zero {a b : F} (h : a + b = 0) : a = b := by
  rcases f_cases a with rfl | rfl <;> rcases f_cases b with rfl | rfl <;> first | rfl | exact absurd h (by decide)

lemma b2f_not (b : Bool) : b2f (!b) = b2f b + 1 := by
  cases b <;> rfl

lemma b2f_and (a b : Bool) : b2f (a && b) = b2f a * b2f b := by
  cases a <;> cases b <;> rfl

lemma b2f_or (a b : Bool) : b2f (a || b) = b2f a + b2f b + b2f a * b2f b := by
  cases a <;> cases b <;> rfl

lemma b2f_mod2_one (a : Bool) : b2f (GateOp.eval (.mod 2) [a]) = b2f a + 1 := by
  cases a <;> rfl

lemma b2f_mod2_two (a b : Bool) : b2f (GateOp.eval (.mod 2) [a, b]) = b2f a + b2f b + 1 := by
  cases a <;> cases b <;> rfl

lemma dot_add_right {k : ℕ} (a u v : Fin k → F) :
    dotProduct a (u + v) = dotProduct a u + dotProduct a v := by
  simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dot_add_left {k : ℕ} (a b u : Fin k → F) :
    dotProduct (a + b) u = dotProduct a u + dotProduct b u := by
  simp only [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dot_smul_right {k : ℕ} (a u : Fin k → F) (c : F) :
    dotProduct a (c • u) = c * dotProduct a u := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma dot_zero_left {k : ℕ} (u : Fin k → F) : dotProduct (0 : Fin k → F) u = 0 := by
  simp [dotProduct]

lemma dot_zero_right {k : ℕ} (a : Fin k → F) : dotProduct a (0 : Fin k → F) = 0 := by
  simp [dotProduct]

lemma dot_single_left {k : ℕ} (i : Fin k) (u : Fin k → F) :
    dotProduct (Pi.single i (1 : F)) u = u i := by
  simp only [dotProduct]
  rw [Finset.sum_eq_single i]
  · simp [Pi.single_eq_same]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

lemma dot_single_right {k : ℕ} (u : Fin k → F) (i : Fin k) :
    dotProduct u (Pi.single i (1 : F)) = u i := by
  simp only [dotProduct]
  rw [Finset.sum_eq_single i]
  · simp [Pi.single_eq_same]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

def bits (n : ℕ) (u : Fin n → F) : List Bool :=
  List.ofFn (fun j : Fin n => decide (u j = 1))

lemma bits_length (n : ℕ) (u : Fin n → F) : (bits n u).length = n := by
  simp [bits]

lemma bits_getD (n : ℕ) (u : Fin n → F) (j : ℕ) (hj : j < n) :
    (bits n u).getD j false = decide (u ⟨j, hj⟩ = 1) := by
  simp [bits, List.getD_eq_getElem?_getD, hj]

def stepWires (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (xs : List Bool) :
    C.wires xs = C.gates.foldl stepWires xs := rfl

lemma foldl_step_len (gs : List Gate) (xs : List Bool) :
    (gs.foldl stepWires xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepWires, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_step_getD_lt (gs : List Gate) (xs : List Bool) {i : ℕ} (hi : i < xs.length) :
    (gs.foldl stepWires xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (stepWires xs g).length := by
      simp only [stepWires, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (stepWires xs g) hi']
    simp [stepWires, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_step_snoc_val (gs : List Gate) (g : Gate) (xs : List Bool) :
    ((gs ++ [g]).foldl stepWires xs).getD (xs.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl stepWires xs).getD i false) := by
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  set w := gs.foldl stepWires xs
  have hlen : w.length = xs.length + gs.length := foldl_step_len gs xs
  change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD (xs.length + gs.length) false = _
  rw [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (le_refl _)]
  simp

lemma foldl_step_append_getD_lt (gs1 gs2 : List Gate) (xs : List Bool) {i : ℕ}
    (hi : i < xs.length + gs1.length) :
    ((gs1 ++ gs2).foldl stepWires xs).getD i false =
      (gs1.foldl stepWires xs).getD i false := by
  rw [List.foldl_append]
  apply foldl_step_getD_lt
  rw [foldl_step_len]
  exact hi

def isAndOp : GateOp → Bool
  | .and => true
  | _ => false

def isOrOp : GateOp → Bool
  | .or => true
  | _ => false

def isLegalGate (h : Gate) : Prop :=
  h.inputs.length ≤ 2 ∧
    (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))

noncomputable def isCostGate (h : Gate) : Bool :=
  @decide ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _)

noncomputable def gateListCost (gs : List Gate) : ℕ :=
  gs.countP isCostGate

lemma gateListCost_nil : gateListCost [] = 0 := rfl

lemma gateListCost_append (gs1 gs2 : List Gate) :
    gateListCost (gs1 ++ gs2) = gateListCost gs1 + gateListCost gs2 := by
  simp [gateListCost, List.countP_append]

lemma gateListCost_singleton (g : Gate) :
    gateListCost [g] = if isCostGate g then 1 else 0 := by
  simp [gateListCost]

lemma isCostGate_of_not_binary {g : Gate}
    (h : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)) :
    isCostGate g = false := by
  simp [isCostGate, h]

lemma isCostGate_of_binary {g : Gate}
    (h : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    isCostGate g = true := by
  simp [isCostGate, h]

def readsBackList (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j (Gate.mk GateOp.or [])).inputs, i < n + j

lemma readsBack_iff_list (n : ℕ) (C : Circuit) :
    ReadsBack n C ↔ readsBackList n C.gates := Iff.rfl

lemma readsBackList_nil (n : ℕ) : readsBackList n [] := by
  intro j hj
  simp at hj

lemma readsBackList_snoc {n : ℕ} {gs : List Gate} {g : Gate}
    (hgs : readsBackList n gs) (hg : ∀ i ∈ g.inputs, i < n + gs.length) :
    readsBackList n (gs ++ [g]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < gs.length
  · have hget : (gs ++ [g]).getD j (Gate.mk GateOp.or []) = gs.getD j (Gate.mk GateOp.or []) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    rw [hget] at hi
    exact hgs j hlt i hi
  · have hjeq : j = gs.length := by omega
    subst hjeq
    have hget : (gs ++ [g]).getD gs.length (Gate.mk GateOp.or []) = g := by
      simp [List.getD_eq_getElem?_getD]
    rw [hget] at hi
    exact hg i hi

lemma readsBackList_of_snoc {n : ℕ} {gs : List Gate} {g : Gate}
    (h : readsBackList n (gs ++ [g])) :
    readsBackList n gs ∧ (∀ i ∈ g.inputs, i < n + gs.length) := by
  constructor
  · intro j hj i hi
    have hlt : j < (gs ++ [g]).length := by simp; omega
    have hget : (gs ++ [g]).getD j (Gate.mk GateOp.or []) = gs.getD j (Gate.mk GateOp.or []) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    exact h j hlt i (by rwa [hget])
  · intro i hi
    have hlt : gs.length < (gs ++ [g]).length := by simp
    have hget : (gs ++ [g]).getD gs.length (Gate.mk GateOp.or []) = g := by
      simp [List.getD_eq_getElem?_getD]
    exact h gs.length hlt i (by rwa [hget])

def const0Gate : Gate := Gate.mk .or []
def const1Gate : Gate := Gate.mk .and []

lemma isLegalGate_const0 : isLegalGate const0Gate := by
  refine ⟨by simp [const0Gate], Or.inr (Or.inl rfl)⟩

lemma isLegalGate_const1 : isLegalGate const1Gate := by
  refine ⟨by simp [const1Gate], Or.inl rfl⟩

lemma isLegalGate_not (u : ℕ) : isLegalGate (Gate.mk .not [u]) := by
  refine ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

lemma isLegalGate_xnor (u v : ℕ) : isLegalGate (Gate.mk (.mod 2) [u, v]) := by
  refine ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩

lemma isLegalGate_and2 (u v : ℕ) : isLegalGate (Gate.mk .and [u, v]) := by
  refine ⟨by simp, Or.inl rfl⟩

lemma isLegalGate_or2 (u v : ℕ) : isLegalGate (Gate.mk .or [u, v]) := by
  refine ⟨by simp, Or.inr (Or.inl rfl)⟩

lemma cost_const0 : gateListCost [const0Gate] = 0 := by
  rw [gateListCost_singleton, isCostGate_of_not_binary]
  · rfl
  · simp [const0Gate]

lemma cost_const1 : gateListCost [const1Gate] = 0 := by
  rw [gateListCost_singleton, isCostGate_of_not_binary]
  · rfl
  · simp [const1Gate]

lemma cost_not (u : ℕ) : gateListCost [Gate.mk .not [u]] = 0 := by
  rw [gateListCost_singleton, isCostGate_of_not_binary]
  · rfl
  · simp

lemma cost_xnor (u v : ℕ) : gateListCost [Gate.mk (.mod 2) [u, v]] = 0 := by
  rw [gateListCost_singleton, isCostGate_of_not_binary]
  · rfl
  · simp

lemma cost_and2 (u v : ℕ) : gateListCost [Gate.mk .and [u, v]] = 1 := by
  rw [gateListCost_singleton, isCostGate_of_binary ⟨Or.inl rfl, rfl⟩]
  rfl

lemma cost_or2 (u v : ℕ) : gateListCost [Gate.mk .or [u, v]] = 1 := by
  rw [gateListCost_singleton, isCostGate_of_binary ⟨Or.inr rfl, rfl⟩]
  rfl

def xorAllGates (W δw : ℕ) : ℕ → List Gate
  | 0 => []
  | r + 1 => xorAllGates W δw r ++ [Gate.mk (.mod 2) [r, δw], Gate.mk .not [W + 2 * r]]

lemma xorAllGates_len (W δw r : ℕ) : (xorAllGates W δw r).length = 2 * r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp [xorAllGates, ih]
    omega

lemma xorAllGates_cost (W δw r : ℕ) : gateListCost (xorAllGates W δw r) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [xorAllGates, gateListCost_append, ih, zero_add]
    have h2 : [Gate.mk (.mod 2) [r, δw], Gate.mk .not [W + 2 * r]] =
        [Gate.mk (.mod 2) [r, δw]] ++ [Gate.mk .not [W + 2 * r]] := rfl
    rw [h2, gateListCost_append, cost_xnor, cost_not]

lemma xorAllGates_legal (W δw r : ℕ) : ∀ h ∈ xorAllGates W δw r, isLegalGate h := by
  induction r with
  | zero => intro h hh; simp [xorAllGates] at hh
  | succ r ih =>
    intro h hh
    simp only [xorAllGates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with hh | rfl | rfl
    · exact ih h hh
    · exact isLegalGate_xnor r δw
    · exact isLegalGate_not (W + 2 * r)

lemma xorAllGates_readsBack (m : ℕ) (ds : List Gate) (δw : ℕ)
    (hds : readsBackList m ds) (hδ : δw < m + ds.length) (r : ℕ) (hr : r ≤ m + ds.length) :
    readsBackList m (ds ++ xorAllGates (m + ds.length) δw r) := by
  induction r with
  | zero => simpa [xorAllGates] using hds
  | succ r ih =>
    have hprev := ih (Nat.le_of_succ_le hr)
    have hstep1 : readsBackList m ((ds ++ xorAllGates (m + ds.length) δw r) ++ [Gate.mk (.mod 2) [r, δw]]) := by
      apply readsBackList_snoc hprev
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rw [List.length_append, xorAllGates_len]
      rcases hi with rfl | rfl <;> omega
    have hstep2 : readsBackList m (((ds ++ xorAllGates (m + ds.length) δw r) ++ [Gate.mk (.mod 2) [r, δw]]) ++ [Gate.mk .not [m + ds.length + 2 * r]]) := by
      apply readsBackList_snoc hstep1
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rw [List.length_append, List.length_append, xorAllGates_len, List.length_singleton]
      subst hi
      omega
    simpa [xorAllGates, List.append_assoc] using hstep2

lemma xorAllGates_eval (m : ℕ) (ds : List Gate) (δw : ℕ) (hδ : δw < m + ds.length)
    (r : ℕ) (hr : r ≤ m + ds.length) (addr : List Bool) (haddr : addr.length = m)
    (j : ℕ) (hj : j < r) :
    b2f (((ds ++ xorAllGates (m + ds.length) δw r).foldl stepWires addr).getD (m + ds.length + 2 * j + 1) false) =
      b2f ((ds.foldl stepWires addr).getD j false) + b2f ((ds.foldl stepWires addr).getD δw false) := by
  induction r with
  | zero => omega
  | succ r ih =>
    have hprev_len : (ds ++ xorAllGates (m + ds.length) δw r).length = ds.length + 2 * r := by
      rw [List.length_append, xorAllGates_len]
    by_cases hjr : j < r
    · have hlt : m + ds.length + 2 * j + 1 < addr.length + (ds ++ xorAllGates (m + ds.length) δw r).length := by
        rw [haddr, hprev_len]; omega
      have hrew : ds ++ xorAllGates (m + ds.length) δw (r + 1) =
          (ds ++ xorAllGates (m + ds.length) δw r) ++ [Gate.mk (.mod 2) [r, δw], Gate.mk .not [m + ds.length + 2 * r]] := by
        simp [xorAllGates, List.append_assoc]
      rw [hrew, foldl_step_append_getD_lt _ _ _ hlt]
      exact ih (Nat.le_of_succ_le hr) hjr
    · have hjeq : j = r := by omega
      subst hjeq
      set pref := ds ++ xorAllGates (m + ds.length) δw j
      have hpref_len : pref.length = ds.length + 2 * j := hprev_len
      have hrew : ds ++ xorAllGates (m + ds.length) δw (j + 1) =
          (pref ++ [Gate.mk (.mod 2) [j, δw]]) ++ [Gate.mk .not [m + ds.length + 2 * j]] := by
        simp [pref, xorAllGates, List.append_assoc]
      rw [hrew]
      have hidx2 : m + ds.length + 2 * j + 1 = addr.length + (pref ++ [Gate.mk (.mod 2) [j, δw]]).length := by
        rw [haddr, List.length_append, hpref_len, List.length_singleton]; omega
      rw [hidx2, foldl_step_snoc_val]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
      have hidx1 : m + ds.length + 2 * j = addr.length + pref.length := by
        rw [haddr, hpref_len]; omega
      rw [hidx1, foldl_step_snoc_val]
      simp only [List.map_cons, List.map_nil]
      have hlt_j : j < addr.length + ds.length := by rw [haddr]; omega
      have hlt_δ : δw < addr.length + ds.length := by rw [haddr]; omega
      have hget_j : (pref.foldl stepWires addr).getD j false = (ds.foldl stepWires addr).getD j false :=
        foldl_step_append_getD_lt ds (xorAllGates (m + ds.length) δw j) addr hlt_j
      have hget_δ : (pref.foldl stepWires addr).getD δw false = (ds.foldl stepWires addr).getD δw false :=
        foldl_step_append_getD_lt ds (xorAllGates (m + ds.length) δw j) addr hlt_δ
      rw [hget_j, hget_δ, b2f_not, b2f_mod2_two]
      have h11 : (1 : F) + 1 = 0 := f_add_self 1
      calc
        (b2f ((ds.foldl stepWires addr).getD j false) + b2f ((ds.foldl stepWires addr).getD δw false) + 1) + 1
            = b2f ((ds.foldl stepWires addr).getD j false) + b2f ((ds.foldl stepWires addr).getD δw false) + (1 + 1) := by ring
        _ = b2f ((ds.foldl stepWires addr).getD j false) + b2f ((ds.foldl stepWires addr).getD δw false) := by rw [h11, add_zero]

lemma elim_binary_gate (k m : ℕ) (cs : List Gate) (h : Gate)
    (hop : h.op = .and ∨ h.op = .or)
    (w1 w2 : ℕ) (hw1 : w1 < k + m + cs.length) (_hw2 : w2 < k + m + cs.length)
    (hins : h.inputs = [w1, w2] ∨ h.inputs = [w2, w1])
    (ds : List Gate) (eqs : List (Fin k → F)) (tap : Fin k → ℕ)
    (val : ℕ → ℕ) (slope : ℕ → (Fin k → F))
    (hds_rb : readsBackList m ds)
    (hds_leg : ∀ g ∈ ds, isLegalGate g)
    (hcost : gateListCost ds + eqs.length ≤ gateListCost cs)
    (htap : ∀ i : Fin k, tap i < m + ds.length)
    (hval : ∀ w < k + m + cs.length, val w < m + ds.length)
    (heval : ∀ (addr : List Bool), addr.length = m →
      let dw := ds.foldl stepWires addr
      let p : Fin k → F := fun i => b2f (dw.getD (tap i) false)
      ∀ u : Fin k → F, (∀ a ∈ eqs, dotProduct a u = 0) →
        ∀ w < k + m + cs.length,
          b2f ((cs.foldl stepWires (bits k (p + u) ++ addr)).getD w false) =
            b2f (dw.getD (val w) false) + dotProduct (slope w) u)
    (v : Fin k → F) (hv_ker : ∀ a ∈ eqs, dotProduct a v = 0)
    (hv1 : dotProduct (slope w1) v ≠ 0) :
    ∃ (ds' : List Gate) (eqs' : List (Fin k → F)) (tap' : Fin k → ℕ)
      (val' : ℕ → ℕ) (slope' : ℕ → (Fin k → F)),
      readsBackList m ds' ∧
      (∀ g ∈ ds', isLegalGate g) ∧
      gateListCost ds' + eqs'.length ≤ gateListCost (cs ++ [h]) ∧
      (∀ i : Fin k, tap' i < m + ds'.length) ∧
      (∀ w < k + m + (cs ++ [h]).length, val' w < m + ds'.length) ∧
      (∀ (addr : List Bool), addr.length = m →
        let dw := ds'.foldl stepWires addr
        let p : Fin k → F := fun i => b2f (dw.getD (tap' i) false)
        ∀ u : Fin k → F, (∀ a ∈ eqs', dotProduct a u = 0) →
          ∀ w < k + m + (cs ++ [h]).length,
            b2f (((cs ++ [h]).foldl stepWires (bits k (p + u) ++ addr)).getD w false) =
              b2f (dw.getD (val' w) false) + dotProduct (slope' w) u) := by
  have hv1_eq : dotProduct (slope w1) v = 1 := f_ne_zero_eq_one hv1
  have hval_w1 : val w1 < m + ds.length := hval w1 hw1
  set ds1 : List Gate := if isAndOp h.op then ds else ds ++ [Gate.mk .not [val w1]]
  set δw : ℕ := if isAndOp h.op then val w1 else m + ds.length
  have hds1_rb : readsBackList m ds1 := by
    cases hand : isAndOp h.op
    · simp only [ds1, hand, Bool.false_eq_true, ↓reduceIte]
      apply readsBackList_snoc hds_rb
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi
      exact hval_w1
    · simpa [ds1, hand] using hds_rb
  have hds1_leg : ∀ g ∈ ds1, isLegalGate g := by
    cases hand : isAndOp h.op
    · intro g hg
      simp only [ds1, hand, Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with hg | rfl
      · exact hds_leg g hg
      · exact isLegalGate_not (val w1)
    · simpa [ds1, hand] using hds_leg
  have hds1_cost : gateListCost ds1 = gateListCost ds := by
    cases hand : isAndOp h.op
    · simp only [ds1, hand, Bool.false_eq_true, ↓reduceIte, gateListCost_append, cost_not, add_zero]
    · simp [ds1, hand]
  have hds1_len_ge : ds.length ≤ ds1.length := by
    cases hand : isAndOp h.op <;> simp [ds1, hand]
  have hδ_lt : δw < m + ds1.length := by
    cases hand : isAndOp h.op
    · simp only [ds1, δw, hand, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]; omega
    · simp only [ds1, δw, hand, ↓reduceIte]; exact hval_w1
  set W : ℕ := m + ds1.length
  set cGate : Gate := if isAndOp h.op then const0Gate else const1Gate
  set ds' : List Gate := (ds1 ++ xorAllGates W δw W) ++ [cGate]
  have hds'_rb : readsBackList m ds' := by
    apply readsBackList_snoc
    · exact xorAllGates_readsBack m ds1 δw hds1_rb hδ_lt W (le_refl W)
    · intro i hi
      cases hand : isAndOp h.op <;> simp [cGate, hand, const0Gate, const1Gate] at hi
  have hds'_leg : ∀ g ∈ ds', isLegalGate g := by
    intro g hg
    simp only [ds', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (hg | hg) | rfl
    · exact hds1_leg g hg
    · exact xorAllGates_legal W δw W g hg
    · cases hand : isAndOp h.op
      · simpa [cGate, hand] using isLegalGate_const1
      · simpa [cGate, hand] using isLegalGate_const0
  have hds'_cost : gateListCost ds' = gateListCost ds := by
    have hc : gateListCost [cGate] = 0 := by
      cases hand : isAndOp h.op
      · simp only [cGate, hand, Bool.false_eq_true, ↓reduceIte, cost_const1]
      · simp only [cGate, hand, ↓reduceIte, cost_const0]
    rw [show ds' = (ds1 ++ xorAllGates W δw W) ++ [cGate] from rfl]
    rw [gateListCost_append, gateListCost_append, hds1_cost, xorAllGates_cost, hc]
    omega
  have hds'_len : ds'.length = ds1.length + 2 * W + 1 := by
    simp only [ds', List.length_append, xorAllGates_len, List.length_singleton]
  have hcost_h : gateListCost [h] = 1 := by
    have hlen2 : h.inputs.length = 2 := by rcases hins with he | he <;> simp [he]
    rw [gateListCost_singleton, isCostGate_of_binary ⟨hop, hlen2⟩]
    rfl
  set eqs' : List (Fin k → F) := slope w1 :: eqs
  set cWire : ℕ := m + (ds1 ++ xorAllGates W δw W).length
  set tap' : Fin k → ℕ := fun i => if v i = 1 then W + 2 * tap i + 1 else tap i
  set val' : ℕ → ℕ := fun w =>
    if w < k + m + cs.length then
      (if dotProduct (slope w) v = 1 then W + 2 * val w + 1 else val w)
    else cWire
  set slope' : ℕ → (Fin k → F) := fun w =>
    if w < k + m + cs.length then slope w else 0
  refine ⟨ds', eqs', tap', val', slope', hds'_rb, hds'_leg, ?_, ?_, ?_, ?_⟩
  · rw [hds'_cost, gateListCost_append, hcost_h]
    simp only [eqs', List.length_cons]
    omega
  · intro i
    have hti : tap i < W := by have := htap i; omega
    dsimp only [tap']
    split_ifs <;> rw [hds'_len] <;> omega
  · intro w hw
    rw [List.length_append, List.length_singleton] at hw
    dsimp only [val']
    split_ifs with hlt
    · have hvw : val w < W := by have := hval w hlt; omega
      rw [hds'_len]; omega
    · have hvw : val w < W := by have := hval w hlt; omega
      rw [hds'_len]; omega
    · simp only [cWire, List.length_append, xorAllGates_len, hds'_len]
      omega
  · intro addr haddr
    set dw0 := ds.foldl stepWires addr
    set dw1 := ds1.foldl stepWires addr
    set dw2 := (ds1 ++ xorAllGates W δw W).foldl stepWires addr
    set dw' := ds'.foldl stepWires addr
    have hdw1_old : ∀ r < m + ds.length, dw1.getD r false = dw0.getD r false := by
      intro r hr
      cases hand : isAndOp h.op
      · simp only [dw1, ds1, hand, Bool.false_eq_true, ↓reduceIte]
        exact foldl_step_append_getD_lt ds [Gate.mk .not [val w1]] addr (by rw [haddr]; exact hr)
      · simp [dw1, dw0, ds1, hand]
    have hdw'_dw2 : ∀ r < m + (ds1 ++ xorAllGates W δw W).length, dw'.getD r false = dw2.getD r false := by
      intro r hr
      exact foldl_step_append_getD_lt (ds1 ++ xorAllGates W δw W) [cGate] addr (by rw [haddr]; exact hr)
    have hdw2_dw1 : ∀ r < W, dw2.getD r false = dw1.getD r false := by
      intro r hr
      exact foldl_step_append_getD_lt ds1 (xorAllGates W δw W) addr (by rw [haddr]; exact hr)
    have hdw'_old : ∀ r < m + ds.length, dw'.getD r false = dw0.getD r false := by
      intro r hr
      have hrW : r < W := by omega
      have hr2 : r < m + (ds1 ++ xorAllGates W δw W).length := by
        rw [List.length_append, xorAllGates_len]; omega
      rw [hdw'_dw2 r hr2, hdw2_dw1 r hrW, hdw1_old r hr]
    have hdw'_flip : ∀ r < m + ds.length,
        b2f (dw'.getD (W + 2 * r + 1) false) = b2f (dw0.getD r false) + b2f (dw1.getD δw false) := by
      intro r hr
      have hrW : r < W := by omega
      have hr2 : W + 2 * r + 1 < m + (ds1 ++ xorAllGates W δw W).length := by
        rw [List.length_append, xorAllGates_len]; omega
      rw [hdw'_dw2 (W + 2 * r + 1) hr2]
      have hx := xorAllGates_eval m ds1 δw hδ_lt W (le_refl W) addr haddr r hrW
      rw [hx, hdw1_old r hr]
    set c_abs : F := if isAndOp h.op then 0 else 1
    have hδ_val : b2f (dw1.getD δw false) = b2f (dw0.getD (val w1) false) + c_abs := by
      cases hand : isAndOp h.op
      · simp only [dw1, ds1, δw, c_abs, hand, Bool.false_eq_true, ↓reduceIte]
        have hidx : m + ds.length = addr.length + ds.length := by rw [haddr]
        rw [hidx, foldl_step_snoc_val]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2f_not]
        rfl
      · simp only [dw1, dw0, ds1, δw, c_abs, hand, ↓reduceIte, add_zero]
    set δ : F := b2f (dw1.getD δw false)
    set p0 : Fin k → F := fun i => b2f (dw0.getD (tap i) false)
    set p' : Fin k → F := fun i => b2f (dw'.getD (tap' i) false)
    have hp'_eq : p' = p0 + δ • v := by
      funext i
      simp only [p', p0, tap', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases f_cases (v i) with hvi | hvi
      · simp only [hvi, zero_ne_one, ↓reduceIte, mul_zero, add_zero]
        rw [hdw'_old (tap i) (htap i)]
      · simp only [hvi, ↓reduceIte, mul_one]
        exact hdw'_flip (tap i) (htap i)
    have hval'_eq : ∀ w < k + m + cs.length,
        b2f (dw'.getD (val' w) false) = b2f (dw0.getD (val w) false) + δ * dotProduct (slope w) v := by
      intro w hw
      simp only [val', hw, ↓reduceIte]
      rcases f_cases (dotProduct (slope w) v) with hsv | hsv
      · simp only [hsv, zero_ne_one, ↓reduceIte, mul_zero, add_zero]
        rw [hdw'_old (val w) (hval w hw)]
      · simp only [hsv, ↓reduceIte, mul_one]
        exact hdw'_flip (val w) (hval w hw)
    dsimp only
    intro u hu w hw
    have hu_w1 : dotProduct (slope w1) u = 0 := hu (slope w1) (by simp [eqs'])
    have hu_eqs : ∀ a ∈ eqs, dotProduct a u = 0 := fun a ha => hu a (by simp [eqs', ha])
    have hδv_u_ker : ∀ a ∈ eqs, dotProduct a (δ • v + u) = 0 := by
      intro a ha
      rw [dot_add_right, dot_smul_right, hv_ker a ha, hu_eqs a ha]
      simp
    have hpu : p' + u = p0 + (δ • v + u) := by rw [hp'_eq, add_assoc]
    rw [List.length_append, List.length_singleton] at hw
    by_cases hlt : w < k + m + cs.length
    · have hlen_in : (bits k (p' + u) ++ addr).length = k + m := by
        rw [List.length_append, bits_length, haddr]
      have hfold_lt : ((cs ++ [h]).foldl stepWires (bits k (p' + u) ++ addr)).getD w false =
          (cs.foldl stepWires (bits k (p' + u) ++ addr)).getD w false := by
        apply foldl_step_append_getD_lt
        rw [hlen_in]
        exact hlt
      change b2f (((cs ++ [h]).foldl stepWires (bits k (p' + u) ++ addr)).getD w false) =
        b2f (dw'.getD (val' w) false) + dotProduct (slope' w) u
      rw [hfold_lt, hpu]
      have hbase := heval addr haddr (δ • v + u) hδv_u_ker w hlt
      rw [hbase, dot_add_right, dot_smul_right, hval'_eq w hlt]
      simp only [slope', hlt, ↓reduceIte]
      ring
    · have hweq : w = k + m + cs.length := by omega
      subst hweq
      change b2f (((cs ++ [h]).foldl stepWires (bits k (p' + u) ++ addr)).getD (k + m + cs.length) false) =
        b2f (dw'.getD (val' (k + m + cs.length)) false) + dotProduct (slope' (k + m + cs.length)) u
      have hlen_in : (bits k (p' + u) ++ addr).length = k + m := by
        rw [List.length_append, bits_length, haddr]
      have hidx_cs : k + m + cs.length = (bits k (p' + u) ++ addr).length + cs.length := by rw [hlen_in]
      have hsnoc_c := foldl_step_snoc_val cs h (bits k (p' + u) ++ addr)
      rw [← hidx_cs] at hsnoc_c
      rw [hsnoc_c]
      have hw1_val : b2f ((cs.foldl stepWires (bits k (p' + u) ++ addr)).getD w1 false) = c_abs := by
        rw [hpu]
        have h1 := heval addr haddr (δ • v + u) hδv_u_ker w1 hw1
        rw [h1, dot_add_right, dot_smul_right, hv1_eq, mul_one, hu_w1, add_zero]
        show b2f (dw0.getD (val w1) false) + δ = c_abs
        rw [show δ = b2f (dw0.getD (val w1) false) + c_abs from hδ_val]
        rw [← add_assoc, f_add_self, zero_add]
      have hw1_bool : (cs.foldl stepWires (bits k (p' + u) ++ addr)).getD w1 false = f2b c_abs := by
        rw [← hw1_val, f2b_b2f]
      have hgate_eval : h.op.eval (h.inputs.map fun i => (cs.foldl stepWires (bits k (p' + u) ++ addr)).getD i false) = f2b c_abs := by
        rcases hop with hand | hor
        · have hia : isAndOp h.op = true := by simp [hand, isAndOp]
          have hc0 : f2b c_abs = false := by simp [c_abs, hia, f2b]
          rw [hand, hc0]
          rw [hc0] at hw1_bool
          rcases hins with he | he <;>
            simp only [he, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, hw1_bool,
              Bool.false_and, Bool.and_false, Bool.and_true]
        · have hia : isAndOp h.op = false := by simp [hor, isAndOp]
          have hc1 : f2b c_abs = true := by simp [c_abs, hia, f2b]
          rw [hor, hc1]
          rw [hc1] at hw1_bool
          rcases hins with he | he <;>
            simp only [he, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, hw1_bool,
              Bool.true_or, Bool.or_true, Bool.or_false]
      rw [hgate_eval, b2f_f2b]
      have hnotlt : ¬ (k + m + cs.length < k + m + cs.length) := lt_irrefl _
      simp only [val', slope', hnotlt, ↓reduceIte, dot_zero_left, add_zero]
      have hcidx : cWire = addr.length + (ds1 ++ xorAllGates W δw W).length := by rw [haddr]
      rw [hcidx]
      show c_abs = b2f ((((ds1 ++ xorAllGates W δw W) ++ [cGate]).foldl stepWires addr).getD _ false)
      rw [foldl_step_snoc_val]
      cases hand : isAndOp h.op <;> simp [cGate, c_abs, hand, const0Gate, const1Gate, GateOp.eval, b2f]

lemma slice_induction (k m : ℕ) (cs : List Gate)
    (hrb : readsBackList (k + m) cs)
    (hleg : ∀ h ∈ cs, isLegalGate h) :
    ∃ (ds : List Gate) (eqs : List (Fin k → F)) (tap : Fin k → ℕ)
      (val : ℕ → ℕ) (slope : ℕ → (Fin k → F)),
      readsBackList m ds ∧
      (∀ g ∈ ds, isLegalGate g) ∧
      gateListCost ds + eqs.length ≤ gateListCost cs ∧
      (∀ i : Fin k, tap i < m + ds.length) ∧
      (∀ w < k + m + cs.length, val w < m + ds.length) ∧
      (∀ (addr : List Bool), addr.length = m →
        let dw := ds.foldl stepWires addr
        let p : Fin k → F := fun i => b2f (dw.getD (tap i) false)
        ∀ u : Fin k → F, (∀ a ∈ eqs, dotProduct a u = 0) →
          ∀ w < k + m + cs.length,
            b2f ((cs.foldl stepWires (bits k (p + u) ++ addr)).getD w false) =
              b2f (dw.getD (val w) false) + dotProduct (slope w) u) := by
  induction cs using List.reverseRecOn with
  | nil =>
    refine ⟨[const0Gate], [], fun _ => m, fun w => if w < k then m else w - k,
      fun w => if hw : w < k then Pi.single ⟨w, hw⟩ 1 else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply readsBackList_snoc (readsBackList_nil m)
      intro i hi; simp [const0Gate] at hi
    · intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg; exact isLegalGate_const0
    · rw [cost_const0]; rfl
    · intro i; simp
    · intro w hw
      dsimp only
      simp only [List.length_nil, add_zero] at hw
      split_ifs
      · simp
      · simp; omega
    · intro addr haddr
      have hdwm : ([const0Gate].foldl stepWires addr).getD m false = false := by
        have hm : m = addr.length + ([] : List Gate).length := by rw [haddr]; simp
        have h1 := foldl_step_snoc_val [] const0Gate addr
        rw [← hm] at h1
        simpa [const0Gate, GateOp.eval] using h1
      have hp0 : (fun _ : Fin k => b2f (([const0Gate].foldl stepWires addr).getD m false)) = 0 := by
        funext i; rw [hdwm]; rfl
      dsimp only
      intro u _ w hw
      simp only [List.length_nil, add_zero] at hw
      rw [hp0, zero_add]
      by_cases hwk : w < k
      · simp only [hwk, ↓reduceIte, ↓reduceDIte, List.foldl_nil]
        rw [hdwm, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [bits_length]; exact hwk)]
        rw [← List.getD_eq_getElem?_getD, bits_getD k u w hwk, b2f_decide_eq_one, dot_single_left]
        rw [show b2f false = 0 from rfl, zero_add]
      · simp only [hwk, ↓reduceIte, ↓reduceDIte, dot_zero_left, add_zero, List.foldl_nil]
        have hlt_addr : w - k < addr.length := by rw [haddr]; omega
        have hdw_lt : ([const0Gate].foldl stepWires addr).getD (w - k) false = addr.getD (w - k) false :=
          foldl_step_getD_lt [const0Gate] addr hlt_addr
        rw [hdw_lt, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [bits_length]; omega)]
        rw [bits_length, ← List.getD_eq_getElem?_getD]
  | append_singleton cs h ih =>
    have ⟨hrb_cs, hg_rb⟩ := readsBackList_of_snoc hrb
    have hleg_cs : ∀ g ∈ cs, isLegalGate g := fun g hg => hleg g (List.mem_append_left _ hg)
    have hleg_h : isLegalGate h := hleg h (List.mem_append_right _ (List.mem_singleton_self h))
    rcases ih hrb_cs hleg_cs with ⟨ds, eqs, tap, val, slope, hds_rb, hds_leg, hcost, htap, hval, heval⟩
    rcases hleg_h with ⟨hlen_le, hop⟩
    match hins : h.inputs with
    | [] =>
      have hcost_h : gateListCost [h] = 0 := by
        rw [gateListCost_singleton, isCostGate_of_not_binary]
        · rfl
        · simp [hins]
      set g0 : Gate := if isOrOp h.op then const0Gate else const1Gate
      have hg0_leg : isLegalGate g0 := by
        cases hor : isOrOp h.op
        · simpa [g0, hor] using isLegalGate_const1
        · simpa [g0, hor] using isLegalGate_const0
      have hg0_cost : gateListCost [g0] = 0 := by
        cases hor : isOrOp h.op
        · simp only [g0, hor, Bool.false_eq_true, ↓reduceIte, cost_const1]
        · simp only [g0, hor, ↓reduceIte, cost_const0]
      refine ⟨ds ++ [g0], eqs, tap,
        fun w => if w < k + m + cs.length then val w else m + ds.length,
        fun w => if w < k + m + cs.length then slope w else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply readsBackList_snoc hds_rb
        intro i hi; cases hor : isOrOp h.op <;> simp [g0, hor, const0Gate, const1Gate] at hi
      · intro g hg
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with hg | rfl
        · exact hds_leg g hg
        · exact hg0_leg
      · rw [gateListCost_append, gateListCost_append, hg0_cost, hcost_h]; omega
      · intro i; rw [List.length_append, List.length_singleton]; have := htap i; omega
      · intro w hw
        dsimp only
        rw [List.length_append, List.length_singleton] at hw ⊢
        split_ifs with hlt
        · have := hval w hlt; omega
        · omega
      · intro addr haddr
        have hdw_old : ∀ r < m + ds.length, ((ds ++ [g0]).foldl stepWires addr).getD r false = (ds.foldl stepWires addr).getD r false :=
          fun r hr => foldl_step_append_getD_lt ds [g0] addr (by rw [haddr]; exact hr)
        have hp_eq : (fun i : Fin k => b2f (((ds ++ [g0]).foldl stepWires addr).getD (tap i) false)) =
            (fun i : Fin k => b2f ((ds.foldl stepWires addr).getD (tap i) false)) := by
          funext i; rw [hdw_old (tap i) (htap i)]
        dsimp only
        intro u hu w hw
        rw [hp_eq]
        rw [List.length_append, List.length_singleton] at hw
        by_cases hlt : w < k + m + cs.length
        · simp only [hlt, ↓reduceIte]
          rw [hdw_old (val w) (hval w hlt)]
          rw [foldl_step_append_getD_lt cs [h] _ (by rw [List.length_append, bits_length, haddr]; exact hlt)]
          exact heval addr haddr u hu w hlt
        · have hweq : w = k + m + cs.length := by omega
          subst hweq
          simp only [hlt, ↓reduceIte, dot_zero_left, add_zero]
          have hidx_c : k + m + cs.length = (bits k ((fun i => b2f ((ds.foldl stepWires addr).getD (tap i) false)) + u) ++ addr).length + cs.length := by
            rw [List.length_append, bits_length, haddr]
          have hidx_d : m + ds.length = addr.length + ds.length := by rw [haddr]
          rw [hidx_c, foldl_step_snoc_val, hidx_d, foldl_step_snoc_val, hins]
          rcases hop with hand | hor | hmod | ⟨_, hnotlen⟩
          · simp [hand, g0, isOrOp, const1Gate, GateOp.eval]
          · simp [hor, g0, isOrOp, const0Gate, GateOp.eval]
          · simp [hmod, g0, isOrOp, const1Gate, GateOp.eval]
          · simp [hins] at hnotlen
    | [w1] =>
      have hw1 : w1 < k + m + cs.length := hg_rb w1 (by simp [hins])
      have hcost_h : gateListCost [h] = 0 := by
        rw [gateListCost_singleton, isCostGate_of_not_binary]
        · rfl
        · simp [hins]
      rcases hop with hand | hor | hmod | ⟨hnot, _⟩
      · refine ⟨ds, eqs, tap,
          fun w => if w < k + m + cs.length then val w else val w1,
          fun w => if w < k + m + cs.length then slope w else slope w1,
          hds_rb, hds_leg, ?_, htap, ?_, ?_⟩
        · rw [gateListCost_append, hcost_h]; omega
        · intro w hw
          dsimp only
          rw [List.length_append, List.length_singleton] at hw
          split_ifs with hlt
          · exact hval w hlt
          · exact hval w1 hw1
        · intro addr haddr
          dsimp only
          intro u hu w hw
          rw [List.length_append, List.length_singleton] at hw
          by_cases hlt : w < k + m + cs.length
          · simp only [hlt, ↓reduceIte]
            rw [foldl_step_append_getD_lt cs [h] _ (by rw [List.length_append, bits_length, haddr]; exact hlt)]
            exact heval addr haddr u hu w hlt
          · have hweq : w = k + m + cs.length := by omega
            subst hweq
            simp only [hlt, ↓reduceIte]
            have hidx_c : k + m + cs.length = (bits k ((fun i => b2f ((ds.foldl stepWires addr).getD (tap i) false)) + u) ++ addr).length + cs.length := by
              rw [List.length_append, bits_length, haddr]
            rw [hidx_c, foldl_step_snoc_val, hins, hand]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact heval addr haddr u hu w1 hw1
      · refine ⟨ds, eqs, tap,
          fun w => if w < k + m + cs.length then val w else val w1,
          fun w => if w < k + m + cs.length then slope w else slope w1,
          hds_rb, hds_leg, ?_, htap, ?_, ?_⟩
        · rw [gateListCost_append, hcost_h]; omega
        · intro w hw
          dsimp only
          rw [List.length_append, List.length_singleton] at hw
          split_ifs with hlt
          · exact hval w hlt
          · exact hval w1 hw1
        · intro addr haddr
          dsimp only
          intro u hu w hw
          rw [List.length_append, List.length_singleton] at hw
          by_cases hlt : w < k + m + cs.length
          · simp only [hlt, ↓reduceIte]
            rw [foldl_step_append_getD_lt cs [h] _ (by rw [List.length_append, bits_length, haddr]; exact hlt)]
            exact heval addr haddr u hu w hlt
          · have hweq : w = k + m + cs.length := by omega
            subst hweq
            simp only [hlt, ↓reduceIte]
            have hidx_c : k + m + cs.length = (bits k ((fun i => b2f ((ds.foldl stepWires addr).getD (tap i) false)) + u) ++ addr).length + cs.length := by
              rw [List.length_append, bits_length, haddr]
            rw [hidx_c, foldl_step_snoc_val, hins, hor]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact heval addr haddr u hu w1 hw1
      · refine ⟨ds ++ [Gate.mk .not [val w1]], eqs, tap,
          fun w => if w < k + m + cs.length then val w else m + ds.length,
          fun w => if w < k + m + cs.length then slope w else slope w1, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · apply readsBackList_snoc hds_rb
          intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; subst hi; exact hval w1 hw1
        · intro g hg
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with hg | rfl
          · exact hds_leg g hg
          · exact isLegalGate_not (val w1)
        · rw [gateListCost_append, gateListCost_append, hcost_h, cost_not]; omega
        · intro i; rw [List.length_append, List.length_singleton]; have := htap i; omega
        · intro w hw
          dsimp only
          rw [List.length_append, List.length_singleton] at hw ⊢
          split_ifs with hlt
          · have := hval w hlt; omega
          · omega
        · intro addr haddr
          have hdw_old : ∀ r < m + ds.length, ((ds ++ [Gate.mk .not [val w1]]).foldl stepWires addr).getD r false = (ds.foldl stepWires addr).getD r false :=
            fun r hr => foldl_step_append_getD_lt ds [Gate.mk .not [val w1]] addr (by rw [haddr]; exact hr)
          have hp_eq : (fun i : Fin k => b2f (((ds ++ [Gate.mk .not [val w1]]).foldl stepWires addr).getD (tap i) false)) =
              (fun i : Fin k => b2f ((ds.foldl stepWires addr).getD (tap i) false)) := by
            funext i; rw [hdw_old (tap i) (htap i)]
          dsimp only
          intro u hu w hw
          rw [hp_eq]
          rw [List.length_append, List.length_singleton] at hw
          by_cases hlt : w < k + m + cs.length
          · simp only [hlt, ↓reduceIte]
            rw [hdw_old (val w) (hval w hlt)]
            rw [foldl_step_append_getD_lt cs [h] _ (by rw [List.length_append, bits_length, haddr]; exact hlt)]
            exact heval addr haddr u hu w hlt
          · have hweq : w = k + m + cs.length := by omega
            subst hweq
            simp only [hlt, ↓reduceIte]
            have hidx_c : k + m + cs.length = (bits k ((fun i => b2f ((ds.foldl stepWires addr).getD (tap i) false)) + u) ++ addr).length + cs.length := by
              rw [List.length_append, bits_length, haddr]
            have hidx_d : m + ds.length = addr.length + ds.length := by rw [haddr]
            rw [hidx_c, foldl_step_snoc_val, hidx_d, foldl_step_snoc_val, hins, hmod]
            simp only [List.map_cons, List.map_nil]
            rw [b2f_mod2_one]
            simp only [GateOp.eval, List.headD_cons, b2f_not]
            rw [heval addr haddr u hu w1 hw1]
            ring
      · refine ⟨ds ++ [Gate.mk .not [val w1]], eqs, tap,
          fun w => if w < k + m + cs.length then val w else m + ds.length,
          fun w => if w < k + m + cs.length then slope w else slope w1, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · apply readsBackList_snoc hds_rb
          intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; subst hi; exact hval w1 hw1
        · intro g hg
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with hg | rfl
          · exact hds_leg g hg
          · exact isLegalGate_not (val w1)
        · rw [gateListCost_append, gateListCost_append, hcost_h, cost_not]; omega
        · intro i; rw [List.length_append, List.length_singleton]; have := htap i; omega
        · intro w hw
          dsimp only
          rw [List.length_append, List.length_singleton] at hw ⊢
          split_ifs with hlt
          · have := hval w hlt; omega
          · omega
        · intro addr haddr
          have hdw_old : ∀ r < m + ds.length, ((ds ++ [Gate.mk .not [val w1]]).foldl stepWires addr).getD r false = (ds.foldl stepWires addr).getD r false :=
            fun r hr => foldl_step_append_getD_lt ds [Gate.mk .not [val w1]] addr (by rw [haddr]; exact hr)
          have hp_eq : (fun i : Fin k => b2f (((ds ++ [Gate.mk .not [val w1]]).foldl stepWires addr).getD (tap i) false)) =
              (fun i : Fin k => b2f ((ds.foldl stepWires addr).getD (tap i) false)) := by
            funext i; rw [hdw_old (tap i) (htap i)]
          dsimp only
          intro u hu w hw
          rw [hp_eq]
          rw [List.length_append, List.length_singleton] at hw
          by_cases hlt : w < k + m + cs.length
          · simp only [hlt, ↓reduceIte]
            rw [hdw_old (val w) (hval w hlt)]
            rw [foldl_step_append_getD_lt cs [h] _ (by rw [List.length_append, bits_length, haddr]; exact hlt)]
            exact heval addr haddr u hu w hlt
          · have hweq : w = k + m + cs.length := by omega
            subst hweq
            simp only [hlt, ↓reduceIte]
            have hidx_c : k + m + cs.length = (bits k ((fun i => b2f ((ds.foldl stepWires addr).getD (tap i) false)) + u) ++ addr).length + cs.length := by
              rw [List.length_append, bits_length, haddr]
            have hidx_d : m + ds.length = addr.length + ds.length := by rw [haddr]
            rw [hidx_c, foldl_step_snoc_val, hidx_d, foldl_step_snoc_val, hins, hnot]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2f_not]
            rw [heval addr haddr u hu w1 hw1]
            ring
    | [w1, w2] =>
      have hw1 : w1 < k + m + cs.length := hg_rb w1 (by simp [hins])
      have hw2 : w2 < k + m + cs.length := hg_rb w2 (by simp [hins])
      rcases hop with hand | hor | hmod | ⟨_, hnotlen⟩
      · by_cases h1 : ∃ v : Fin k → F, (∀ a ∈ eqs, dotProduct a v = 0) ∧ dotProduct (slope w1) v ≠ 0
        · rcases h1 with ⟨v, hv_ker, hv1⟩
          exact elim_binary_gate k m cs h (Or.inl hand) w1 w2 hw1 hw2 (Or.inl hins)
            ds eqs tap val slope hds_rb hds_leg hcost htap hval heval v hv_ker hv1
        · by_cases h2 : ∃ v : Fin k → F, (∀ a ∈ eqs, dotProduct a v = 0) ∧ dotProduct (slope w2) v ≠ 0
          · rcases h2 with ⟨v, hv_ker, hv2⟩
            exact elim_binary_gate k m cs h (Or.inl hand) w2 w1 hw2 hw1 (Or.inr hins)
              ds eqs tap val slope hds_rb hds_leg hcost htap hval heval v hv_ker hv2
          · push Not at h1 h2
            have hcost_h : gateListCost [h] = 1 := by
              rw [gateListCost_singleton, isCostGate_of_binary ⟨Or.inl hand, by simp [hins]⟩]; rfl
            refine ⟨ds ++ [Gate.mk .and [val w1, val w2]], eqs, tap,
              fun w => if w < k + m + cs.length then val w else m + ds.length,
              fun w => if w < k + m + cs.length then slope w else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · apply readsBackList_snoc hds_rb
              intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · exact hval w1 hw1
              · exact hval w2 hw2
            · intro g hg
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
              rcases hg with hg | rfl
              · exact hds_leg g hg
              · exact isLegalGate_and2 (val w1) (val w2)
            · rw [gateListCost_append, gateListCost_append, cost_and2, hcost_h]; omega
            · intro i; rw [List.length_append, List.length_singleton]; have := htap i; omega
            · intro w hw
              dsimp only
              rw [List.length_append, List.length_singleton] at hw ⊢
              split_ifs with hlt
              · have := hval w hlt; omega
              · omega
            · intro addr haddr
              have hdw_old : ∀ r < m + ds.length, ((ds ++ [Gate.mk .and [val w1, val w2]]).foldl stepWires addr).getD r false = (ds.foldl stepWires addr).getD r false :=
                fun r hr => foldl_step_append_getD_lt ds [Gate.mk .and [val w1, val w2]] addr (by rw [haddr]; exact hr)
              have hp_eq : (fun i : Fin k => b2f (((ds ++ [Gate.mk .and [val w1, val w2]]).foldl stepWires addr).getD (tap i) false)) =
                  (fun i : Fin k => b2f ((ds.foldl stepWires addr).getD (tap i) false)) := by
                funext i; rw [hdw_old (tap i) (htap i)]
              dsimp only
              intro u hu w hw
              rw [hp_eq]
              rw [List.length_append, List.length_singleton] at hw
              by_cases hlt : w < k + m + cs.length
              · simp only [hlt, ↓reduceIte]
                rw [hdw_old (val w) (hval w hlt)]
                rw [foldl_step_append_getD_lt cs [h] _ (by rw [List.length_append, bits_length, haddr]; exact hlt)]
                exact heval addr haddr u hu w hlt
              · have hweq : w = k + m + cs.length := by omega
                subst hweq
                simp only [hlt, ↓reduceIte, dot_zero_left, add_zero]
                have hidx_c : k + m + cs.length = (bits k ((fun i => b2f ((ds.foldl stepWires addr).getD (tap i) false)) + u) ++ addr).length + cs.length := by
                  rw [List.length_append, bits_length, haddr]
                have hidx_d : m + ds.length = addr.length + ds.length := by rw [haddr]
                rw [hidx_c, foldl_step_snoc_val, hidx_d, foldl_step_snoc_val, hins, hand]
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, b2f_and]
                rw [heval addr haddr u hu w1 hw1, heval addr haddr u hu w2 hw2, h1 u hu, h2 u hu, add_zero, add_zero]
      · by_cases h1 : ∃ v : Fin k → F, (∀ a ∈ eqs, dotProduct a v = 0) ∧ dotProduct (slope w1) v ≠ 0
        · rcases h1 with ⟨v, hv_ker, hv1⟩
          exact elim_binary_gate k m cs h (Or.inr hor) w1 w2 hw1 hw2 (Or.inl hins)
            ds eqs tap val slope hds_rb hds_leg hcost htap hval heval v hv_ker hv1
        · by_cases h2 : ∃ v : Fin k → F, (∀ a ∈ eqs, dotProduct a v = 0) ∧ dotProduct (slope w2) v ≠ 0
          · rcases h2 with ⟨v, hv_ker, hv2⟩
            exact elim_binary_gate k m cs h (Or.inr hor) w2 w1 hw2 hw1 (Or.inr hins)
              ds eqs tap val slope hds_rb hds_leg hcost htap hval heval v hv_ker hv2
          · push Not at h1 h2
            have hcost_h : gateListCost [h] = 1 := by
              rw [gateListCost_singleton, isCostGate_of_binary ⟨Or.inr hor, by simp [hins]⟩]; rfl
            refine ⟨ds ++ [Gate.mk .or [val w1, val w2]], eqs, tap,
              fun w => if w < k + m + cs.length then val w else m + ds.length,
              fun w => if w < k + m + cs.length then slope w else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · apply readsBackList_snoc hds_rb
              intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · exact hval w1 hw1
              · exact hval w2 hw2
            · intro g hg
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
              rcases hg with hg | rfl
              · exact hds_leg g hg
              · exact isLegalGate_or2 (val w1) (val w2)
            · rw [gateListCost_append, gateListCost_append, cost_or2, hcost_h]; omega
            · intro i; rw [List.length_append, List.length_singleton]; have := htap i; omega
            · intro w hw
              dsimp only
              rw [List.length_append, List.length_singleton] at hw ⊢
              split_ifs with hlt
              · have := hval w hlt; omega
              · omega
            · intro addr haddr
              have hdw_old : ∀ r < m + ds.length, ((ds ++ [Gate.mk .or [val w1, val w2]]).foldl stepWires addr).getD r false = (ds.foldl stepWires addr).getD r false :=
                fun r hr => foldl_step_append_getD_lt ds [Gate.mk .or [val w1, val w2]] addr (by rw [haddr]; exact hr)
              have hp_eq : (fun i : Fin k => b2f (((ds ++ [Gate.mk .or [val w1, val w2]]).foldl stepWires addr).getD (tap i) false)) =
                  (fun i : Fin k => b2f ((ds.foldl stepWires addr).getD (tap i) false)) := by
                funext i; rw [hdw_old (tap i) (htap i)]
              dsimp only
              intro u hu w hw
              rw [hp_eq]
              rw [List.length_append, List.length_singleton] at hw
              by_cases hlt : w < k + m + cs.length
              · simp only [hlt, ↓reduceIte]
                rw [hdw_old (val w) (hval w hlt)]
                rw [foldl_step_append_getD_lt cs [h] _ (by rw [List.length_append, bits_length, haddr]; exact hlt)]
                exact heval addr haddr u hu w hlt
              · have hweq : w = k + m + cs.length := by omega
                subst hweq
                simp only [hlt, ↓reduceIte, dot_zero_left, add_zero]
                have hidx_c : k + m + cs.length = (bits k ((fun i => b2f ((ds.foldl stepWires addr).getD (tap i) false)) + u) ++ addr).length + cs.length := by
                  rw [List.length_append, bits_length, haddr]
                have hidx_d : m + ds.length = addr.length + ds.length := by rw [haddr]
                rw [hidx_c, foldl_step_snoc_val, hidx_d, foldl_step_snoc_val, hins, hor]
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, b2f_or]
                rw [heval addr haddr u hu w1 hw1, heval addr haddr u hu w2 hw2, h1 u hu, h2 u hu, add_zero, add_zero]
      · have hcost_h : gateListCost [h] = 0 := by
          rw [gateListCost_singleton, isCostGate_of_not_binary]
          · rfl
          · simp [hmod]
        refine ⟨ds ++ [Gate.mk (.mod 2) [val w1, val w2]], eqs, tap,
          fun w => if w < k + m + cs.length then val w else m + ds.length,
          fun w => if w < k + m + cs.length then slope w else slope w1 + slope w2, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · apply readsBackList_snoc hds_rb
          intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact hval w1 hw1
          · exact hval w2 hw2
        · intro g hg
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with hg | rfl
          · exact hds_leg g hg
          · exact isLegalGate_xnor (val w1) (val w2)
        · rw [gateListCost_append, gateListCost_append, cost_xnor, hcost_h]; omega
        · intro i; rw [List.length_append, List.length_singleton]; have := htap i; omega
        · intro w hw
          dsimp only
          rw [List.length_append, List.length_singleton] at hw ⊢
          split_ifs with hlt
          · have := hval w hlt; omega
          · omega
        · intro addr haddr
          have hdw_old : ∀ r < m + ds.length, ((ds ++ [Gate.mk (.mod 2) [val w1, val w2]]).foldl stepWires addr).getD r false = (ds.foldl stepWires addr).getD r false :=
            fun r hr => foldl_step_append_getD_lt ds [Gate.mk (.mod 2) [val w1, val w2]] addr (by rw [haddr]; exact hr)
          have hp_eq : (fun i : Fin k => b2f (((ds ++ [Gate.mk (.mod 2) [val w1, val w2]]).foldl stepWires addr).getD (tap i) false)) =
              (fun i : Fin k => b2f ((ds.foldl stepWires addr).getD (tap i) false)) := by
            funext i; rw [hdw_old (tap i) (htap i)]
          dsimp only
          intro u hu w hw
          rw [hp_eq]
          rw [List.length_append, List.length_singleton] at hw
          by_cases hlt : w < k + m + cs.length
          · simp only [hlt, ↓reduceIte]
            rw [hdw_old (val w) (hval w hlt)]
            rw [foldl_step_append_getD_lt cs [h] _ (by rw [List.length_append, bits_length, haddr]; exact hlt)]
            exact heval addr haddr u hu w hlt
          · have hweq : w = k + m + cs.length := by omega
            subst hweq
            simp only [hlt, ↓reduceIte]
            have hidx_c : k + m + cs.length = (bits k ((fun i => b2f ((ds.foldl stepWires addr).getD (tap i) false)) + u) ++ addr).length + cs.length := by
              rw [List.length_append, bits_length, haddr]
            have hidx_d : m + ds.length = addr.length + ds.length := by rw [haddr]
            rw [hidx_c, foldl_step_snoc_val, hidx_d, foldl_step_snoc_val, hins, hmod]
            simp only [List.map_cons, List.map_nil, b2f_mod2_two]
            rw [heval addr haddr u hu w1 hw1, heval addr haddr u hu w2 hw2, dot_add_left]
            ring
      · simp [hins] at hnotlen
    | _ :: _ :: _ :: _ =>
      simp [hins] at hlen_le

lemma ker_trivial_card_le {k : ℕ} (eqs : List (Fin k → F))
    (hker : ∀ u : Fin k → F, (∀ a ∈ eqs, dotProduct a u = 0) → u = 0) :
    k ≤ eqs.length := by
  let φ : (Fin k → F) → (Fin eqs.length → F) := fun u j => dotProduct (eqs.get j) u
  have hinj : Function.Injective φ := by
    intro u v huv
    have hsum : ∀ a ∈ eqs, dotProduct a (u + v) = 0 := by
      intro a ha
      rw [List.mem_iff_get] at ha
      rcases ha with ⟨j, rfl⟩
      have hj : dotProduct (eqs.get j) u = dotProduct (eqs.get j) v := congrFun huv j
      rw [dot_add_right, hj, f_add_self]
    have h0 : u + v = 0 := hker (u + v) hsum
    funext i
    have hi : u i + v i = 0 := congrFun h0 i
    exact f_eq_of_add_eq_zero hi
  have hcard : Fintype.card (Fin k → F) ≤ Fintype.card (Fin eqs.length → F) :=
    Fintype.card_le_of_injective φ hinj
  simp only [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

def shiftGate (k : ℕ) (h : Gate) : Gate :=
  Gate.mk h.op (h.inputs.map (· + k))

def shiftGates (k : ℕ) (gs : List Gate) : List Gate :=
  gs.map (shiftGate k)

lemma shiftGates_len (k : ℕ) (gs : List Gate) : (shiftGates k gs).length = gs.length := by
  simp [shiftGates]

lemma shiftGates_legal (k : ℕ) (gs : List Gate) (hleg : ∀ h ∈ gs, isLegalGate h) :
    ∀ h ∈ shiftGates k gs, isLegalGate h := by
  intro h hh
  simp only [shiftGates, List.mem_map] at hh
  rcases hh with ⟨g, hg, rfl⟩
  have ⟨hl, ho⟩ := hleg g hg
  refine ⟨by simpa [shiftGate] using hl, ?_⟩
  simpa [shiftGate] using ho

lemma shiftGates_cost (k : ℕ) (gs : List Gate) :
    gateListCost (shiftGates k gs) = gateListCost gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [shiftGates, List.map_cons, gateListCost, List.countP_cons] at ih ⊢
    have hce : isCostGate (shiftGate k g) = isCostGate g := by
      by_cases hp : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2
      · rw [isCostGate_of_binary (by simpa [shiftGate] using hp), isCostGate_of_binary hp]
      · rw [isCostGate_of_not_binary (by simpa [shiftGate] using hp), isCostGate_of_not_binary hp]
    rw [hce]
    omega

lemma shiftGates_readsBack (k m : ℕ) (gs : List Gate) (hrb : readsBackList m gs) :
    readsBackList (k + m) (shiftGates k gs) := by
  induction gs using List.reverseRecOn with
  | nil => exact readsBackList_nil (k + m)
  | append_singleton gs g ih =>
    have ⟨hgs, hg⟩ := readsBackList_of_snoc hrb
    have hprev := ih hgs
    have hrew : shiftGates k (gs ++ [g]) = shiftGates k gs ++ [shiftGate k g] := by
      simp [shiftGates]
    rw [hrew]
    apply readsBackList_snoc hprev
    intro i hi
    simp only [shiftGate, List.mem_map] at hi
    rcases hi with ⟨j, hj, rfl⟩
    rw [shiftGates_len]
    have := hg j hj
    omega

lemma shiftGates_eval (k m : ℕ) (gs : List Gate) (hrb : readsBackList m gs)
    (xs addr : List Bool) (hxs : xs.length = k) (haddr : addr.length = m) :
    ∀ w < m + gs.length,
      ((shiftGates k gs).foldl stepWires (xs ++ addr)).getD (k + w) false =
        (gs.foldl stepWires addr).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w hw
    simp only [shiftGates, List.map_nil, List.foldl_nil]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hxs]; omega)]
    rw [hxs, Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
  | append_singleton gs g ih =>
    have ⟨hgs, hg⟩ := readsBackList_of_snoc hrb
    have hprev := ih hgs
    have hrew : shiftGates k (gs ++ [g]) = shiftGates k gs ++ [shiftGate k g] := by
      simp [shiftGates]
    rw [hrew]
    intro w hw
    rw [List.length_append, List.length_singleton] at hw
    by_cases hlt : w < m + gs.length
    · rw [foldl_step_append_getD_lt (shiftGates k gs) [shiftGate k g] (xs ++ addr)
        (by rw [List.length_append, hxs, haddr, shiftGates_len]; omega)]
      rw [foldl_step_append_getD_lt gs [g] addr (by rw [haddr]; exact hlt)]
      exact hprev w hlt
    · have hweq : w = m + gs.length := by omega
      subst hweq
      have hidx1 : k + (m + gs.length) = (xs ++ addr).length + (shiftGates k gs).length := by
        rw [List.length_append, hxs, haddr, shiftGates_len]; omega
      have hidx2 : m + gs.length = addr.length + gs.length := by rw [haddr]
      rw [hidx1, foldl_step_snoc_val, hidx2, foldl_step_snoc_val]
      simp only [shiftGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      simp only [Function.comp_apply]
      have hj' : j < m + gs.length := hg j hj
      have hcomm : j + k = k + j := Nat.add_comm j k
      rw [hcomm]
      exact hprev j hj'

def prodChain (k : ℕ) (tap : Fin k → ℕ) (baseLen acc0 : ℕ) : (i : ℕ) → i ≤ k → List Gate × ℕ
  | 0, _ => ([], acc0)
  | i + 1, hi =>
    let res := prodChain k tap baseLen acc0 i (Nat.le_of_succ_le hi)
    let gs := res.1
    let acc := res.2
    let cur := baseLen + gs.length
    let wTap := k + tap ⟨i, hi⟩
    let step : List Gate :=
      [ Gate.mk (.mod 2) [i, wTap]
      , Gate.mk .not [cur]
      , Gate.mk .and [cur + 1, k + i]
      , Gate.mk (.mod 2) [acc, cur + 2]
      , Gate.mk .not [cur + 3] ]
    (gs ++ step, cur + 4)

lemma prodChain_props (k t : ℕ) (gs0 : List Gate) (tap : Fin k → ℕ) (acc0 : ℕ)
    (hgs0_rb : readsBackList (2 * k + t) gs0)
    (hacc0 : acc0 < 2 * k + t + gs0.length)
    (htap : ∀ j : Fin k, k + tap j < 2 * k + t + gs0.length)
    (i : ℕ) (hi : i ≤ k) :
    let res := prodChain k tap (2 * k + t + gs0.length) acc0 i hi
    readsBackList (2 * k + t) (gs0 ++ res.1) ∧
    (∀ h ∈ res.1, isLegalGate h) ∧
    gateListCost res.1 = i ∧
    res.2 < 2 * k + t + gs0.length + res.1.length ∧
    ∀ (x y : Fin k → F) (z : Fin t → F),
      let inp := bits k x ++ bits k y ++ bits t z
      let w0 := gs0.foldl stepWires inp
      b2f (((gs0 ++ res.1).foldl stepWires inp).getD res.2 false) =
        b2f (w0.getD acc0 false) +
          ∑ j : Fin k, if j.val < i then (x j + b2f (w0.getD (k + tap j) false)) * y j else 0 := by
  induction i with
  | zero =>
    refine ⟨by simpa [prodChain] using hgs0_rb,
      fun h hh => by simp [prodChain] at hh,
      by simp [prodChain, gateListCost],
      by simpa [prodChain] using hacc0, ?_⟩
    intro x y z
    simp [prodChain]
  | succ i ih =>
    have hi_le : i ≤ k := Nat.le_of_succ_le hi
    rcases ih hi_le with ⟨hrb_i, hleg_i, hcost_i, hacc_i, heval_i⟩
    set baseLen := 2 * k + t + gs0.length
    set res := prodChain k tap baseLen acc0 i hi_le
    set gs := res.1
    set acc := res.2
    set cur := baseLen + gs.length
    set wTap := k + tap ⟨i, hi⟩
    set g1 : Gate := Gate.mk (.mod 2) [i, wTap]
    set g2 : Gate := Gate.mk .not [cur]
    set g3 : Gate := Gate.mk .and [cur + 1, k + i]
    set g4 : Gate := Gate.mk (.mod 2) [acc, cur + 2]
    set g5 : Gate := Gate.mk .not [cur + 3]
    have hcur_eq : cur = 2 * k + t + (gs0 ++ gs).length := by
      simp only [cur, baseLen, List.length_append]; omega
    have hwTap_lt : wTap < cur := by have := htap ⟨i, hi⟩; omega
    have hrb1 : readsBackList (2 * k + t) ((gs0 ++ gs) ++ [g1]) := by
      apply readsBackList_snoc hrb_i
      intro u hu; simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> omega
    have hrb2 : readsBackList (2 * k + t) (((gs0 ++ gs) ++ [g1]) ++ [g2]) := by
      apply readsBackList_snoc hrb1
      intro u hu; simp only [g2, List.mem_cons, List.not_mem_nil, or_false] at hu
      subst hu; rw [List.length_append, List.length_singleton]; omega
    have hrb3 : readsBackList (2 * k + t) ((((gs0 ++ gs) ++ [g1]) ++ [g2]) ++ [g3]) := by
      apply readsBackList_snoc hrb2
      intro u hu; simp only [g3, List.mem_cons, List.not_mem_nil, or_false] at hu
      rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      rcases hu with rfl | rfl <;> omega
    have hrb4 : readsBackList (2 * k + t) (((((gs0 ++ gs) ++ [g1]) ++ [g2]) ++ [g3]) ++ [g4]) := by
      apply readsBackList_snoc hrb3
      intro u hu; simp only [g4, List.mem_cons, List.not_mem_nil, or_false] at hu
      rw [List.length_append, List.length_append, List.length_append,
        List.length_singleton, List.length_singleton, List.length_singleton]
      rcases hu with rfl | rfl <;> omega
    have hrb5 : readsBackList (2 * k + t) ((((((gs0 ++ gs) ++ [g1]) ++ [g2]) ++ [g3]) ++ [g4]) ++ [g5]) := by
      apply readsBackList_snoc hrb4
      intro u hu; simp only [g5, List.mem_cons, List.not_mem_nil, or_false] at hu
      subst hu
      rw [List.length_append, List.length_append, List.length_append, List.length_append,
        List.length_singleton, List.length_singleton, List.length_singleton, List.length_singleton]
      omega
    have hstep_eq : gs0 ++ (gs ++ [g1, g2, g3, g4, g5]) =
        (((((gs0 ++ gs) ++ [g1]) ++ [g2]) ++ [g3]) ++ [g4]) ++ [g5] := by
      simp [List.append_assoc]
    have hres1 : (prodChain k tap baseLen acc0 (i + 1) hi).1 = gs ++ [g1, g2, g3, g4, g5] := rfl
    have hres2 : (prodChain k tap baseLen acc0 (i + 1) hi).2 = cur + 4 := rfl
    dsimp only
    rw [hres1, hres2]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hstep_eq]; exact hrb5
    · intro h hh
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with hh | rfl | rfl | rfl | rfl | rfl
      · exact hleg_i h hh
      · exact isLegalGate_xnor i wTap
      · exact isLegalGate_not cur
      · exact isLegalGate_and2 (cur + 1) (k + i)
      · exact isLegalGate_xnor acc (cur + 2)
      · exact isLegalGate_not (cur + 3)
    · rw [gateListCost_append, hcost_i]
      have hsc : gateListCost [g1, g2, g3, g4, g5] = 1 := by
        have hlist : [g1, g2, g3, g4, g5] = [g1] ++ [g2] ++ [g3] ++ [g4] ++ [g5] := rfl
        rw [hlist, gateListCost_append, gateListCost_append, gateListCost_append, gateListCost_append,
          cost_xnor, cost_not, cost_and2, cost_xnor, cost_not]
      omega
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · intro x y z
      set inp := bits k x ++ bits k y ++ bits t z
      have hinp_len : inp.length = 2 * k + t := by
        simp only [inp, List.length_append, bits_length]; omega
      set pref := gs0 ++ gs
      set w0 := gs0.foldl stepWires inp
      set wp := pref.foldl stepWires inp
      have hwp_w0 : ∀ r < baseLen, wp.getD r false = w0.getD r false :=
        fun r hr => foldl_step_append_getD_lt gs0 gs inp (by rw [hinp_len]; exact hr)
      have hget_xi : b2f (wp.getD i false) = x ⟨i, hi⟩ := by
        rw [hwp_w0 i (by omega)]
        rw [foldl_step_getD_lt gs0 inp (by rw [hinp_len]; omega)]
        simp only [inp, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by rw [List.length_append, bits_length, bits_length]; omega)]
        rw [List.getElem?_append_left (by rw [bits_length]; exact hi)]
        rw [← List.getD_eq_getElem?_getD, bits_getD k x i hi, b2f_decide_eq_one]
      have hget_yi : b2f (wp.getD (k + i) false) = y ⟨i, hi⟩ := by
        rw [hwp_w0 (k + i) (by omega)]
        rw [foldl_step_getD_lt gs0 inp (by rw [hinp_len]; omega)]
        simp only [inp, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by rw [List.length_append, bits_length, bits_length]; omega)]
        rw [List.getElem?_append_right (by rw [bits_length]; omega)]
        rw [bits_length, Nat.add_sub_cancel_left]
        rw [← List.getD_eq_getElem?_getD, bits_getD k y i hi, b2f_decide_eq_one]
      have hget_tap : wp.getD wTap false = w0.getD wTap false :=
        hwp_w0 wTap (htap ⟨i, hi⟩)
      set p1 := pref ++ [g1]
      set p2 := p1 ++ [g2]
      set p3 := p2 ++ [g3]
      set p4 := p3 ++ [g4]
      set p5 := p4 ++ [g5]
      have hcur_len : cur = inp.length + pref.length := by
        rw [hinp_len, hcur_eq]
      have hp1_val : b2f ((p1.foldl stepWires inp).getD cur false) =
          x ⟨i, hi⟩ + b2f (w0.getD wTap false) + 1 := by
        rw [hcur_len, foldl_step_snoc_val]
        simp only [g1, List.map_cons, List.map_nil, b2f_mod2_two]
        rw [hget_xi, hget_tap]
      have hp2_val : b2f ((p2.foldl stepWires inp).getD (cur + 1) false) =
          x ⟨i, hi⟩ + b2f (w0.getD wTap false) := by
        have hidx : cur + 1 = inp.length + p1.length := by
          simp only [p1, List.length_append, List.length_singleton, hcur_len]; omega
        rw [hidx, foldl_step_snoc_val]
        simp only [g2, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2f_not, hp1_val]
        have h11 : (1 : F) + 1 = 0 := f_add_self 1
        calc
          x ⟨i, hi⟩ + b2f (w0.getD wTap false) + 1 + 1
              = x ⟨i, hi⟩ + b2f (w0.getD wTap false) + (1 + 1) := by ring
          _ = x ⟨i, hi⟩ + b2f (w0.getD wTap false) := by rw [h11, add_zero]
      have hp3_val : b2f ((p3.foldl stepWires inp).getD (cur + 2) false) =
          (x ⟨i, hi⟩ + b2f (w0.getD wTap false)) * y ⟨i, hi⟩ := by
        have hidx : cur + 2 = inp.length + p2.length := by
          simp only [p2, p1, List.length_append, List.length_singleton, hcur_len]; omega
        rw [hidx, foldl_step_snoc_val]
        simp only [g3, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, b2f_and]
        have hki : (p2.foldl stepWires inp).getD (k + i) false = wp.getD (k + i) false := by
          have hr : p2 = pref ++ [g1, g2] := by simp [p2, p1, List.append_assoc]
          rw [hr]
          exact foldl_step_append_getD_lt pref [g1, g2] inp (by rw [← hcur_len]; omega)
        rw [hp2_val, hki, hget_yi]
      have hp4_val : b2f ((p4.foldl stepWires inp).getD (cur + 3) false) =
          b2f (wp.getD acc false) + (x ⟨i, hi⟩ + b2f (w0.getD wTap false)) * y ⟨i, hi⟩ + 1 := by
        have hidx : cur + 3 = inp.length + p3.length := by
          simp only [p3, p2, p1, List.length_append, List.length_singleton, hcur_len]; omega
        rw [hidx, foldl_step_snoc_val]
        simp only [g4, List.map_cons, List.map_nil, b2f_mod2_two]
        have hacc_old : (p3.foldl stepWires inp).getD acc false = wp.getD acc false := by
          have hr : p3 = pref ++ [g1, g2, g3] := by simp [p3, p2, p1, List.append_assoc]
          rw [hr]
          exact foldl_step_append_getD_lt pref [g1, g2, g3] inp (by rw [← hcur_len]; exact hacc_i)
        rw [hacc_old, hp3_val]
      have hp5_val : b2f ((p5.foldl stepWires inp).getD (cur + 4) false) =
          b2f (wp.getD acc false) + (x ⟨i, hi⟩ + b2f (w0.getD wTap false)) * y ⟨i, hi⟩ := by
        have hidx : cur + 4 = inp.length + p4.length := by
          simp only [p4, p3, p2, p1, List.length_append, List.length_singleton, hcur_len]; omega
        rw [hidx, foldl_step_snoc_val]
        simp only [g5, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2f_not, hp4_val]
        have h11 : (1 : F) + 1 = 0 := f_add_self 1
        calc
          b2f (wp.getD acc false) + (x ⟨i, hi⟩ + b2f (w0.getD wTap false)) * y ⟨i, hi⟩ + 1 + 1
              = b2f (wp.getD acc false) + (x ⟨i, hi⟩ + b2f (w0.getD wTap false)) * y ⟨i, hi⟩ + (1 + 1) := by ring
          _ = b2f (wp.getD acc false) + (x ⟨i, hi⟩ + b2f (w0.getD wTap false)) * y ⟨i, hi⟩ := by rw [h11, add_zero]
      have hsum_step :
          (∑ j : Fin k, if j.val < i + 1 then (x j + b2f (w0.getD (k + tap j) false)) * y j else 0) =
          (∑ j : Fin k, if j.val < i then (x j + b2f (w0.getD (k + tap j) false)) * y j else 0) +
            (x ⟨i, hi⟩ + b2f (w0.getD wTap false)) * y ⟨i, hi⟩ := by
        have hsplit : ∀ j : Fin k,
            (if j.val < i + 1 then (x j + b2f (w0.getD (k + tap j) false)) * y j else 0) =
            (if j.val < i then (x j + b2f (w0.getD (k + tap j) false)) * y j else 0) +
              (if j = ⟨i, hi⟩ then (x j + b2f (w0.getD (k + tap j) false)) * y j else 0) := by
          intro j
          by_cases hji : j.val < i
          · have hlt1 : j.val < i + 1 := by omega
            have hne : j ≠ ⟨i, hi⟩ := by
              intro heq
              have hv : j.val = i := congrArg Fin.val heq
              omega
            simp [hji, hlt1, hne]
          · by_cases hjeq : j = ⟨i, hi⟩
            · subst hjeq; simp
            · have hnot1 : ¬ (j.val < i + 1) := by
                intro hlt1
                have hv : j.val = i := by omega
                exact hjeq (Fin.ext hv)
              simp [hji, hjeq, hnot1]
        simp_rw [hsplit]
        rw [Finset.sum_add_distrib]
        simp [wTap]
      rw [hstep_eq]
      change b2f ((p5.foldl stepWires inp).getD (cur + 4) false) = _
      rw [hp5_val, heval_i x y z, hsum_step, add_assoc]

lemma main_equiv (k t : ℕ) (g : (Fin k → F) → (Fin t → F) → F) (s : ℕ) :
    (∃ C : Circuit,
      (ReadsBack (2 * k + t) C ∧
        (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
          (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))) ∧
      C.gates.countP (fun h => @decide ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _)) ≤ s ∧
      ∀ (x y : Fin k → F) (z : Fin t → F),
        C.eval (bits k x ++ bits k y ++ bits t z) = decide (dotProduct x y + g y z = 1)) ↔
    (k ≤ s ∧ ∃ (D : Circuit) (tap : Fin k → ℕ),
      (ReadsBack (k + t) D ∧
        (∀ h ∈ D.gates, h.inputs.length ≤ 2 ∧
          (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))) ∧
      D.gates.countP (fun h => @decide ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _)) ≤ s - k ∧
      D.output < k + t + D.size ∧
      (∀ i, tap i < k + t + D.size) ∧
      ∀ (y : Fin k → F) (z : Fin t → F),
        let inp := bits k y ++ bits t z
        let p := fun i : Fin k => if (D.wires inp).getD (tap i) false then (1 : F) else 0
        g y z = (if D.eval inp then 1 else 0) + dotProduct p y) := by
  constructor
  · rintro ⟨C, ⟨hC_rb, hC_leg⟩, hC_cost, hC_eval⟩
    have hrb_list : readsBackList (k + (k + t)) C.gates := by
      have h2k : k + (k + t) = 2 * k + t := by omega
      rw [h2k]
      exact hC_rb
    rcases slice_induction k (k + t) C.gates hrb_list hC_leg with
      ⟨ds, eqs, tap, val, slope, hds_rb, hds_leg, hcost, htap, hval, heval⟩
    have hout_exists : ∃ (D : Circuit) (α : Fin k → F),
        ReadsBack (k + t) D ∧
        (∀ h ∈ D.gates, isLegalGate h) ∧
        gateListCost D.gates + eqs.length ≤ gateListCost C.gates ∧
        D.output < k + t + D.size ∧
        (∀ i : Fin k, tap i < k + t + D.size) ∧
        (∀ (y : Fin k → F) (z : Fin t → F),
          let inp := bits k y ++ bits t z
          let p : Fin k → F := fun i => b2f ((D.wires inp).getD (tap i) false)
          ∀ u : Fin k → F, (∀ a ∈ eqs, dotProduct a u = 0) →
            b2f (C.eval (bits k (p + u) ++ bits k y ++ bits t z)) =
              b2f (D.eval inp) + dotProduct α u) := by
      by_cases hout : C.output < k + (k + t) + C.gates.length
      · refine ⟨⟨ds, val C.output⟩, slope C.output, hds_rb, hds_leg, hcost,
          hval C.output hout, htap, ?_⟩
        intro y z inp p u hu
        have hinp_len : inp.length = k + t := by simp [inp, bits_length]
        have h1 := heval inp hinp_len u hu C.output hout
        simpa [Circuit.eval, wires_eq_foldl, inp, p, List.append_assoc] using h1
      · refine ⟨⟨ds ++ [const0Gate], k + t + ds.length⟩, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · apply readsBackList_snoc hds_rb
          intro i hi; simp [const0Gate] at hi
        · intro h hh
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hh
          rcases hh with hh | rfl
          · exact hds_leg h hh
          · exact isLegalGate_const0
        · rw [gateListCost_append, cost_const0]
          omega
        · simp [Circuit.size]
        · intro i; simp only [Circuit.size, List.length_append, List.length_singleton]; have := htap i; omega
        · intro y z inp p u _
          have hinp_len : inp.length = k + t := by simp [inp, bits_length]
          have hC_len : (C.wires (bits k (p + u) ++ bits k y ++ bits t z)).length = k + (k + t) + C.gates.length := by
            rw [wires_eq_foldl, foldl_step_len, List.length_append, List.length_append, bits_length, bits_length, bits_length]
            omega
          have hC_false : C.eval (bits k (p + u) ++ bits k y ++ bits t z) = false := by
            simp only [Circuit.eval, List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_none (by omega)]
            rfl
          have hD_false : (⟨ds ++ [const0Gate], k + t + ds.length⟩ : Circuit).eval inp = false := by
            simp only [Circuit.eval, wires_eq_foldl]
            have hidx : k + t + ds.length = inp.length + ds.length := by rw [hinp_len]
            rw [hidx, foldl_step_snoc_val]
            rfl
          rw [hC_false, hD_false, dot_zero_left, add_zero]
    rcases hout_exists with ⟨D, α, hD_rb, hD_leg, hD_cost, hD_out, hD_tap, hD_eval⟩
    have hker_triv : ∀ u : Fin k → F, (∀ a ∈ eqs, dotProduct a u = 0) → u = 0 := by
      intro u hu
      have h0 : ∀ a ∈ eqs, dotProduct a (0 : Fin k → F) = 0 := fun a _ => dot_zero_right a
      have hrel : ∀ y : Fin k → F, dotProduct u y = dotProduct α u := by
        intro y
        let z0 : Fin t → F := 0
        have heq_u := hD_eval y z0 u hu
        have heq_0 := hD_eval y z0 0 h0
        rw [hC_eval _ y z0, b2f_decide_eq_one] at heq_u heq_0
        rw [add_zero, dot_zero_right, add_zero] at heq_0
        rw [dot_add_left] at heq_u
        have hsub : (dotProduct (fun i => b2f ((D.wires (bits k y ++ bits t z0)).getD (tap i) false)) y + dotProduct u y + g y z0) +
            (dotProduct (fun i => b2f ((D.wires (bits k y ++ bits t z0)).getD (tap i) false)) y + g y z0) =
            (b2f (D.eval (bits k y ++ bits t z0)) + dotProduct α u) + b2f (D.eval (bits k y ++ bits t z0)) := by
          rw [heq_u, heq_0]
        set A := dotProduct (fun i => b2f ((D.wires (bits k y ++ bits t z0)).getD (tap i) false)) y + g y z0
        set B := b2f (D.eval (bits k y ++ bits t z0))
        have hL : (dotProduct (fun i => b2f ((D.wires (bits k y ++ bits t z0)).getD (tap i) false)) y + dotProduct u y + g y z0) + A = dotProduct u y := by
          calc
            _ = (A + A) + dotProduct u y := by ring
            _ = 0 + dotProduct u y := by rw [f_add_self A]
            _ = dotProduct u y := zero_add _
        have hR : (B + dotProduct α u) + B = dotProduct α u := by
          calc
            _ = (B + B) + dotProduct α u := by ring
            _ = 0 + dotProduct α u := by rw [f_add_self B]
            _ = dotProduct α u := zero_add _
        rw [hL, hR] at hsub
        exact hsub
      have hαu : dotProduct α u = 0 := by
        have h0y := hrel 0
        rw [dot_zero_right] at h0y
        exact h0y.symm
      funext i
      have hi := hrel (Pi.single i 1)
      rw [dot_single_right, hαu] at hi
      exact hi
    have hk_le_eqs : k ≤ eqs.length := ker_trivial_card_le eqs hker_triv
    have hk_le_s : k ≤ s := by
      have hc : gateListCost C.gates ≤ s := hC_cost
      omega
    have hD_cost_le : gateListCost D.gates ≤ s - k := by
      have hc : gateListCost C.gates ≤ s := hC_cost
      omega
    refine ⟨hk_le_s, D, tap, ⟨hD_rb, hD_leg⟩, hD_cost_le, hD_out, hD_tap, ?_⟩
    intro y z inp p
    have h0 : ∀ a ∈ eqs, dotProduct a (0 : Fin k → F) = 0 := fun a _ => dot_zero_right a
    have heq_0 := hD_eval y z 0 h0
    rw [hC_eval _ y z, b2f_decide_eq_one, add_zero, dot_zero_right, add_zero] at heq_0
    have hp_eq : (fun i : Fin k => b2f ((D.wires inp).getD (tap i) false)) = p := rfl
    rw [hp_eq] at heq_0
    calc
      g y z = (dotProduct p y + g y z) + dotProduct p y := by
        calc
          g y z = 0 + g y z := (zero_add _).symm
          _ = (dotProduct p y + dotProduct p y) + g y z := by rw [f_add_self]
          _ = (dotProduct p y + g y z) + dotProduct p y := by ring
      _ = b2f (D.eval inp) + dotProduct p y := by rw [heq_0]
  · rintro ⟨hk_le_s, D, tap, ⟨hD_rb, hD_leg⟩, hD_cost, hD_out, hD_tap, hD_eval⟩
    set gs0 := shiftGates k D.gates
    have hgs0_rb : readsBackList (2 * k + t) gs0 := by
      have h2k : 2 * k + t = k + (k + t) := by omega
      rw [h2k]
      exact shiftGates_readsBack k (k + t) D.gates hD_rb
    have hgs0_leg : ∀ h ∈ gs0, isLegalGate h := shiftGates_legal k D.gates hD_leg
    have hgs0_cost : gateListCost gs0 = gateListCost D.gates := shiftGates_cost k D.gates
    have hacc0 : k + D.output < 2 * k + t + gs0.length := by
      simp only [gs0, shiftGates_len]; simp only [Circuit.size] at hD_out; omega
    have htap_lt : ∀ j : Fin k, k + tap j < 2 * k + t + gs0.length := by
      intro j; simp only [gs0, shiftGates_len]; have := hD_tap j; simp only [Circuit.size] at this; omega
    rcases prodChain_props k t gs0 tap (k + D.output) hgs0_rb hacc0 htap_lt k (le_refl k) with
      ⟨hrb_all, hleg_chain, hcost_chain, _, heval_chain⟩
    set res := prodChain k tap (2 * k + t + gs0.length) (k + D.output) k (le_refl k)
    let C : Circuit := ⟨gs0 ++ res.1, res.2⟩
    refine ⟨C, ⟨hrb_all, ?_⟩, ?_, ?_⟩
    · intro h hh
      simp only [C, List.mem_append] at hh
      rcases hh with hh | hh
      · exact hgs0_leg h hh
      · exact hleg_chain h hh
    · show gateListCost (gs0 ++ res.1) ≤ s
      rw [gateListCost_append, hgs0_cost, hcost_chain]
      have hDc : gateListCost D.gates ≤ s - k := hD_cost
      omega
    · intro x y z
      have hchain := heval_chain x y z
      set inpD := bits k y ++ bits t z
      set inpC := bits k x ++ bits k y ++ bits t z
      have hinpD_len : inpD.length = k + t := by simp [inpD, bits_length]
      have hinpC_eq : inpC = bits k x ++ inpD := by simp [inpC, inpD, List.append_assoc]
      have hshift_out : (gs0.foldl stepWires inpC).getD (k + D.output) false = D.eval inpD := by
        rw [hinpC_eq]
        exact shiftGates_eval k (k + t) D.gates hD_rb (bits k x) inpD (bits_length k x) hinpD_len D.output hD_out
      have hshift_tap : ∀ j : Fin k, (gs0.foldl stepWires inpC).getD (k + tap j) false = (D.wires inpD).getD (tap j) false := by
        intro j
        rw [hinpC_eq]
        exact shiftGates_eval k (k + t) D.gates hD_rb (bits k x) inpD (bits_length k x) hinpD_len (tap j) (hD_tap j)
      have hb2f_C : b2f (C.eval inpC) = dotProduct x y + g y z := by
        change b2f (((gs0 ++ res.1).foldl stepWires inpC).getD res.2 false) = dotProduct x y + g y z
        rw [hchain, hshift_out]
        have hsum_eq :
            (∑ j : Fin k, if j.val < k then (x j + b2f ((gs0.foldl stepWires inpC).getD (k + tap j) false)) * y j else 0) =
            dotProduct x y + dotProduct (fun i : Fin k => b2f ((D.wires inpD).getD (tap i) false)) y := by
          have h1 : ∀ j : Fin k,
              (if j.val < k then (x j + b2f ((gs0.foldl stepWires inpC).getD (k + tap j) false)) * y j else 0) =
              x j * y j + b2f ((D.wires inpD).getD (tap j) false) * y j := by
            intro j
            simp only [j.isLt, ↓reduceIte, hshift_tap j, add_mul]
          simp_rw [h1]
          rw [Finset.sum_add_distrib]
          rfl
        rw [hsum_eq, hD_eval y z]
        show b2f (D.eval inpD) + (dotProduct x y + dotProduct (fun i => b2f ((D.wires inpD).getD (tap i) false)) y) =
          dotProduct x y + (b2f (D.eval inpD) + dotProduct (fun i => b2f ((D.wires inpD).getD (tap i) false)) y)
        ring
      rw [← f2b_b2f (C.eval inpC), hb2f_C]
      rfl


def affFun {k t : ℕ} (f : (Fin k → F) → (Fin t → F) → F) : Prop :=
  ∃ (a : Fin k → F) (b : Fin t → F) (c : F),
    ∀ y z, f y z = c + dotProduct a y + dotProduct b z

lemma affFun_const {k t : ℕ} (c : F) : affFun (k := k) (t := t) (fun _ _ => c) := by
  refine ⟨0, 0, c, fun y z => ?_⟩
  simp

lemma affFun_varY {k t : ℕ} (i : Fin k) : affFun (k := k) (t := t) (fun y _ => y i) := by
  refine ⟨Pi.single i 1, 0, 0, fun y z => ?_⟩
  simp [dot_single_left]

lemma affFun_varZ {k t : ℕ} (j : Fin t) : affFun (k := k) (t := t) (fun _ z => z j) := by
  refine ⟨0, Pi.single j 1, 0, fun y z => ?_⟩
  simp [dot_single_left]

lemma affFun_add {k t : ℕ} {f1 f2 : (Fin k → F) → (Fin t → F) → F}
    (h1 : affFun f1) (h2 : affFun f2) : affFun (fun y z => f1 y z + f2 y z) := by
  rcases h1 with ⟨a1, b1, c1, hf1⟩
  rcases h2 with ⟨a2, b2, c2, hf2⟩
  refine ⟨a1 + a2, b1 + b2, c1 + c2, fun y z => ?_⟩
  dsimp only
  rw [hf1 y z, hf2 y z, dot_add_left, dot_add_left]
  ring

lemma affFun_add_const {k t : ℕ} {f1 : (Fin k → F) → (Fin t → F) → F}
    (h1 : affFun f1) (d : F) : affFun (fun y z => f1 y z + d) :=
  affFun_add h1 (affFun_const d)

lemma cost_zero_affine (k t : ℕ) (ds : List Gate)
    (hrb : readsBackList (k + t) ds)
    (hleg : ∀ h ∈ ds, isLegalGate h)
    (hcost : gateListCost ds = 0) :
    ∀ w < k + t + ds.length,
      affFun (fun (y : Fin k → F) (z : Fin t → F) =>
        b2f ((ds.foldl stepWires (bits k y ++ bits t z)).getD w false)) := by
  induction ds using List.reverseRecOn with
  | nil =>
    intro w hw
    simp only [List.length_nil, add_zero] at hw
    by_cases hwk : w < k
    · have hfeq : (fun (y : Fin k → F) (z : Fin t → F) =>
          b2f ((([] : List Gate).foldl stepWires (bits k y ++ bits t z)).getD w false)) =
          (fun y _ => y ⟨w, hwk⟩) := by
        funext y z
        simp only [List.foldl_nil, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by rw [bits_length]; exact hwk)]
        rw [← List.getD_eq_getElem?_getD, bits_getD k y w hwk, b2f_decide_eq_one]
      rw [hfeq]
      exact affFun_varY ⟨w, hwk⟩
    · have hwt : w - k < t := by omega
      have hfeq : (fun (y : Fin k → F) (z : Fin t → F) =>
          b2f ((([] : List Gate).foldl stepWires (bits k y ++ bits t z)).getD w false)) =
          (fun _ z => z ⟨w - k, hwt⟩) := by
        funext y z
        simp only [List.foldl_nil, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by rw [bits_length]; omega)]
        rw [bits_length, ← List.getD_eq_getElem?_getD, bits_getD t z (w - k) hwt, b2f_decide_eq_one]
      rw [hfeq]
      exact affFun_varZ ⟨w - k, hwt⟩
  | append_singleton ds h ih =>
    have ⟨hrb_ds, hg_rb⟩ := readsBackList_of_snoc hrb
    have hleg_ds : ∀ g ∈ ds, isLegalGate g := fun g hg => hleg g (List.mem_append_left _ hg)
    have hleg_h : isLegalGate h := hleg h (List.mem_append_right _ (List.mem_singleton_self h))
    rw [gateListCost_append] at hcost
    have hcost_ds : gateListCost ds = 0 := by omega
    have hcost_h : gateListCost [h] = 0 := by omega
    have hprev := ih hrb_ds hleg_ds hcost_ds
    intro w hw
    rw [List.length_append, List.length_singleton] at hw
    by_cases hlt : w < k + t + ds.length
    · have hfeq : (fun (y : Fin k → F) (z : Fin t → F) =>
          b2f (((ds ++ [h]).foldl stepWires (bits k y ++ bits t z)).getD w false)) =
          (fun y z => b2f ((ds.foldl stepWires (bits k y ++ bits t z)).getD w false)) := by
        funext y z
        rw [foldl_step_append_getD_lt ds [h] _ (by rw [List.length_append, bits_length, bits_length]; exact hlt)]
      rw [hfeq]
      exact hprev w hlt
    · have hweq : w = k + t + ds.length := by omega
      subst hweq
      rcases hleg_h with ⟨hlen_le, hop⟩
      match hins : h.inputs with
      | [] =>
        have hfeq : (fun (y : Fin k → F) (z : Fin t → F) =>
            b2f (((ds ++ [h]).foldl stepWires (bits k y ++ bits t z)).getD (k + t + ds.length) false)) =
            (fun _ _ => b2f (h.op.eval [])) := by
          funext y z
          have hidx : k + t + ds.length = (bits k y ++ bits t z).length + ds.length := by
            rw [List.length_append, bits_length, bits_length]
          rw [hidx, foldl_step_snoc_val, hins]
          rfl
        rw [hfeq]
        exact affFun_const (b2f (h.op.eval []))
      | [w1] =>
        have hw1 : w1 < k + t + ds.length := hg_rb w1 (by simp [hins])
        have haff1 := hprev w1 hw1
        rcases hop with hand | hor | hmod | ⟨hnot, _⟩
        · have hfeq : (fun (y : Fin k → F) (z : Fin t → F) =>
              b2f (((ds ++ [h]).foldl stepWires (bits k y ++ bits t z)).getD (k + t + ds.length) false)) =
              (fun y z => b2f ((ds.foldl stepWires (bits k y ++ bits t z)).getD w1 false)) := by
            funext y z
            have hidx : k + t + ds.length = (bits k y ++ bits t z).length + ds.length := by
              rw [List.length_append, bits_length, bits_length]
            rw [hidx, foldl_step_snoc_val, hins, hand]
            simp [GateOp.eval]
          rw [hfeq]; exact haff1
        · have hfeq : (fun (y : Fin k → F) (z : Fin t → F) =>
              b2f (((ds ++ [h]).foldl stepWires (bits k y ++ bits t z)).getD (k + t + ds.length) false)) =
              (fun y z => b2f ((ds.foldl stepWires (bits k y ++ bits t z)).getD w1 false)) := by
            funext y z
            have hidx : k + t + ds.length = (bits k y ++ bits t z).length + ds.length := by
              rw [List.length_append, bits_length, bits_length]
            rw [hidx, foldl_step_snoc_val, hins, hor]
            simp [GateOp.eval]
          rw [hfeq]; exact haff1
        · have hfeq : (fun (y : Fin k → F) (z : Fin t → F) =>
              b2f (((ds ++ [h]).foldl stepWires (bits k y ++ bits t z)).getD (k + t + ds.length) false)) =
              (fun y z => b2f ((ds.foldl stepWires (bits k y ++ bits t z)).getD w1 false) + 1) := by
            funext y z
            have hidx : k + t + ds.length = (bits k y ++ bits t z).length + ds.length := by
              rw [List.length_append, bits_length, bits_length]
            rw [hidx, foldl_step_snoc_val, hins, hmod]
            simp only [List.map_cons, List.map_nil]
            exact b2f_mod2_one _
          rw [hfeq]; exact affFun_add_const haff1 1
        · have hfeq : (fun (y : Fin k → F) (z : Fin t → F) =>
              b2f (((ds ++ [h]).foldl stepWires (bits k y ++ bits t z)).getD (k + t + ds.length) false)) =
              (fun y z => b2f ((ds.foldl stepWires (bits k y ++ bits t z)).getD w1 false) + 1) := by
            funext y z
            have hidx : k + t + ds.length = (bits k y ++ bits t z).length + ds.length := by
              rw [List.length_append, bits_length, bits_length]
            rw [hidx, foldl_step_snoc_val, hins, hnot]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2f_not]
          rw [hfeq]; exact affFun_add_const haff1 1
      | [w1, w2] =>
        have hw1 : w1 < k + t + ds.length := hg_rb w1 (by simp [hins])
        have hw2 : w2 < k + t + ds.length := hg_rb w2 (by simp [hins])
        rcases hop with hand | hor | hmod | ⟨_, hnotlen⟩
        · have h1 : gateListCost [h] = 1 := by
            rw [gateListCost_singleton, isCostGate_of_binary ⟨Or.inl hand, by simp [hins]⟩]; rfl
          omega
        · have h1 : gateListCost [h] = 1 := by
            rw [gateListCost_singleton, isCostGate_of_binary ⟨Or.inr hor, by simp [hins]⟩]; rfl
          omega
        · have hfeq : (fun (y : Fin k → F) (z : Fin t → F) =>
              b2f (((ds ++ [h]).foldl stepWires (bits k y ++ bits t z)).getD (k + t + ds.length) false)) =
              (fun y z => b2f ((ds.foldl stepWires (bits k y ++ bits t z)).getD w1 false) +
                b2f ((ds.foldl stepWires (bits k y ++ bits t z)).getD w2 false) + 1) := by
            funext y z
            have hidx : k + t + ds.length = (bits k y ++ bits t z).length + ds.length := by
              rw [List.length_append, bits_length, bits_length]
            rw [hidx, foldl_step_snoc_val, hins, hmod]
            simp only [List.map_cons, List.map_nil]
            exact b2f_mod2_two _ _
          rw [hfeq]
          exact affFun_add_const (affFun_add (hprev w1 hw1) (hprev w2 hw2)) 1
        · simp [hins] at hnotlen
      | _ :: _ :: _ :: _ =>
        simp [hins] at hlen_le

lemma cost_le_one_decomp (k t : ℕ) (ds : List Gate)
    (hrb : readsBackList (k + t) ds)
    (hleg : ∀ h ∈ ds, isLegalGate h)
    (hcost : gateListCost ds ≤ 1) :
    ∃ (u v : (Fin k → F) → (Fin t → F) → F),
      affFun u ∧ affFun v ∧
      ∀ w < k + t + ds.length,
        ∃ (fw : (Fin k → F) → (Fin t → F) → F) (cw : F),
          affFun fw ∧
          ∀ (y : Fin k → F) (z : Fin t → F),
            b2f ((ds.foldl stepWires (bits k y ++ bits t z)).getD w false) =
              fw y z + cw * (u y z * v y z) := by
  induction ds using List.reverseRecOn with
  | nil =>
    refine ⟨fun _ _ => 0, fun _ _ => 0, affFun_const 0, affFun_const 0, ?_⟩
    intro w hw
    refine ⟨fun y z => b2f ((([] : List Gate).foldl stepWires (bits k y ++ bits t z)).getD w false), 0,
      cost_zero_affine k t [] hrb hleg rfl w hw, fun y z => by simp⟩
  | append_singleton ds h ih =>
    have ⟨hrb_ds, hg_rb⟩ := readsBackList_of_snoc hrb
    have hleg_ds : ∀ g ∈ ds, isLegalGate g := fun g hg => hleg g (List.mem_append_left _ hg)
    have hleg_h : isLegalGate h := hleg h (List.mem_append_right _ (List.mem_singleton_self h))
    rw [gateListCost_append] at hcost
    by_cases hch : gateListCost [h] = 0
    · rcases ih hrb_ds hleg_ds (by omega) with ⟨u, v, hu, hv, hprev⟩
      refine ⟨u, v, hu, hv, ?_⟩
      intro w hw
      rw [List.length_append, List.length_singleton] at hw
      by_cases hlt : w < k + t + ds.length
      · rcases hprev w hlt with ⟨fw, cw, hfw, heq⟩
        refine ⟨fw, cw, hfw, fun y z => ?_⟩
        rw [foldl_step_append_getD_lt ds [h] _ (by rw [List.length_append, bits_length, bits_length]; exact hlt)]
        exact heq y z
      · have hweq : w = k + t + ds.length := by omega
        subst hweq
        rcases hleg_h with ⟨hlen_le, hop⟩
        match hins : h.inputs with
        | [] =>
          refine ⟨fun _ _ => b2f (h.op.eval []), 0, affFun_const _, fun y z => ?_⟩
          have hidx : k + t + ds.length = (bits k y ++ bits t z).length + ds.length := by
            rw [List.length_append, bits_length, bits_length]
          rw [hidx, foldl_step_snoc_val, hins]
          simp
        | [w1] =>
          have hw1 : w1 < k + t + ds.length := hg_rb w1 (by simp [hins])
          rcases hprev w1 hw1 with ⟨f1, c1, hf1, heq1⟩
          rcases hop with hand | hor | hmod | ⟨hnot, _⟩
          · refine ⟨f1, c1, hf1, fun y z => ?_⟩
            have hidx : k + t + ds.length = (bits k y ++ bits t z).length + ds.length := by
              rw [List.length_append, bits_length, bits_length]
            rw [hidx, foldl_step_snoc_val, hins, hand]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact heq1 y z
          · refine ⟨f1, c1, hf1, fun y z => ?_⟩
            have hidx : k + t + ds.length = (bits k y ++ bits t z).length + ds.length := by
              rw [List.length_append, bits_length, bits_length]
            rw [hidx, foldl_step_snoc_val, hins, hor]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact heq1 y z
          · refine ⟨fun y z => f1 y z + 1, c1, affFun_add_const hf1 1, fun y z => ?_⟩
            have hidx : k + t + ds.length = (bits k y ++ bits t z).length + ds.length := by
              rw [List.length_append, bits_length, bits_length]
            rw [hidx, foldl_step_snoc_val, hins, hmod]
            simp only [List.map_cons, List.map_nil]
            rw [b2f_mod2_one, heq1 y z]
            ring
          · refine ⟨fun y z => f1 y z + 1, c1, affFun_add_const hf1 1, fun y z => ?_⟩
            have hidx : k + t + ds.length = (bits k y ++ bits t z).length + ds.length := by
              rw [List.length_append, bits_length, bits_length]
            rw [hidx, foldl_step_snoc_val, hins, hnot]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2f_not, heq1 y z]
            ring
        | [w1, w2] =>
          have hw1 : w1 < k + t + ds.length := hg_rb w1 (by simp [hins])
          have hw2 : w2 < k + t + ds.length := hg_rb w2 (by simp [hins])
          rcases hop with hand | hor | hmod | ⟨_, hnotlen⟩
          · have h1 : gateListCost [h] = 1 := by
              rw [gateListCost_singleton, isCostGate_of_binary ⟨Or.inl hand, by simp [hins]⟩]; rfl
            omega
          · have h1 : gateListCost [h] = 1 := by
              rw [gateListCost_singleton, isCostGate_of_binary ⟨Or.inr hor, by simp [hins]⟩]; rfl
            omega
          · rcases hprev w1 hw1 with ⟨f1, c1, hf1, heq1⟩
            rcases hprev w2 hw2 with ⟨f2, c2, hf2, heq2⟩
            refine ⟨fun y z => f1 y z + f2 y z + 1, c1 + c2,
              affFun_add_const (affFun_add hf1 hf2) 1, fun y z => ?_⟩
            have hidx : k + t + ds.length = (bits k y ++ bits t z).length + ds.length := by
              rw [List.length_append, bits_length, bits_length]
            rw [hidx, foldl_step_snoc_val, hins, hmod]
            simp only [List.map_cons, List.map_nil]
            rw [b2f_mod2_two, heq1 y z, heq2 y z]
            ring
          · simp [hins] at hnotlen
        | _ :: _ :: _ :: _ =>
          simp [hins] at hlen_le
    · have hcost_ds : gateListCost ds = 0 := by
        have hch1 : gateListCost [h] ≤ 1 := by
          simp only [gateListCost, List.countP_cons, List.countP_nil]
          split_ifs <;> omega
        omega
      have haff_ds := cost_zero_affine k t ds hrb_ds hleg_ds hcost_ds
      rcases hleg_h with ⟨hlen_le, hop⟩
      have hbin : (h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2 := by
        by_contra hnb
        have : gateListCost [h] = 0 := by rw [gateListCost_singleton, isCostGate_of_not_binary hnb]; rfl
        exact hch this
      match hins : h.inputs with
      | [w1, w2] =>
        have hw1 : w1 < k + t + ds.length := hg_rb w1 (by simp [hins])
        have hw2 : w2 < k + t + ds.length := hg_rb w2 (by simp [hins])
        let u : (Fin k → F) → (Fin t → F) → F :=
          fun y z => b2f ((ds.foldl stepWires (bits k y ++ bits t z)).getD w1 false)
        let v : (Fin k → F) → (Fin t → F) → F :=
          fun y z => b2f ((ds.foldl stepWires (bits k y ++ bits t z)).getD w2 false)
        refine ⟨u, v, haff_ds w1 hw1, haff_ds w2 hw2, ?_⟩
        intro w hw
        rw [List.length_append, List.length_singleton] at hw
        by_cases hlt : w < k + t + ds.length
        · refine ⟨fun y z => b2f ((ds.foldl stepWires (bits k y ++ bits t z)).getD w false), 0,
            haff_ds w hlt, fun y z => ?_⟩
          rw [foldl_step_append_getD_lt ds [h] _ (by rw [List.length_append, bits_length, bits_length]; exact hlt)]
          simp
        · have hweq : w = k + t + ds.length := by omega
          subst hweq
          rcases hbin.1 with hand | hor
          · refine ⟨fun _ _ => 0, 1, affFun_const 0, fun y z => ?_⟩
            have hidx : k + t + ds.length = (bits k y ++ bits t z).length + ds.length := by
              rw [List.length_append, bits_length, bits_length]
            rw [hidx, foldl_step_snoc_val, hins, hand]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, b2f_and]
            simp [u, v]
          · refine ⟨fun y z => u y z + v y z, 1, affFun_add (haff_ds w1 hw1) (haff_ds w2 hw2), fun y z => ?_⟩
            have hidx : k + t + ds.length = (bits k y ++ bits t z).length + ds.length := by
              rw [List.length_append, bits_length, bits_length]
            rw [hidx, foldl_step_snoc_val, hins, hor]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, b2f_or]
            simp [u, v]
      | [] => simp [hins] at hbin
      | [_] => simp [hins] at hbin
      | _ :: _ :: _ :: _ => simp [hins] at hbin

def xorInputChain {n : ℕ} (startIdx : ℕ) (vec : Fin n → F) (baseLen acc0 : ℕ) :
    (i : ℕ) → i ≤ n → List Gate × ℕ
  | 0, _ => ([], acc0)
  | i + 1, hi =>
    let res := xorInputChain startIdx vec baseLen acc0 i (Nat.le_of_succ_le hi)
    let gs := res.1
    let acc := res.2
    let cur := baseLen + gs.length
    if vec ⟨i, hi⟩ = 1 then
      (gs ++ [Gate.mk (.mod 2) [acc, startIdx + i], Gate.mk .not [cur]], cur + 1)
    else
      (gs, acc)

lemma xorInputChain_props {m n : ℕ} (ds : List Gate) (startIdx : ℕ) (hstart : startIdx + n ≤ m)
    (vec : Fin n → F) (acc0 : ℕ) (hrb : readsBackList m ds) (hacc0 : acc0 < m + ds.length)
    (i : ℕ) (hi : i ≤ n) :
    let res := xorInputChain startIdx vec (m + ds.length) acc0 i hi
    readsBackList m (ds ++ res.1) ∧
    (∀ h ∈ res.1, isLegalGate h) ∧
    gateListCost res.1 = 0 ∧
    res.2 < m + ds.length + res.1.length ∧
    ∀ (addr : List Bool), addr.length = m →
      b2f (((ds ++ res.1).foldl stepWires addr).getD res.2 false) =
        b2f ((ds.foldl stepWires addr).getD acc0 false) +
          ∑ j : Fin n, if j.val < i then vec j * b2f (addr.getD (startIdx + j.val) false) else 0 := by
  induction i with
  | zero =>
    refine ⟨by simpa [xorInputChain] using hrb,
      fun h hh => by simp [xorInputChain] at hh,
      by simp [xorInputChain, gateListCost],
      by simpa [xorInputChain] using hacc0, ?_⟩
    intro addr _
    simp [xorInputChain]
  | succ i ih =>
    have hi_le : i ≤ n := Nat.le_of_succ_le hi
    rcases ih hi_le with ⟨hrb_i, hleg_i, hcost_i, hacc_i, heval_i⟩
    set baseLen := m + ds.length
    set res := xorInputChain startIdx vec baseLen acc0 i hi_le
    set gs := res.1
    set acc := res.2
    set cur := baseLen + gs.length
    have hsum_step : ∀ (addr : List Bool),
        (∑ j : Fin n, if j.val < i + 1 then vec j * b2f (addr.getD (startIdx + j.val) false) else 0) =
        (∑ j : Fin n, if j.val < i then vec j * b2f (addr.getD (startIdx + j.val) false) else 0) +
          vec ⟨i, hi⟩ * b2f (addr.getD (startIdx + i) false) := by
      intro addr
      have hsplit : ∀ j : Fin n,
          (if j.val < i + 1 then vec j * b2f (addr.getD (startIdx + j.val) false) else 0) =
          (if j.val < i then vec j * b2f (addr.getD (startIdx + j.val) false) else 0) +
            (if j = ⟨i, hi⟩ then vec j * b2f (addr.getD (startIdx + j.val) false) else 0) := by
        intro j
        by_cases hji : j.val < i
        · have hlt1 : j.val < i + 1 := by omega
          have hne : j ≠ ⟨i, hi⟩ := by
            intro heq
            have hv : j.val = i := congrArg Fin.val heq
            omega
          simp [hji, hlt1, hne]
        · by_cases hjeq : j = ⟨i, hi⟩
          · subst hjeq; simp
          · have hnot1 : ¬ (j.val < i + 1) := by
              intro hlt1
              have hv : j.val = i := by omega
              exact hjeq (Fin.ext hv)
            simp [hji, hjeq, hnot1]
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib]
      simp
    rcases f_cases (vec ⟨i, hi⟩) with hv0 | hv1
    · have hres_eq : xorInputChain startIdx vec baseLen acc0 (i + 1) hi = res := by
        simp [xorInputChain, hv0, res, gs, acc, baseLen]
      dsimp only
      rw [hres_eq]
      refine ⟨hrb_i, hleg_i, hcost_i, hacc_i, fun addr haddr => ?_⟩
      rw [hsum_step addr, hv0, zero_mul, add_zero]
      exact heval_i addr haddr
    · have hres1 : (xorInputChain startIdx vec baseLen acc0 (i + 1) hi).1 =
          gs ++ [Gate.mk (.mod 2) [acc, startIdx + i], Gate.mk .not [cur]] := by
        simp [xorInputChain, hv1, res, gs, acc, cur, baseLen]
      have hres2 : (xorInputChain startIdx vec baseLen acc0 (i + 1) hi).2 = cur + 1 := by
        simp [xorInputChain, hv1, res, gs, acc, cur, baseLen]
      dsimp only
      rw [hres1, hres2]
      have hcur_eq : cur = m + (ds ++ gs).length := by
        simp only [cur, baseLen, List.length_append]; omega
      have hstep_eq : ds ++ (gs ++ [Gate.mk (.mod 2) [acc, startIdx + i], Gate.mk .not [cur]]) =
          ((ds ++ gs) ++ [Gate.mk (.mod 2) [acc, startIdx + i]]) ++ [Gate.mk .not [cur]] := by
        simp [List.append_assoc]
      have hrb1 : readsBackList m ((ds ++ gs) ++ [Gate.mk (.mod 2) [acc, startIdx + i]]) := by
        apply readsBackList_snoc hrb_i
        intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> omega
      have hrb2 : readsBackList m (((ds ++ gs) ++ [Gate.mk (.mod 2) [acc, startIdx + i]]) ++ [Gate.mk .not [cur]]) := by
        apply readsBackList_snoc hrb1
        intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        subst hu; rw [List.length_append, List.length_singleton]; omega
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hstep_eq]; exact hrb2
      · intro h hh
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hh
        rcases hh with hh | rfl | rfl
        · exact hleg_i h hh
        · exact isLegalGate_xnor acc (startIdx + i)
        · exact isLegalGate_not cur
      · rw [gateListCost_append, hcost_i, zero_add]
        have hl : [Gate.mk (.mod 2) [acc, startIdx + i], Gate.mk .not [cur]] =
            [Gate.mk (.mod 2) [acc, startIdx + i]] ++ [Gate.mk .not [cur]] := rfl
        rw [hl, gateListCost_append, cost_xnor, cost_not]
      · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · intro addr haddr
        rw [hstep_eq]
        set p0 := ds ++ gs
        set p1 := p0 ++ [Gate.mk (.mod 2) [acc, startIdx + i]]
        have hidx2 : cur + 1 = addr.length + p1.length := by
          simp only [p1, List.length_append, List.length_singleton, haddr, hcur_eq]; omega
        have hidx1 : cur = addr.length + p0.length := by rw [haddr, hcur_eq]
        rw [hidx2, foldl_step_snoc_val]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2f_not]
        rw [hidx1, foldl_step_snoc_val]
        simp only [List.map_cons, List.map_nil, b2f_mod2_two]
        have hget_in : (p0.foldl stepWires addr).getD (startIdx + i) false = addr.getD (startIdx + i) false :=
          foldl_step_getD_lt p0 addr (by rw [haddr]; omega)
        rw [hget_in, heval_i addr haddr, hsum_step addr, hv1, one_mul]
        have h11 : (1 : F) + 1 = 0 := f_add_self 1
        calc
          b2f ((ds.foldl stepWires addr).getD acc0 false) +
              (∑ j : Fin n, if j.val < i then vec j * b2f (addr.getD (startIdx + j.val) false) else 0) +
              b2f (addr.getD (startIdx + i) false) + 1 + 1
              = b2f ((ds.foldl stepWires addr).getD acc0 false) +
                ((∑ j : Fin n, if j.val < i then vec j * b2f (addr.getD (startIdx + j.val) false) else 0) +
                b2f (addr.getD (startIdx + i) false)) + (1 + 1) := by ring
          _ = _ := by rw [h11, add_zero]

lemma append_aff_wire {k t : ℕ} (ds : List Gate)
    (hrb : readsBackList (k + t) ds) (hleg : ∀ h ∈ ds, isLegalGate h)
    (f : (Fin k → F) → (Fin t → F) → F) (haff : affFun f) :
    ∃ (ds' : List Gate) (w : ℕ),
      readsBackList (k + t) (ds ++ ds') ∧
      (∀ h ∈ ds', isLegalGate h) ∧
      gateListCost ds' = 0 ∧
      w < k + t + (ds ++ ds').length ∧
      ∀ (y : Fin k → F) (z : Fin t → F),
        b2f (((ds ++ ds').foldl stepWires (bits k y ++ bits t z)).getD w false) = f y z := by
  rcases haff with ⟨a, b, c, hf⟩
  set g0 : Gate := if c = 1 then const1Gate else const0Gate
  have hg0_leg : isLegalGate g0 := by
    by_cases hc : c = 1
    · simpa [g0, hc] using isLegalGate_const1
    · simpa [g0, hc] using isLegalGate_const0
  have hg0_cost : gateListCost [g0] = 0 := by
    by_cases hc : c = 1
    · simp only [g0, hc, ↓reduceIte, cost_const1]
    · simp only [g0, hc, ↓reduceIte, cost_const0]
  have hds0_rb : readsBackList (k + t) (ds ++ [g0]) := by
    apply readsBackList_snoc hrb
    intro i hi; by_cases hc : c = 1 <;> simp [g0, hc, const0Gate, const1Gate] at hi
  set w0 : ℕ := k + t + ds.length
  have hw0_lt : w0 < k + t + (ds ++ [g0]).length := by
    simp only [w0, List.length_append, List.length_singleton]; omega
  rcases xorInputChain_props (ds ++ [g0]) 0 (by omega : 0 + k ≤ k + t) a w0 hds0_rb hw0_lt k (le_refl k) with
    ⟨hrb1, hleg1, hcost1, hw1_lt, heval1⟩
  set res1 := xorInputChain 0 a (k + t + (ds ++ [g0]).length) w0 k (le_refl k)
  have hw1_lt' : res1.2 < k + t + ((ds ++ [g0]) ++ res1.1).length := by
    rw [List.length_append]; omega
  rcases xorInputChain_props ((ds ++ [g0]) ++ res1.1) k (by omega : k + t ≤ k + t) b res1.2 hrb1 hw1_lt' t (le_refl t) with
    ⟨hrb2, hleg2, hcost2, hw2_lt, heval2⟩
  set res2 := xorInputChain k b (k + t + ((ds ++ [g0]) ++ res1.1).length) res1.2 t (le_refl t)
  set ds' : List Gate := [g0] ++ res1.1 ++ res2.1
  have happ : ds ++ ds' = ((ds ++ [g0]) ++ res1.1) ++ res2.1 := by simp [ds', List.append_assoc]
  refine ⟨ds', res2.2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [happ]; exact hrb2
  · intro h hh
    simp only [ds', List.mem_append, List.mem_singleton] at hh
    rcases hh with (rfl | hh) | hh
    · exact hg0_leg
    · exact hleg1 h hh
    · exact hleg2 h hh
  · simp only [ds', gateListCost_append, hg0_cost, hcost1, hcost2]
  · rw [happ, List.length_append]; omega
  · intro y z
    rw [happ]
    set addr := bits k y ++ bits t z
    have haddr_len : addr.length = k + t := by simp [addr, bits_length]
    rw [heval2 addr haddr_len, heval1 addr haddr_len]
    have hg0_val : b2f (((ds ++ [g0]).foldl stepWires addr).getD w0 false) = c := by
      have hidx : w0 = addr.length + ds.length := by rw [haddr_len]
      rw [hidx, foldl_step_snoc_val]
      rcases f_cases c with rfl | rfl
      · simp [g0, const0Gate, GateOp.eval, b2f]
      · simp [g0, const1Gate, GateOp.eval, b2f]
    rw [hg0_val, hf y z]
    have hsum1 : (∑ j : Fin k, if j.val < k then a j * b2f (addr.getD (0 + j.val) false) else 0) = dotProduct a y := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [j.isLt, ↓reduceIte, zero_add]
      have hget : b2f (addr.getD j.val false) = y j := by
        simp only [addr, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by rw [bits_length]; exact j.isLt)]
        rw [← List.getD_eq_getElem?_getD, bits_getD k y j.val j.isLt, b2f_decide_eq_one]
      rw [hget]
    have hsum2 : (∑ j : Fin t, if j.val < t then b j * b2f (addr.getD (k + j.val) false) else 0) = dotProduct b z := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [j.isLt, ↓reduceIte]
      have hget : b2f (addr.getD (k + j.val) false) = z j := by
        simp only [addr, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by rw [bits_length]; omega)]
        rw [bits_length, Nat.add_sub_cancel_left]
        rw [← List.getD_eq_getElem?_getD, bits_getD t z j.val j.isLt, b2f_decide_eq_one]
      rw [hget]
    rw [hsum1, hsum2]

lemma append_aff_plus_mul {k t : ℕ} (ds : List Gate) (wuv : ℕ)
    (hrb : readsBackList (k + t) ds) (hleg : ∀ h ∈ ds, isLegalGate h)
    (hwuv : wuv < k + t + ds.length)
    (uv : (Fin k → F) → (Fin t → F) → F)
    (huv_eval : ∀ y z, b2f ((ds.foldl stepWires (bits k y ++ bits t z)).getD wuv false) = uv y z)
    (f : (Fin k → F) → (Fin t → F) → F) (haff : affFun f) (coef : F) :
    ∃ (ds' : List Gate) (w : ℕ),
      readsBackList (k + t) (ds ++ ds') ∧
      (∀ h ∈ ds', isLegalGate h) ∧
      gateListCost ds' = 0 ∧
      w < k + t + (ds ++ ds').length ∧
      ∀ (y : Fin k → F) (z : Fin t → F),
        b2f (((ds ++ ds').foldl stepWires (bits k y ++ bits t z)).getD w false) =
          f y z + coef * uv y z := by
  rcases append_aff_wire ds hrb hleg f haff with ⟨ds1, wf, hrb1, hleg1, hcost1, hwf_lt, heval1⟩
  rcases f_cases coef with rfl | rfl
  · refine ⟨ds1, wf, hrb1, hleg1, hcost1, hwf_lt, fun y z => by rw [heval1 y z]; simp⟩
  · set cur := k + t + (ds ++ ds1).length
    have hwuv1 : wuv < cur := by simp only [cur, List.length_append]; omega
    set g1 : Gate := Gate.mk (.mod 2) [wf, wuv]
    set g2 : Gate := Gate.mk .not [cur]
    have hrb2 : readsBackList (k + t) ((ds ++ ds1) ++ [g1]) := by
      apply readsBackList_snoc hrb1
      intro u hu; simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> omega
    have hrb3 : readsBackList (k + t) (((ds ++ ds1) ++ [g1]) ++ [g2]) := by
      apply readsBackList_snoc hrb2
      intro u hu; simp only [g2, List.mem_cons, List.not_mem_nil, or_false] at hu
      subst hu; rw [List.length_append, List.length_singleton]; omega
    have happ : ds ++ (ds1 ++ [g1, g2]) = ((ds ++ ds1) ++ [g1]) ++ [g2] := by simp [List.append_assoc]
    refine ⟨ds1 ++ [g1, g2], cur + 1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [happ]; exact hrb3
    · intro h hh
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with hh | rfl | rfl
      · exact hleg1 h hh
      · exact isLegalGate_xnor wf wuv
      · exact isLegalGate_not cur
    · rw [gateListCost_append, hcost1, zero_add]
      have hl : [g1, g2] = [g1] ++ [g2] := rfl
      rw [hl, gateListCost_append, cost_xnor, cost_not]
    · rw [happ, List.length_append, List.length_append, List.length_singleton, List.length_singleton]; omega
    · intro y z
      rw [happ]
      set addr := bits k y ++ bits t z
      have haddr_len : addr.length = k + t := by simp [addr, bits_length]
      have hidx2 : cur + 1 = addr.length + ((ds ++ ds1) ++ [g1]).length := by
        simp only [cur, haddr_len, List.length_append, List.length_singleton]; omega
      have hidx1 : cur = addr.length + (ds ++ ds1).length := by rw [haddr_len]
      rw [hidx2, foldl_step_snoc_val]
      simp only [g2, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, b2f_not]
      rw [hidx1, foldl_step_snoc_val]
      simp only [g1, List.map_cons, List.map_nil, b2f_mod2_two]
      have hwuv_old : ((ds ++ ds1).foldl stepWires addr).getD wuv false = (ds.foldl stepWires addr).getD wuv false :=
        foldl_step_append_getD_lt ds ds1 addr (by rw [haddr_len]; exact hwuv)
      rw [heval1 y z, hwuv_old, huv_eval y z, one_mul]
      have h11 : (1 : F) + 1 = 0 := f_add_self 1
      calc
        f y z + uv y z + 1 + 1 = f y z + uv y z + (1 + 1) := by ring
        _ = f y z + uv y z := by rw [h11, add_zero]

lemma build_taps {k t : ℕ} (ds : List Gate) (wuv : ℕ)
    (hrb : readsBackList (k + t) ds) (hleg : ∀ h ∈ ds, isLegalGate h)
    (hwuv : wuv < k + t + ds.length)
    (uv : (Fin k → F) → (Fin t → F) → F)
    (huv_eval : ∀ y z, b2f ((ds.foldl stepWires (bits k y ++ bits t z)).getD wuv false) = uv y z)
    (p : Fin k → (Fin k → F) → (Fin t → F) → F) (hp : ∀ i, affFun (p i)) (a : Fin k → F)
    (m : ℕ) (hm : m ≤ k) :
    ∃ (ds' : List Gate) (tap : Fin k → ℕ),
      readsBackList (k + t) (ds ++ ds') ∧
      (∀ h ∈ ds', isLegalGate h) ∧
      gateListCost ds' = 0 ∧
      (∀ i : Fin k, i.val < m → tap i < k + t + (ds ++ ds').length) ∧
      (∀ i : Fin k, i.val < m → ∀ y z,
        b2f (((ds ++ ds').foldl stepWires (bits k y ++ bits t z)).getD (tap i) false) =
          p i y z + a i * uv y z) := by
  induction m with
  | zero =>
    refine ⟨[], fun _ => 0, by simpa using hrb, fun _ hh => by simp at hh, rfl,
      fun _ hi => by omega, fun _ hi => by omega⟩
  | succ m ih =>
    rcases ih (Nat.le_of_succ_le hm) with ⟨ds1, tap1, hrb1, hleg1, hcost1, hlt1, heval1⟩
    have hwuv1 : wuv < k + t + (ds ++ ds1).length := by rw [List.length_append]; omega
    have huv1 : ∀ y z, b2f (((ds ++ ds1).foldl stepWires (bits k y ++ bits t z)).getD wuv false) = uv y z := by
      intro y z
      rw [foldl_step_append_getD_lt ds ds1 _ (by rw [List.length_append, bits_length, bits_length]; exact hwuv)]
      exact huv_eval y z
    have hleg_all1 : ∀ h ∈ ds ++ ds1, isLegalGate h := by
      intro h hh; rw [List.mem_append] at hh; rcases hh with hh | hh; exact hleg h hh; exact hleg1 h hh
    rcases append_aff_plus_mul (ds ++ ds1) wuv hrb1 hleg_all1 hwuv1 uv huv1 (p ⟨m, hm⟩) (hp ⟨m, hm⟩) (a ⟨m, hm⟩) with
      ⟨ds2, wm, hrb2, hleg2, hcost2, hwm_lt, hevalm⟩
    have happ : ds ++ (ds1 ++ ds2) = (ds ++ ds1) ++ ds2 := by simp [List.append_assoc]
    refine ⟨ds1 ++ ds2, fun i => if i = ⟨m, hm⟩ then wm else tap1 i, ?_, ?_, ?_, ?_, ?_⟩
    · rw [happ]; exact hrb2
    · intro h hh; rw [List.mem_append] at hh; rcases hh with hh | hh; exact hleg1 h hh; exact hleg2 h hh
    · rw [gateListCost_append, hcost1, hcost2]
    · intro i hi
      rw [happ]
      by_cases him : i = ⟨m, hm⟩
      · simp only [him, ↓reduceIte]; exact hwm_lt
      · simp only [him, ↓reduceIte]
        have hltm : i.val < m := by
          have : i.val ≠ m := fun h => him (Fin.ext h)
          omega
        have := hlt1 i hltm
        rw [List.length_append]; omega
    · intro i hi y z
      rw [happ]
      by_cases him : i = ⟨m, hm⟩
      · subst him; simp only [↓reduceIte]; exact hevalm y z
      · simp only [him, ↓reduceIte]
        have hltm : i.val < m := by
          have : i.val ≠ m := fun h => him (Fin.ext h)
          omega
        rw [foldl_step_append_getD_lt (ds ++ ds1) ds2 _ (by rw [List.length_append, bits_length, bits_length]; exact hlt1 i hltm)]
        exact heval1 i hltm y z

lemma main_29764 (k t : ℕ) (g : (Fin k → F) → (Fin t → F) → F) :
    (∃ C : Circuit,
      (ReadsBack (2 * k + t) C ∧
        (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
          (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))) ∧
      C.gates.countP (fun h => @decide ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _)) ≤ k + 1 ∧
      ∀ (x y : Fin k → F) (z : Fin t → F),
        C.eval (bits k x ++ bits k y ++ bits t z) = decide (dotProduct x y + g y z = 1)) ↔
    ∃ (f u v : (Fin k → F) → (Fin t → F) → F) (p : Fin k → (Fin k → F) → (Fin t → F) → F)
      (a : Fin k → F) (b : F),
      affFun f ∧ affFun u ∧ affFun v ∧ (∀ i, affFun (p i)) ∧
      ∀ y z, g y z = f y z + (∑ i : Fin k, y i * p i y z) +
        (b + dotProduct a y) * u y z * v y z := by
  rw [main_equiv k t g (k + 1)]
  constructor
  · rintro ⟨_, D, tap, ⟨hD_rb, hD_leg⟩, hD_cost, hD_out, hD_tap, hD_eval⟩
    have hD_cost1 : gateListCost D.gates ≤ 1 := by
      have hc : gateListCost D.gates ≤ k + 1 - k := hD_cost
      omega
    rcases cost_le_one_decomp k t D.gates hD_rb hD_leg hD_cost1 with ⟨u, v, hu, hv, hdecomp⟩
    rcases hdecomp D.output hD_out with ⟨f, b, hf, hfeq⟩
    have hp_exists : ∀ i : Fin k, ∃ (pi : (Fin k → F) → (Fin t → F) → F) (ai : F),
        affFun pi ∧ ∀ y z, b2f ((D.wires (bits k y ++ bits t z)).getD (tap i) false) = pi y z + ai * (u y z * v y z) :=
      fun i => hdecomp (tap i) (hD_tap i)
    choose p a hp hpeq using hp_exists
    refine ⟨f, u, v, p, a, b, hf, hu, hv, hp, fun y z => ?_⟩
    have hg := hD_eval y z
    dsimp only at hg
    have hD_eval_eq : b2f (D.eval (bits k y ++ bits t z)) = f y z + b * (u y z * v y z) := hfeq y z
    have hdot_eq : dotProduct (fun i : Fin k => if (D.wires (bits k y ++ bits t z)).getD (tap i) false then (1 : F) else 0) y =
        (∑ i : Fin k, y i * p i y z) + dotProduct a y * (u y z * v y z) := by
      simp only [dotProduct]
      have hterm : ∀ i : Fin k,
          (if (D.wires (bits k y ++ bits t z)).getD (tap i) false then (1 : F) else 0) * y i =
          y i * p i y z + a i * y i * (u y z * v y z) := by
        intro i
        have hi : (if (D.wires (bits k y ++ bits t z)).getD (tap i) false then (1 : F) else 0) = p i y z + a i * (u y z * v y z) := hpeq i y z
        rw [hi]
        ring
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    change g y z = b2f (D.eval (bits k y ++ bits t z)) + dotProduct (fun i => if (D.wires (bits k y ++ bits t z)).getD (tap i) false then (1 : F) else 0) y at hg
    rw [hg, hD_eval_eq, hdot_eq]
    ring
  · rintro ⟨f, u, v, p, a, b, hf, hu, hv, hp, hg⟩
    rcases append_aff_wire ([] : List Gate) (readsBackList_nil (k + t)) (fun _ hh => by simp at hh) u hu with
      ⟨ds1, wu, hrb1, hleg1, hcost1, hwu_lt, heval_u⟩
    simp only [List.nil_append] at hrb1 hwu_lt heval_u
    rcases append_aff_wire ds1 hrb1 hleg1 v hv with
      ⟨ds2, wv, hrb2, hleg2, hcost2, hwv_lt, heval_v⟩
    set ds12 := ds1 ++ ds2
    have hleg12 : ∀ h ∈ ds12, isLegalGate h := by
      intro h hh; rw [List.mem_append] at hh; rcases hh with hh | hh; exact hleg1 h hh; exact hleg2 h hh
    have hwu12 : wu < k + t + ds12.length := by simp only [ds12, List.length_append]; omega
    set wuv := k + t + ds12.length
    set ds_uv := ds12 ++ [Gate.mk .and [wu, wv]]
    have hrb_uv : readsBackList (k + t) ds_uv := by
      apply readsBackList_snoc hrb2
      intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hwu12
      · exact hwv_lt
    have hleg_uv : ∀ h ∈ ds_uv, isLegalGate h := by
      intro h hh
      simp only [ds_uv, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with hh | rfl
      · exact hleg12 h hh
      · exact isLegalGate_and2 wu wv
    have hcost_uv : gateListCost ds_uv = 1 := by
      simp only [ds_uv, ds12, gateListCost_append, hcost1, hcost2, cost_and2]
    have hwuv_lt : wuv < k + t + ds_uv.length := by
      simp only [wuv, ds_uv, List.length_append, List.length_singleton]; omega
    have huv_eval : ∀ y z, b2f ((ds_uv.foldl stepWires (bits k y ++ bits t z)).getD wuv false) = u y z * v y z := by
      intro y z
      have hidx : wuv = (bits k y ++ bits t z).length + ds12.length := by
        simp only [wuv, List.length_append, bits_length]
      rw [hidx, foldl_step_snoc_val]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, b2f_and]
      have hu' : (ds12.foldl stepWires (bits k y ++ bits t z)).getD wu false =
          (ds1.foldl stepWires (bits k y ++ bits t z)).getD wu false :=
        foldl_step_append_getD_lt ds1 ds2 _ (by rw [List.length_append, bits_length, bits_length]; exact hwu_lt)
      rw [hu', heval_u y z, heval_v y z]
    rcases append_aff_plus_mul ds_uv wuv hrb_uv hleg_uv hwuv_lt (fun y z => u y z * v y z) huv_eval f hf b with
      ⟨ds3, wout, hrb3, hleg3, hcost3, hwout_lt, heval_out⟩
    have hleg_uv3 : ∀ h ∈ ds_uv ++ ds3, isLegalGate h := by
      intro h hh; rw [List.mem_append] at hh; rcases hh with hh | hh; exact hleg_uv h hh; exact hleg3 h hh
    have hwuv3 : wuv < k + t + (ds_uv ++ ds3).length := by rw [List.length_append]; omega
    have huv3 : ∀ y z, b2f (((ds_uv ++ ds3).foldl stepWires (bits k y ++ bits t z)).getD wuv false) = u y z * v y z := by
      intro y z
      rw [foldl_step_append_getD_lt ds_uv ds3 _ (by rw [List.length_append, bits_length, bits_length]; exact hwuv_lt)]
      exact huv_eval y z
    rcases build_taps (ds_uv ++ ds3) wuv hrb3 hleg_uv3 hwuv3 (fun y z => u y z * v y z) huv3 p hp a k (le_refl k) with
      ⟨ds4, tap, hrb4, hleg4, hcost4, htap_lt, heval_tap⟩
    let D : Circuit := ⟨(ds_uv ++ ds3) ++ ds4, wout⟩
    refine ⟨by omega, D, tap, ⟨hrb4, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro h hh
      simp only [D, List.mem_append] at hh
      rcases hh with (hh | hh) | hh
      · exact hleg_uv h hh
      · exact hleg3 h hh
      · exact hleg4 h hh
    · show gateListCost ((ds_uv ++ ds3) ++ ds4) ≤ k + 1 - k
      rw [gateListCost_append, gateListCost_append, hcost_uv, hcost3, hcost4]
      omega
    · have h1 := hwout_lt
      simp only [D, Circuit.size, List.length_append] at h1 ⊢
      omega
    · intro i; exact htap_lt i i.isLt
    · intro y z inp p'
      have hout_val : b2f (D.eval inp) = f y z + b * (u y z * v y z) := by
        simp only [D, Circuit.eval, wires_eq_foldl, inp]
        rw [foldl_step_append_getD_lt (ds_uv ++ ds3) ds4 _ (by rw [List.length_append, bits_length, bits_length]; exact hwout_lt)]
        exact heval_out y z
      have hp_val : ∀ i : Fin k, p' i = p i y z + a i * (u y z * v y z) := by
        intro i
        exact heval_tap i i.isLt y z
      have hdot : dotProduct p' y = (∑ i : Fin k, y i * p i y z) + dotProduct a y * (u y z * v y z) := by
        simp only [dotProduct]
        have hterm : ∀ i : Fin k, p' i * y i = y i * p i y z + a i * y i * (u y z * v y z) := by
          intro i; rw [hp_val i]; ring
        simp_rw [hterm]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [hg y z]
      change f y z + (∑ i : Fin k, y i * p i y z) + (b + dotProduct a y) * u y z * v y z =
        b2f (D.eval inp) + dotProduct p' y
      rw [hout_val, hdot]
      ring

end PEqualNP.Outside.L_meta_29764_aux

theorem PEqualNP.Outside.L_meta_29764 :
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
  let fits := fun (g : V → Z → F) (s : ℕ) =>
    ∃ C : Circ, legal (2*k+t) C ∧ cost C ≤ s ∧
      ∀ (x y : V) (z : Z), C.eval (bits k x ++ bits k y ++ bits t z) =
        decide (dotProduct x y + g y z = 1)
  let aff := fun (f : V → Z → F) =>
    ∃ (a : V) (b : Z) (c : F), ∀ y z, f y z = c + dotProduct a y + dotProduct b z
  ∀ g : V → Z → F, fits g (k+1) ↔
    ∃ (f u v : V → Z → F) (p : Fin k → V → Z → F) (a : V) (b : F),
      aff f ∧ aff u ∧ aff v ∧ (∀ i, aff (p i)) ∧
      ∀ y z, g y z = f y z + (∑ i : Fin k, y i * p i y z) +
        (b + dotProduct a y) * u y z * v y z
:= fun k t g => PEqualNP.Outside.L_meta_29764_aux.main_29764 k t g
