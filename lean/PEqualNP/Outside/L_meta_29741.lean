import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29741_aux

open PEqualNP.CircuitLowerBounds

/-! ## Running gate lists -/

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl stp w

theorem run_append (g1 g2 : List Gate) (w : List Bool) :
    run (g1 ++ g2) w = run g2 (run g1 w) := by
  unfold run; rw [List.foldl_append]

theorem run_length (gs : List Gate) : ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [run]
  | cons g gs ih =>
    intro w
    show (run gs (stp w g)).length = _
    rw [ih]; simp [stp]; omega

theorem run_getD_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (run gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    show (run gs (stp w g)).getD i false = _
    rw [ih _ _ (by simp [stp]; omega)]
    simp only [stp]
    rw [List.getD_append _ _ _ _ hi]

theorem getD_snoc (l : List Bool) (b : Bool) (n : ℕ) :
    (l ++ [b]).getD n false = if n = l.length then b else l.getD n false := by
  split_ifs with h
  · subst h; rw [List.getD_append_right _ _ _ _ le_rfl]; simp
  · rcases Nat.lt_or_ge n l.length with h' | h'
    · rw [List.getD_append _ _ _ _ h']
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ h']

theorem run_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ (gs[j]).inputs, i < w.length + j) :
    (run gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (run gs w).getD i false) := by
  have hlen : (gs.take j).length = j := by simp; omega
  have hsplit : gs = gs.take j ++ (gs[j] :: gs.drop (j+1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hW1len : (run (gs.take j) w).length = w.length + j := by rw [run_length, hlen]
  have hrun : run gs w = run (gs.drop (j+1)) (stp (run (gs.take j) w) gs[j]) := by
    conv_lhs => rw [hsplit]
    rw [run_append]; rfl
  have hpres : ∀ i < (run (gs.take j) w).length,
      (run gs w).getD i false = (run (gs.take j) w).getD i false := by
    intro i hi
    rw [hrun, run_getD_lt _ _ _ (by simp [stp]; omega)]
    simp only [stp]; rw [List.getD_append _ _ _ _ hi]
  have hmap : (gs[j]).inputs.map (fun i => (run gs w).getD i false) =
      (gs[j]).inputs.map (fun i => (run (gs.take j) w).getD i false) := by
    apply List.map_congr_left; intro i hi; exact hpres i (by rw [hW1len]; exact hrb i hi)
  rw [hmap, hrun, run_getD_lt _ _ _ (by simp [stp]; omega)]
  simp only [stp]
  rw [getD_snoc, if_pos hW1len.symm]

/-! ## Gate predicates -/

noncomputable def counted (g : Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

def legalG (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
    (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

theorem eval_mod2_two (p q : Bool) : GateOp.eval (.mod 2) [p, q] = !(xor p q) := by
  cases p <;> cases q <;> rfl

theorem eval_mod2_one (p : Bool) : GateOp.eval (.mod 2) [p] = !p := by
  cases p <;> rfl

theorem eval_and_two (p q : Bool) : GateOp.eval .and [p, q] = (p && q) := by
  cases p <;> cases q <;> rfl

theorem eval_or_two (p q : Bool) : GateOp.eval .or [p, q] = (p || q) := by
  cases p <;> cases q <;> rfl

/-! ## The half lemma -/

theorem add_add_self {k : ℕ} (x d : Fin k → ZMod 2) : x + d + d = x := by
  funext l
  simp only [Pi.add_apply]
  generalize x l = a; generalize d l = b
  revert a b; decide

theorem half_card {k : ℕ} (Q : Finset (Fin k → ZMod 2)) (d : Fin k → ZMod 2)
    (P : (Fin k → ZMod 2) → Prop) [DecidablePred P]
    (hQ : ∀ x ∈ Q, x + d ∈ Q) (hP : ∀ x ∈ Q, (P (x + d) ↔ ¬ P x)) :
    2 * (Q.filter P).card = Q.card := by
  have h1 : (Q.filter P).card = (Q.filter (fun x => ¬ P x)).card := by
    apply Finset.card_bij' (fun x _ => x + d) (fun x _ => x + d)
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hQ x hx.1, by rw [hP x hx.1]; exact not_not.mpr hx.2⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      refine ⟨hQ x hx.1, ?_⟩
      have := hP x hx.1
      tauto
    · intro x _; exact add_add_self x d
    · intro x _; exact add_add_self x d
  have h2 := Finset.card_filter_add_card_filter_not (s := Q) P
  omega

/-! ## Separation (duality) -/

theorem sep {k : ℕ} (D : Submodule (ZMod 2) (Fin k → ZMod 2)) (u : Fin k → ZMod 2) (hu : u ∉ D) :
    ∃ d : Fin k → ZMod 2, (∀ δ ∈ D, δ ⬝ᵥ d = 0) ∧ u ⬝ᵥ d ≠ 0 := by
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hu inferInstance
  have key : ∀ z : Fin k → ZMod 2,
      z ⬝ᵥ (fun i => f (fun j => if i = j then 1 else 0)) = f z := by
    intro z
    rw [LinearMap.pi_apply_eq_sum_univ f z]
    simp [dotProduct, smul_eq_mul]
  refine ⟨fun i => f (fun j => if i = j then 1 else 0), ?_, ?_⟩
  · intro δ hδ
    rw [key]
    have : f δ ∈ D.map f := Submodule.mem_map_of_mem hδ
    rw [hmap] at this
    simpa using this
  · rw [key]; exact hf

/-! ## Small facts in `ZMod 2` -/

theorem z2_neg (a c : ZMod 2) : (!decide (a + c = 1)) = decide (a + (c + 1) = 1) := by
  revert a c; decide

theorem z2_xnor (a b c c' : ZMod 2) :
    (!(xor (decide (a + c = 1)) (decide (b + c' = 1)))) = decide (a + b + (c + c' + 1) = 1) := by
  revert a b c c'; decide

theorem z2_three (α β γ c : ZMod 2) (b : Bool) (h1 : decide (α + c = 1) = b)
    (h2 : decide (β + c = 1) = b) (h3 : decide (γ + c = 1) = b) :
    decide (α + β + γ + c = 1) = b := by
  revert h1 h2 h3; revert α β γ c b; decide

theorem z2_flip (α β γ c : ZMod 2) (h : decide (β + c = 1) ≠ decide (γ + c = 1)) :
    decide (α + (β + γ) + c = 1) = !decide (α + c = 1) := by
  revert h; revert α β γ c; decide

theorem z2_nc (α β c : ZMod 2) (h : decide (α + c = 1) = decide (α + β + c = 1)) (hb : β ≠ 0) :
    False := by
  revert h hb; revert α β c; decide

theorem z2_agree (α β γ δ c e : ZMod 2) (h : δ - β ≠ 0) :
    (decide (α + β + c = 1) = decide (γ + δ + e = 1)) ↔
      ¬ (decide (α + c = 1) = decide (γ + e = 1)) := by
  revert h; revert α β γ δ c e; decide

theorem z2_bit (x : ZMod 2) : (if decide (x = 1) = true then (1 : ZMod 2) else 0) = x := by
  revert x; decide

/-! ## Affine representations -/

def AffOn {k : ℕ} (Q : Finset (Fin k → ZMod 2)) (f : (Fin k → ZMod 2) → Bool) (r : Fin k → ZMod 2)
    (D : Submodule (ZMod 2) (Fin k → ZMod 2)) : Prop :=
  ∃ (lam : Fin k → ZMod 2) (c : ZMod 2), lam - r ∈ D ∧ ∀ x ∈ Q, f x = decide (lam ⬝ᵥ x + c = 1)

theorem AffOn.mono {k : ℕ} {Q Q' : Finset (Fin k → ZMod 2)} {f : (Fin k → ZMod 2) → Bool}
    {r : Fin k → ZMod 2} {D D' : Submodule (ZMod 2) (Fin k → ZMod 2)}
    (h : AffOn Q f r D) (hQ : Q' ⊆ Q) (hD : D ≤ D') : AffOn Q' f r D' := by
  obtain ⟨lam, c, h1, h2⟩ := h
  exact ⟨lam, c, hD h1, fun x hx => h2 x (hQ hx)⟩

theorem AffOn.congr {k : ℕ} {Q : Finset (Fin k → ZMod 2)} {f f' : (Fin k → ZMod 2) → Bool}
    {r : Fin k → ZMod 2} {D : Submodule (ZMod 2) (Fin k → ZMod 2)}
    (h : AffOn Q f' r D) (he : ∀ x ∈ Q, f x = f' x) : AffOn Q f r D := by
  obtain ⟨lam, c, h1, h2⟩ := h
  exact ⟨lam, c, h1, fun x hx => (he x hx).trans (h2 x hx)⟩

theorem AffOn.shift {k : ℕ} {Q : Finset (Fin k → ZMod 2)} {f : (Fin k → ZMod 2) → Bool}
    {r r' : Fin k → ZMod 2} {D : Submodule (ZMod 2) (Fin k → ZMod 2)}
    (h : AffOn Q f r D) (hr : r - r' ∈ D) : AffOn Q f r' D := by
  obtain ⟨lam, c, h1, h2⟩ := h
  refine ⟨lam, c, ?_, h2⟩
  have : lam - r' = (lam - r) + (r - r') := by abel
  rw [this]; exact D.add_mem h1 hr

theorem AffOn.const {k : ℕ} (Q : Finset (Fin k → ZMod 2)) (f : (Fin k → ZMod 2) → Bool)
    (r : Fin k → ZMod 2) (D : Submodule (ZMod 2) (Fin k → ZMod 2)) (b : Bool)
    (hf : ∀ x ∈ Q, f x = b) (hr : r ∈ D) : AffOn Q f r D := by
  refine ⟨0, if b then 1 else 0, by simpa using D.neg_mem hr, fun x hx => ?_⟩
  rw [hf x hx]; cases b <;> simp

theorem AffOn.neg {k : ℕ} {Q : Finset (Fin k → ZMod 2)} {f : (Fin k → ZMod 2) → Bool}
    {r : Fin k → ZMod 2} {D : Submodule (ZMod 2) (Fin k → ZMod 2)}
    (h : AffOn Q f r D) : AffOn Q (fun x => !(f x)) r D := by
  obtain ⟨lam, c, h1, h2⟩ := h
  refine ⟨lam, c + 1, h1, fun x hx => ?_⟩
  show (!(f x)) = _
  rw [h2 x hx]
  exact z2_neg _ _

theorem AffOn.xnor {k : ℕ} {Q : Finset (Fin k → ZMod 2)} {f f' : (Fin k → ZMod 2) → Bool}
    {r r' : Fin k → ZMod 2} {D : Submodule (ZMod 2) (Fin k → ZMod 2)}
    (h : AffOn Q f r D) (h' : AffOn Q f' r' D) :
    AffOn Q (fun x => !(xor (f x) (f' x))) (r + r') D := by
  obtain ⟨lam, c, h1, h2⟩ := h
  obtain ⟨lam', c', h1', h2'⟩ := h'
  refine ⟨lam + lam', c + c' + 1, ?_, fun x hx => ?_⟩
  · have : lam + lam' - (r + r') = (lam - r) + (lam' - r') := by abel
    rw [this]; exact D.add_mem h1 h1'
  · show (!(xor (f x) (f' x))) = _
    rw [h2 x hx, h2' x hx, add_dotProduct]
    exact z2_xnor _ _ _ _

/-! ## The invariant -/

def inp (k t : ℕ) (x : Fin k → ZMod 2) (a : Fin t → Bool) : List Bool :=
  List.ofFn (fun l : Fin k => decide (x l = 1)) ++ List.ofFn a

theorem inp_length (k t : ℕ) (x : Fin k → ZMod 2) (a : Fin t → Bool) :
    (inp k t x a).length = k + t := by simp [inp]

def wv (k t : ℕ) (gs : List Gate) (a : Fin t → Bool) (w : ℕ) (x : Fin k → ZMod 2) : Bool :=
  (run gs (inp k t x a)).getD w false

def Inv (k t : ℕ) (gs : List Gate) (i : ℕ) : Prop :=
  ∃ (Q : (Fin t → Bool) → (Fin i → Bool) → Finset (Fin k → ZMod 2))
    (wt : (Fin t → Bool) → (Fin i → Bool) → ℕ)
    (D : (Fin i → Bool) → Submodule (ZMod 2) (Fin k → ZMod 2))
    (r : (Fin i → Bool) → ℕ → (Fin k → ZMod 2)),
    (∀ ξ, Module.finrank (ZMod 2) (D ξ) ≤ i) ∧
    (∀ a ξ, ∀ x ∈ Q a ξ, ∀ y ∈ Q a ξ, ∀ z ∈ Q a ξ, x + y + z ∈ Q a ξ) ∧
    (∀ a ξ, ∀ x ∈ Q a ξ, ∀ d : Fin k → ZMod 2, (∀ δ ∈ D ξ, δ ⬝ᵥ d = 0) → x + d ∈ Q a ξ) ∧
    (∀ a ξ, wt a ξ * (Q a ξ).card = 2^k) ∧
    (∀ a (φ : (Fin k → ZMod 2) → ℕ), 2^i * ∑ x, φ x = ∑ ξ, wt a ξ * ∑ x ∈ Q a ξ, φ x) ∧
    (∀ a ξ w, AffOn (Q a ξ) (wv k t gs a w) (r ξ w) (D ξ))

theorem card_fun_zmod (k : ℕ) : (Finset.univ : Finset (Fin k → ZMod 2)).card = 2^k := by
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem inv_nil (k t : ℕ) : Inv k t [] 0 := by
  refine ⟨fun _ _ => Finset.univ, fun _ _ => 1, fun _ => ⊥,
    fun _ w => if h : w < k then Pi.single ⟨w, h⟩ 1 else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ; simp
  · intro a ξ x _ y _ z _; exact Finset.mem_univ _
  · intro a ξ x _ d _; exact Finset.mem_univ _
  · intro a ξ; rw [one_mul, card_fun_zmod]
  · intro a φ; simp
  · intro a ξ w
    show AffOn Finset.univ (fun x => (inp k t x a).getD w false)
      (if h : w < k then Pi.single ⟨w, h⟩ 1 else 0) ⊥
    by_cases hw : w < k
    · rw [dif_pos hw]
      refine ⟨Pi.single ⟨w, hw⟩ 1, 0, by simp, fun x _ => ?_⟩
      show (inp k t x a).getD w false = _
      rw [inp, List.getD_append _ _ _ _ (by simpa using hw)]
      simp [List.getD_eq_getElem?_getD, hw]
    · rw [dif_neg hw]
      by_cases hw2 : w < k + t
      · refine AffOn.const _ _ _ _ (a ⟨w - k, by omega⟩) (fun x _ => ?_) (Submodule.zero_mem _)
        show (inp k t x a).getD w false = _
        rw [inp, List.getD_append_right _ _ _ _ (by simp; omega)]
        simp [List.getD_eq_getElem?_getD, show w - k < t by omega]
      · refine AffOn.const _ _ _ _ false (fun x _ => ?_) (Submodule.zero_mem _)
        show (inp k t x a).getD w false = _
        rw [List.getD_eq_default _ _ (by rw [inp_length]; omega)]


theorem free_aff {k : ℕ} (g : Gate) (hl : legalG g) (hc : counted g = false)
    (Q : Finset (Fin k → ZMod 2)) (f : ℕ → (Fin k → ZMod 2) → Bool) (r : ℕ → (Fin k → ZMod 2))
    (D : Submodule (ZMod 2) (Fin k → ZMod 2)) (h : ∀ w, AffOn Q (f w) (r w) D) :
    AffOn Q (fun x => g.op.eval (g.inputs.map fun i => f i x)) (g.inputs.map r).sum D := by
  obtain ⟨hlen, hop⟩ := hl
  have hc' : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) := by
    simpa [counted] using hc
  obtain ⟨op, ins⟩ := g
  simp only at hlen hop hc' ⊢
  rcases ins with _ | ⟨p, _ | ⟨q, _ | ⟨z, rest⟩⟩⟩
  · exact AffOn.const _ _ _ _ (op.eval []) (fun x _ => rfl) (by simp)
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rcases hop with rfl | rfl | rfl | ⟨rfl, _⟩
    · exact (h p).congr (fun x _ => by simp [GateOp.eval])
    · exact (h p).congr (fun x _ => by simp [GateOp.eval])
    · exact (h p).neg.congr (fun x _ => eval_mod2_one _)
    · exact (h p).neg.congr (fun x _ => rfl)
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rcases hop with rfl | rfl | rfl | ⟨rfl, h1⟩
    · exact absurd ⟨Or.inl rfl, rfl⟩ hc'
    · exact absurd ⟨Or.inr rfl, rfl⟩ hc'
    · exact ((h p).xnor (h q)).congr (fun x _ => eval_mod2_two _ _)
    · simp at h1
  · simp at hlen

theorem run_snoc (gs : List Gate) (g : Gate) (W : List Bool) :
    run (gs ++ [g]) W = stp (run gs W) g := by
  rw [run_append]; rfl

theorem wv_snoc (k t : ℕ) (gs : List Gate) (g : Gate) (a : Fin t → Bool) (w : ℕ)
    (x : Fin k → ZMod 2) :
    wv k t (gs ++ [g]) a w x = if w = k + t + gs.length then
      g.op.eval (g.inputs.map fun i => wv k t gs a i x) else wv k t gs a w x := by
  unfold wv
  rw [run_snoc, stp, getD_snoc, run_length, inp_length]

theorem inv_free (k t : ℕ) (gs : List Gate) (g : Gate) (i : ℕ) (hl : legalG g)
    (hc : counted g = false) (hinv : Inv k t gs i) : Inv k t (gs ++ [g]) i := by
  obtain ⟨Q, wt, D, r, hD, hflat, hperp, hwt, hsum, haff⟩ := hinv
  refine ⟨Q, wt, D, fun ξ w => if w = k + t + gs.length then (g.inputs.map (r ξ)).sum else r ξ w,
    hD, hflat, hperp, hwt, hsum, ?_⟩
  intro a ξ w
  by_cases hw : w = k + t + gs.length
  · simp only [if_pos hw]
    refine (free_aff g hl hc _ (fun i x => wv k t gs a i x) _ _ (fun w => haff a ξ w)).congr ?_
    intro x _
    rw [wv_snoc, if_pos hw]
  · simp only [if_neg hw]
    refine (haff a ξ w).congr ?_
    intro x _
    rw [wv_snoc, if_neg hw]

theorem finrank_sup_span_le {k : ℕ} (D : Submodule (ZMod 2) (Fin k → ZMod 2)) (u : Fin k → ZMod 2) :
    Module.finrank (ZMod 2) ↥(D ⊔ Submodule.span (ZMod 2) {u}) ≤ Module.finrank (ZMod 2) D + 1 := by
  have h1 := Submodule.finrank_add_le_finrank_add_finrank D (Submodule.span (ZMod 2) {u})
  have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({u} : Set (Fin k → ZMod 2))) ≤ 1 := by
    have := finrank_span_le_card (R := ZMod 2) ({u} : Set (Fin k → ZMod 2))
    simpa using this
  omega

theorem sum_cons_bool {i : ℕ} (G : (Fin (i+1) → Bool) → ℕ) :
    ∑ ξ', G ξ' = ∑ ξ : Fin i → Bool, (G (Fin.cons true ξ) + G (Fin.cons false ξ)) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  rw [Fintype.sum_bool]; rfl

theorem aff_gate_split {k : ℕ} {Q Q' : Finset (Fin k → ZMod 2)} (hsub : Q' ⊆ Q)
    {D D' : Submodule (ZMod 2) (Fin k → ZMod 2)} (hDD : D ≤ D')
    (pv qv val : (Fin k → ZMod 2) → Bool) (ia pc : Bool) (rq ref : Fin k → ZMod 2)
    (hq : AffOn Q qv rq D) (hpc : ∀ x ∈ Q', pv x = pc)
    (hval : ∀ x ∈ Q', val x = if ia then (pv x && qv x) else (pv x || qv x))
    (href1 : ia = pc → rq - ref ∈ D') (href2 : ia ≠ pc → ref ∈ D') : AffOn Q' val ref D' := by
  cases ia <;> cases pc
  · exact ((hq.mono hsub hDD).shift (href1 rfl)).congr
      (fun x hx => by rw [hval x hx, hpc x hx]; simp)
  · exact AffOn.const _ _ _ _ true (fun x hx => by rw [hval x hx, hpc x hx]; simp)
      (href2 (by decide))
  · exact AffOn.const _ _ _ _ false (fun x hx => by rw [hval x hx, hpc x hx]; simp)
      (href2 (by decide))
  · exact ((hq.mono hsub hDD).shift (href1 rfl)).congr
      (fun x hx => by rw [hval x hx, hpc x hx]; simp)

theorem inv_counted (k t : ℕ) (gs : List Gate) (g : Gate) (i : ℕ) (hc : counted g = true)
    (hinv : Inv k t gs i) : Inv k t (gs ++ [g]) (i+1) := by
  classical
  obtain ⟨Q, wt, D, r, hD, hflat, hperp, hwt, hsum, haff⟩ := hinv
  have hc' : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by simpa [counted] using hc
  obtain ⟨hop, hlen⟩ := hc'
  obtain ⟨p, q, hpq⟩ : ∃ p q, g.inputs = [p, q] := by
    rcases h : g.inputs with _ | ⟨p, _ | ⟨q, _ | ⟨_, _⟩⟩⟩ <;> rw [h] at hlen <;> simp at hlen
    exact ⟨p, q, rfl⟩
  have hval : ∀ a x, wv k t (gs ++ [g]) a (k + t + gs.length) x =
      if decide (g.op = .and) then (wv k t gs a p x && wv k t gs a q x)
      else (wv k t gs a p x || wv k t gs a q x) := by
    intro a x
    rw [wv_snoc, if_pos rfl, hpq]
    rcases hop with h | h <;> simp [h, eval_and_two, eval_or_two]
  let isC : (Fin t → Bool) → (Fin i → Bool) → Prop := fun a ξ =>
    ∀ x ∈ Q a ξ, ∀ y ∈ Q a ξ, wv k t gs a p x = wv k t gs a p y
  let selD : (Fin i → Bool) → (Fin k → ZMod 2) := fun ξ => if r ξ p ∈ D ξ then r ξ q else r ξ p
  have hrp : ∀ ξ, r ξ p ∈ D ξ ⊔ Submodule.span (ZMod 2) {selD ξ} := by
    intro ξ
    by_cases h : r ξ p ∈ D ξ
    · exact Submodule.mem_sup_left h
    · apply Submodule.mem_sup_right
      simp only [selD, if_neg h]
      exact Submodule.mem_span_singleton_self _
  have hnc : ∀ a ξ, r ξ p ∉ D ξ → ¬ isC a ξ := by
    intro a ξ hA hC
    obtain ⟨lam, c, h1, h2⟩ := haff a ξ p
    have hlam : lam ∉ D ξ := by
      intro hl
      apply hA
      have : r ξ p = lam - (lam - r ξ p) := by abel
      rw [this]; exact (D ξ).sub_mem hl h1
    obtain ⟨d, hd, hld⟩ := sep (D ξ) lam hlam
    have hne : (Q a ξ).Nonempty := by
      rw [← Finset.card_pos]
      have := hwt a ξ
      by_contra h0
      push_neg at h0
      rw [Nat.le_zero.mp h0, mul_zero] at this
      exact absurd this (by positivity)
    obtain ⟨x0, hx0⟩ := hne
    have hx1 := hperp a ξ x0 hx0 d hd
    have := hC x0 hx0 _ hx1
    rw [h2 _ hx0, h2 _ hx1, dotProduct_add] at this
    exact z2_nc _ _ _ this hld
  have hsub : ∀ a (ξ' : Fin (i+1) → Bool), (if isC a (Fin.tail ξ') then Q a (Fin.tail ξ')
      else (Q a (Fin.tail ξ')).filter (fun x => wv k t gs a p x = ξ' 0)) ⊆ Q a (Fin.tail ξ') := by
    intro a ξ'
    split_ifs
    · exact subset_rfl
    · exact Finset.filter_subset _ _
  refine ⟨fun a ξ' => if isC a (Fin.tail ξ') then Q a (Fin.tail ξ')
      else (Q a (Fin.tail ξ')).filter (fun x => wv k t gs a p x = ξ' 0),
    fun a ξ' => if isC a (Fin.tail ξ') then wt a (Fin.tail ξ') else 2 * wt a (Fin.tail ξ'),
    fun ξ' => D (Fin.tail ξ') ⊔ Submodule.span (ZMod 2) {selD (Fin.tail ξ')},
    fun ξ' w => if w = k + t + gs.length then
      (if r (Fin.tail ξ') p ∈ D (Fin.tail ξ') then 0
        else if ξ' 0 = decide (g.op = .and) then r (Fin.tail ξ') q else 0)
      else r (Fin.tail ξ') w,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ'
    show Module.finrank (ZMod 2)
      ↥(D (Fin.tail ξ') ⊔ Submodule.span (ZMod 2) {selD (Fin.tail ξ')}) ≤ i + 1
    have := hD (Fin.tail ξ')
    have := finrank_sup_span_le (D (Fin.tail ξ')) (selD (Fin.tail ξ'))
    omega
  · intro a ξ' x hx y hy z hz
    by_cases hC : isC a (Fin.tail ξ')
    · simp only [hC, ↓reduceIte] at hx hy hz ⊢
      exact hflat a _ x hx y hy z hz
    · simp only [hC, ↓reduceIte, Finset.mem_filter] at hx hy hz ⊢
      obtain ⟨lam, c, -, h2⟩ := haff a (Fin.tail ξ') p
      have hm := hflat a _ x hx.1 y hy.1 z hz.1
      refine ⟨hm, ?_⟩
      have ex := hx.2; have ey := hy.2; have ez := hz.2
      rw [h2 _ hm, dotProduct_add, dotProduct_add]
      rw [h2 _ hx.1] at ex; rw [h2 _ hy.1] at ey; rw [h2 _ hz.1] at ez
      exact z2_three _ _ _ _ _ ex ey ez
  · intro a ξ' x hx d hd
    have hdD : ∀ δ ∈ D (Fin.tail ξ'), δ ⬝ᵥ d = 0 :=
      fun δ hδ => hd δ (Submodule.mem_sup_left hδ)
    by_cases hC : isC a (Fin.tail ξ')
    · simp only [hC, ↓reduceIte] at hx ⊢
      exact hperp a _ x hx d hdD
    · simp only [hC, ↓reduceIte, Finset.mem_filter] at hx ⊢
      obtain ⟨lam, c, h1, h2⟩ := haff a (Fin.tail ξ') p
      have hm := hperp a _ x hx.1 d hdD
      refine ⟨hm, ?_⟩
      have hl : lam ⬝ᵥ d = 0 := by
        have e1 : lam = (lam - r (Fin.tail ξ') p) + r (Fin.tail ξ') p := by abel
        rw [e1, add_dotProduct, hdD _ h1, hd _ (hrp _), add_zero]
      have ex := hx.2
      rw [h2 _ hx.1] at ex
      rw [h2 _ hm, dotProduct_add, hl, add_zero]
      exact ex
  · intro a ξ'
    by_cases hC : isC a (Fin.tail ξ')
    · simp only [hC, ↓reduceIte]; exact hwt a _
    · simp only [hC, ↓reduceIte]
      have hC' := hC
      simp only [isC, not_forall] at hC'
      obtain ⟨y, hy, z, hz, hyz⟩ := hC'
      obtain ⟨lam, c, -, h2⟩ := haff a (Fin.tail ξ') p
      have hflip : ∀ x ∈ Q a (Fin.tail ξ'),
          wv k t gs a p (x + (y + z)) = !(wv k t gs a p x) := by
        intro x hx
        have hm : x + (y + z) ∈ Q a (Fin.tail ξ') := by
          rw [← add_assoc]; exact hflat a _ x hx y hy z hz
        rw [h2 _ hm, h2 _ hx, dotProduct_add, dotProduct_add]
        rw [h2 _ hy, h2 _ hz] at hyz
        exact z2_flip _ _ _ _ hyz
      have hh := half_card (Q a (Fin.tail ξ')) (y + z) (fun x => wv k t gs a p x = ξ' 0)
        (fun x hx => by rw [← add_assoc]; exact hflat a _ x hx y hy z hz)
        (fun x hx => by
          simp only [hflip x hx]
          generalize wv k t gs a p x = u
          generalize ξ' 0 = b
          cases u <;> cases b <;> decide)
      rw [← hwt a (Fin.tail ξ'), ← hh]; ring
  · intro a φ
    rw [sum_cons_bool, pow_succ, mul_comm (2^i) 2, mul_assoc, hsum a φ, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    simp only [Fin.tail_cons, Fin.cons_zero]
    by_cases hC : isC a ξ
    · simp only [hC, ↓reduceIte]; ring
    · simp only [hC, ↓reduceIte]
      rw [← Finset.sum_filter_add_sum_filter_not (Q a ξ) (fun x => wv k t gs a p x = true) φ]
      have : (Q a ξ).filter (fun x => ¬ wv k t gs a p x = true) =
          (Q a ξ).filter (fun x => wv k t gs a p x = false) := by
        apply Finset.filter_congr; intro x _; simp
      rw [this]; ring
  · intro a ξ' w
    by_cases hw : w = k + t + gs.length
    · subst hw
      simp only [↓reduceIte]
      by_cases hA : r (Fin.tail ξ') p ∈ D (Fin.tail ξ')
      · simp only [hA, ↓reduceIte]
        have hrqm : r (Fin.tail ξ') q ∈
            D (Fin.tail ξ') ⊔ Submodule.span (ZMod 2) {selD (Fin.tail ξ')} := by
          apply Submodule.mem_sup_right
          simp only [selD, if_pos hA]
          exact Submodule.mem_span_singleton_self _
        by_cases hC : isC a (Fin.tail ξ')
        · by_cases hne : (Q a (Fin.tail ξ')).Nonempty
          · obtain ⟨x0, hx0⟩ := hne
            refine aff_gate_split (hsub a ξ') le_sup_left (wv k t gs a p) (wv k t gs a q) _
              (decide (g.op = .and)) (wv k t gs a p x0) _ _ (haff a _ q) ?_
              (fun x _ => hval a x) (fun _ => by simpa using hrqm) (fun _ => Submodule.zero_mem _)
            intro x hx
            simp only [hC, ↓reduceIte] at hx
            exact hC x hx x0 hx0
          · refine AffOn.const _ _ _ _ false (fun x hx => ?_) (Submodule.zero_mem _)
            simp only [hC, ↓reduceIte] at hx
            exact absurd ⟨x, hx⟩ hne
        · refine aff_gate_split (hsub a ξ') le_sup_left (wv k t gs a p) (wv k t gs a q) _
            (decide (g.op = .and)) (ξ' 0) _ _ (haff a _ q) ?_ (fun x _ => hval a x)
            (fun _ => by simpa using hrqm) (fun _ => Submodule.zero_mem _)
          intro x hx
          simp only [hC, ↓reduceIte, Finset.mem_filter] at hx
          exact hx.2
      · simp only [hA, ↓reduceIte]
        have hC := hnc a _ hA
        refine aff_gate_split (hsub a ξ') le_sup_left (wv k t gs a p) (wv k t gs a q) _
          (decide (g.op = .and)) (ξ' 0) _ _ (haff a _ q) ?_ (fun x _ => hval a x) ?_ ?_
        · intro x hx
          simp only [hC, ↓reduceIte, Finset.mem_filter] at hx
          exact hx.2
        · intro h; rw [if_pos h.symm, sub_self]; exact Submodule.zero_mem _
        · intro h; rw [if_neg (Ne.symm h)]; exact Submodule.zero_mem _
    · simp only [hw, ↓reduceIte]
      refine ((haff a (Fin.tail ξ') w).mono (hsub a ξ') le_sup_left).congr ?_
      intro x _
      rw [wv_snoc, if_neg hw]

theorem inv_all (k t : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, legalG g) :
    Inv k t gs (gs.countP counted) := by
  induction gs using List.reverseRecOn with
  | nil => exact inv_nil k t
  | append_singleton gs g ih =>
    have hg : legalG g := hgs g (by simp)
    have ih' := ih (fun g' hg' => hgs g' (by simp [hg']))
    rw [List.countP_append]
    cases hc : counted g
    · have := inv_free k t gs g _ hg hc ih'
      simpa [hc] using this
    · have := inv_counted k t gs g _ hc ih'
      simpa [hc] using this

theorem even_smul_zero {k : ℕ} (n : ℕ) (u : Fin k → ZMod 2) (hn : n % 2 = 0) : n • u = 0 := by
  funext l
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  have : (n : ZMod 2) = 0 := by rw [← ZMod.natCast_mod, hn]; simp
  rw [this, zero_mul]

theorem mask_bound {k m s : ℕ} (v : Fin m → (Fin k → ZMod 2))
    (D : Submodule (ZMod 2) (Fin k → ZMod 2))
    (r : Fin k → ZMod 2) (hD : Module.finrank (ZMod 2) D ≤ s)
    [DecidablePred (fun j => v j - r ∈ D)]
    (hyp : ∀ R : Finset (Fin m), R.Nonempty → R.card % 2 = 0 → R.card ≤ s+2 →
      (∑ j ∈ R, v j) ≠ 0) :
    (Finset.univ.filter (fun j => v j - r ∈ D)).card ≤ s + 1 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hmemT : ∀ j ∈ Finset.univ.filter (fun j => v j - r ∈ D), v j - r ∈ D :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have hTne : (Finset.univ.filter (fun j => v j - r ∈ D)).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨j0, hj0⟩ := hTne
  obtain ⟨T', hT'sub, hT'card⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ.filter (fun j => v j - r ∈ D)).erase j0) (n := s+1)
    (by rw [Finset.card_erase_of_mem hj0]; omega)
  let fam : T' → (Fin k → ZMod 2) := fun j => v j - v j0
  have hnot : ¬ LinearIndependent (ZMod 2) fam := by
    intro hli
    have h1 := finrank_span_eq_card hli
    have h2 : Submodule.span (ZMod 2) (Set.range fam) ≤ D := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have hj := Finset.mem_of_mem_erase (hT'sub j.2)
      have e : v j - v j0 = (v j - r) - (v j0 - r) := by abel
      show v j - v j0 ∈ D
      rw [e]; exact D.sub_mem (hmemT _ hj) (hmemT _ hj0)
    have h3 := Submodule.finrank_mono h2
    rw [h1, Fintype.card_coe, hT'card] at h3
    omega
  rw [Fintype.not_linearIndependent_iff] at hnot
  obtain ⟨g, hg, j1, hj1⟩ := hnot
  let R' : Finset (Fin m) :=
    (Finset.univ.filter (fun j : T' => g j ≠ 0)).map (Function.Embedding.subtype _)
  have hR'sub : R' ⊆ T' := by
    intro j hj
    simp only [R', Finset.mem_map, Finset.mem_filter, Function.Embedding.coe_subtype] at hj
    obtain ⟨j', _, rfl⟩ := hj; exact j'.2
  have hj0R : j0 ∉ R' := by
    intro h; have := hT'sub (hR'sub h); simp at this
  have hR'ne : R'.Nonempty := ⟨j1, by simp [R', hj1]⟩
  have hR'card : R'.card ≤ s + 1 := hT'card ▸ Finset.card_le_card hR'sub
  have hsum0 : ∑ j ∈ R', (v j - v j0) = 0 := by
    rw [← hg]
    simp only [R', Finset.sum_map, Function.Embedding.coe_subtype]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have : g j = 0 ∨ g j = 1 := by generalize g j = z; revert z; decide
    rcases this with h | h <;> simp [h, fam]
  rw [Finset.sum_sub_distrib, Finset.sum_const, sub_eq_zero] at hsum0
  rcases Nat.mod_two_eq_zero_or_one R'.card with he | ho
  · exact hyp R' hR'ne he (by omega) (by rw [hsum0]; exact even_smul_zero _ _ he)
  · apply hyp (insert j0 R') (Finset.insert_nonempty _ _)
      (by rw [Finset.card_insert_of_notMem hj0R]; omega)
      (by rw [Finset.card_insert_of_notMem hj0R]; omega)
    rw [Finset.sum_insert hj0R, hsum0, ← succ_nsmul']
    exact even_smul_zero _ _ (by omega)

/-! ## The lower bound -/

def agr (k t : ℕ) (C : Circuit) (a : Fin t → Bool) (vj : Fin k → ZMod 2) (ej : ZMod 2)
    (s : Finset (Fin k → ZMod 2)) : Finset (Fin k → ZMod 2) :=
  s.filter (fun x => C.eval (List.ofFn (fun l : Fin k => decide (x l = 1)) ++ List.ofFn a) =
    decide (dotProduct vj x + ej = 1))

theorem eval_eq_wv (k t : ℕ) (C : Circuit) (x : Fin k → ZMod 2) (a : Fin t → Bool) :
    C.eval (List.ofFn (fun l : Fin k => decide (x l = 1)) ++ List.ofFn a) =
      wv k t C.gates a C.output x := rfl

theorem part1_core (k t m s : ℕ) (v : Fin m → (Fin k → ZMod 2)) (addr : Fin m → (Fin t → Bool))
    (e : Fin m → ZMod 2) (w : Fin m → ℕ)
    (hyp : ∀ R : Finset (Fin m), R.Nonempty → R.card % 2 = 0 → R.card ≤ s+2 →
      (∑ j ∈ R, v j) ≠ 0)
    (C : Circuit) (i : ℕ) (hinv : Inv k t C.gates i) (hcost : i ≤ s) :
    ∃ S : Finset (Fin m), S.card ≤ s+1 ∧
      2 * (∑ j : Fin m, w j * (agr k t C (addr j) (v j) (e j) Finset.univ).card) -
        2^k * (∑ j : Fin m, w j) ≤ 2^k * (∑ j ∈ S, w j) := by
  classical
  obtain ⟨Q, wt, D, r, hD, hflat, hperp, hwt, hsum, haff⟩ := hinv
  let Sx : (Fin i → Bool) → Finset (Fin m) := fun ξ =>
    Finset.univ.filter (fun j => v j - r ξ C.output ∈ D ξ)
  obtain ⟨ξs, -, hξs⟩ := Finset.exists_max_image Finset.univ (fun ξ => ∑ j ∈ Sx ξ, w j)
    Finset.univ_nonempty
  refine ⟨Sx ξs, mask_bound v (D ξs) (r ξs C.output) (le_trans (hD ξs) hcost) hyp, ?_⟩
  have hper : ∀ j : Fin m, 2^i * (2 * (agr k t C (addr j) (v j) (e j) Finset.univ).card) ≤
      2^k * (2^i + ∑ ξ, if j ∈ Sx ξ then 1 else 0) := by
    intro j
    have h1 := hsum (addr j) (fun x =>
      if C.eval (List.ofFn (fun l : Fin k => decide (x l = 1)) ++ List.ofFn (addr j)) =
        decide (dotProduct (v j) x + e j = 1) then 1 else 0)
    simp only [← Finset.card_filter] at h1
    change 2^i * (agr k t C (addr j) (v j) (e j) Finset.univ).card =
      ∑ ξ, wt (addr j) ξ * (agr k t C (addr j) (v j) (e j) (Q (addr j) ξ)).card at h1
    have hQ : ∀ ξ, 2 * (agr k t C (addr j) (v j) (e j) (Q (addr j) ξ)).card ≤
        (Q (addr j) ξ).card * (1 + if j ∈ Sx ξ then 1 else 0) := by
      intro ξ
      by_cases hj : j ∈ Sx ξ
      · rw [if_pos hj]
        have := Finset.card_filter_le (Q (addr j) ξ) (fun x =>
          C.eval (List.ofFn (fun l : Fin k => decide (x l = 1)) ++ List.ofFn (addr j)) =
            decide (dotProduct (v j) x + e j = 1))
        unfold agr
        omega
      · rw [if_neg hj, add_zero, mul_one]
        obtain ⟨lam, c, hl1, hl2⟩ := haff (addr j) ξ C.output
        have hvl : v j - lam ∉ D ξ := by
          intro hm
          apply hj
          simp only [Sx, Finset.mem_filter, Finset.mem_univ, true_and]
          have : v j - r ξ C.output = (v j - lam) + (lam - r ξ C.output) := by abel
          rw [this]; exact (D ξ).add_mem hm hl1
        obtain ⟨d, hd, hvd⟩ := sep (D ξ) _ hvl
        apply le_of_eq
        apply half_card _ d _ (fun x hx => hperp _ _ x hx d hd)
        intro x hx
        have hx' := hperp _ _ x hx d hd
        rw [eval_eq_wv, eval_eq_wv, hl2 _ hx, hl2 _ hx', dotProduct_add, dotProduct_add]
        rw [sub_dotProduct] at hvd
        exact z2_agree _ _ _ _ _ _ hvd
    calc 2^i * (2 * (agr k t C (addr j) (v j) (e j) Finset.univ).card)
        = 2 * (2^i * (agr k t C (addr j) (v j) (e j) Finset.univ).card) := by ring
      _ = 2 * ∑ ξ, wt (addr j) ξ * (agr k t C (addr j) (v j) (e j) (Q (addr j) ξ)).card := by
          rw [h1]
      _ = ∑ ξ, wt (addr j) ξ * (2 * (agr k t C (addr j) (v j) (e j) (Q (addr j) ξ)).card) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ξ _ => by ring)
      _ ≤ ∑ ξ, wt (addr j) ξ * ((Q (addr j) ξ).card * (1 + if j ∈ Sx ξ then 1 else 0)) :=
          Finset.sum_le_sum (fun ξ _ => Nat.mul_le_mul_left _ (hQ ξ))
      _ = ∑ ξ, 2^k * (1 + if j ∈ Sx ξ then 1 else 0) := by
          refine Finset.sum_congr rfl (fun ξ _ => ?_); rw [← mul_assoc, hwt]
      _ = 2^k * (2^i + ∑ ξ, if j ∈ Sx ξ then 1 else 0) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          simp [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  have hswap : ∑ ξ, ∑ j ∈ Sx ξ, w j = ∑ j, w j * ∑ ξ, (if j ∈ Sx ξ then 1 else 0) := by
    calc ∑ ξ, ∑ j ∈ Sx ξ, w j = ∑ ξ, ∑ j, (if j ∈ Sx ξ then w j else 0) := by
          refine Finset.sum_congr rfl (fun ξ _ => ?_)
          rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = ∑ j, ∑ ξ, (if j ∈ Sx ξ then w j else 0) := Finset.sum_comm
      _ = ∑ j, w j * ∑ ξ, (if j ∈ Sx ξ then 1 else 0) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun ξ _ => by rw [mul_boole])
  have hmax : ∑ ξ, ∑ j ∈ Sx ξ, w j ≤ 2^i * ∑ j ∈ Sx ξs, w j := by
    calc ∑ ξ, ∑ j ∈ Sx ξ, w j ≤ ∑ _ξ : Fin i → Bool, ∑ j ∈ Sx ξs, w j :=
          Finset.sum_le_sum (fun ξ _ => hξs ξ (Finset.mem_univ _))
      _ = 2^i * ∑ j ∈ Sx ξs, w j := by
          simp [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  have hB : ∑ j, w j * (2^k * (2^i + ∑ ξ, if j ∈ Sx ξ then 1 else 0)) =
      2^k * 2^i * ∑ j, w j + 2^k * ∑ j, w j * ∑ ξ, (if j ∈ Sx ξ then 1 else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have htot : 2^i * (2 * ∑ j, w j * (agr k t C (addr j) (v j) (e j) Finset.univ).card) ≤
      2^i * (2^k * (∑ j, w j) + 2^k * ∑ j ∈ Sx ξs, w j) := by
    calc 2^i * (2 * ∑ j, w j * (agr k t C (addr j) (v j) (e j) Finset.univ).card)
        = ∑ j, w j * (2^i * (2 * (agr k t C (addr j) (v j) (e j) Finset.univ).card)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ ∑ j, w j * (2^k * (2^i + ∑ ξ, if j ∈ Sx ξ then 1 else 0)) :=
          Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (hper j))
      _ = 2^k * 2^i * ∑ j, w j + 2^k * ∑ ξ, ∑ j ∈ Sx ξ, w j := by rw [hB, hswap]
      _ ≤ 2^k * 2^i * ∑ j, w j + 2^k * (2^i * ∑ j ∈ Sx ξs, w j) := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_left (2^k) hmax) _
      _ = 2^i * (2^k * (∑ j, w j) + 2^k * ∑ j ∈ Sx ξs, w j) := by ring
  have h2 := Nat.le_of_mul_le_mul_left htot (by positivity)
  rw [Nat.sub_le_iff_le_add, add_comm]
  exact h2

theorem part1 (k t m s : ℕ) (v : Fin m → (Fin k → ZMod 2)) (addr : Fin m → (Fin t → Bool))
    (e : Fin m → ZMod 2) (w : Fin m → ℕ)
    (hyp : ∀ R : Finset (Fin m), R.Nonempty → R.card % 2 = 0 → R.card ≤ s+2 →
      (∑ j ∈ R, v j) ≠ 0)
    (C : Circuit) (hg : ∀ g ∈ C.gates, legalG g) (hcost : C.gates.countP counted ≤ s) :
    ∃ S : Finset (Fin m), S.card ≤ s+1 ∧
      2 * (∑ j : Fin m, w j * (agr k t C (addr j) (v j) (e j) Finset.univ).card) -
        2^k * (∑ j : Fin m, w j) ≤ 2^k * (∑ j ∈ S, w j) :=
  part1_core k t m s v addr e w hyp C _ (inv_all k t C.gates hg) hcost

/-! ## The construction -/

def b2f (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2f_xnor (p q : Bool) : b2f (!(xor p q)) = b2f p + b2f q + 1 := by
  cases p <;> cases q <;> decide

theorem b2f_not (p : Bool) : b2f (!p) = b2f p + 1 := by cases p <;> decide

theorem eq_decide_of_b2f (b : Bool) (z : ZMod 2) (h : b2f b = z) : b = decide (z = 1) := by
  subst h; cases b <;> decide

theorem eval_not_one (p : Bool) : GateOp.eval .not [p] = !p := rfl

theorem sel_lemma (y0 y1 bit : Bool) :
    (!(!(xor y0 (bit && !(!(xor y0 y1)))))) = if bit then y1 else y0 := by
  cases y0 <;> cases y1 <;> cases bit <;> rfl

def xOf (k : ℕ) (W : List Bool) : Fin k → ZMod 2 := fun l => b2f (W.getD l false)

def aOf (k t : ℕ) (W : List Bool) : Fin t → Bool := fun l => W.getD (k + l) false

def Consistent (gs : List Gate) (o : ℕ) (Wf : List Bool) : Prop :=
  ∀ j (hj : j < gs.length), Wf.getD (o + j) false =
    (gs[j]).op.eval ((gs[j]).inputs.map fun i => Wf.getD i false)

def ReadsFrom (gs : List Gate) (o : ℕ) : Prop :=
  ∀ j (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < o + j

def Block (k t m : ℕ) (v : Fin m → (Fin k → ZMod 2)) (e : Fin m → ZMod 2)
    (addr : Fin m → (Fin t → Bool)) (S : Finset (Fin m)) (o : ℕ) (gs : List Gate) (out : ℕ) :
    Prop :=
  (∀ g ∈ gs, legalG g) ∧ ReadsFrom gs o ∧ out < o + gs.length ∧
  gs.countP counted + 1 ≤ S.card ∧
  ∃ leaf : (Fin t → Bool) → Fin m, (∀ a, leaf a ∈ S) ∧ (∀ i ∈ S, leaf (addr i) = i) ∧
    ∀ Wf, Consistent gs o Wf → Wf.getD out false =
      decide (v (leaf (aOf k t Wf)) ⬝ᵥ xOf k Wf + e (leaf (aOf k t Wf)) = 1)

theorem consistent_append {A B : List Gate} {o : ℕ} {Wf : List Bool}
    (h : Consistent (A ++ B) o Wf) : Consistent A o Wf ∧ Consistent B (o + A.length) Wf := by
  constructor
  · intro j hj
    have := h j (by simp; omega)
    rwa [List.getElem_append_left hj] at this
  · intro j hj
    have := h (A.length + j) (by simp; omega)
    rw [List.getElem_append_right (by omega)] at this
    simp only [Nat.add_sub_cancel_left] at this
    rw [show o + A.length + j = o + (A.length + j) by omega]
    exact this

theorem reads_append {A B : List Gate} {o : ℕ} (hA : ReadsFrom A o)
    (hB : ReadsFrom B (o + A.length)) : ReadsFrom (A ++ B) o := by
  intro j hj i hi
  by_cases h : j < A.length
  · rw [List.getElem_append_left h] at hi; exact hA j h i hi
  · rw [List.getElem_append_right (by omega)] at hi
    have := hB (j - A.length) (by simp at hj; omega) i hi
    omega

def leafGates (k : ℕ) (vi : Fin k → ZMod 2) (ei : ZMod 2) (o : ℕ) : List Gate :=
  ⟨if decide (ei + (k : ZMod 2) = 1) then .and else .or, []⟩ ::
  (List.range k).map (fun j => ⟨.mod 2,
    if (if h : j < k then vi ⟨j, h⟩ else 0) = 1 then [o + j, j] else [o + j]⟩)

theorem leaf_block (k t m : ℕ) (v : Fin m → (Fin k → ZMod 2)) (e : Fin m → ZMod 2)
    (addr : Fin m → (Fin t → Bool)) (i : Fin m) (o : ℕ) :
    Block k t m v e addr {i} o (leafGates k (v i) (e i) o) (o + k) := by
  have hlen : (leafGates k (v i) (e i) o).length = k + 1 := by simp [leafGates]
  refine ⟨?_, ?_, ?_, ?_, fun _ => i, fun _ => Finset.mem_singleton_self _, ?_, ?_⟩
  · intro g hg
    simp only [leafGates, List.mem_cons, List.mem_map, List.mem_range] at hg
    rcases hg with rfl | ⟨j, hj, rfl⟩
    · refine ⟨by simp, ?_⟩
      split_ifs <;> simp
    · refine ⟨by split_ifs <;> simp, Or.inr (Or.inr (Or.inl rfl))⟩
  · intro j hj i' hi'
    cases j with
    | zero => simp [leafGates] at hi'
    | succ j =>
      simp only [leafGates, List.getElem_cons_succ, List.getElem_map, List.getElem_range] at hi'
      have key : ∀ L : List ℕ, (L = [o + j, j] ∨ L = [o + j]) → i' ∈ L → i' < o + (j + 1) := by
        rintro L (rfl | rfl) h <;> simp at h <;> omega
      exact key _ (by
        by_cases hv : (if h : j < k then v i ⟨j, h⟩ else 0) = 1
        · rw [if_pos hv]; exact Or.inl rfl
        · rw [if_neg hv]; exact Or.inr rfl) hi'
  · rw [hlen]; omega
  · have : (leafGates k (v i) (e i) o).countP counted = 0 := by
      rw [List.countP_eq_zero]
      intro g hg
      simp only [leafGates, List.mem_cons, List.mem_map, List.mem_range] at hg
      rcases hg with rfl | ⟨j, hj, rfl⟩
      · simp [counted]
      · simp [counted]
    rw [this]; simp
  · intro i' hi'; rw [Finset.mem_singleton] at hi'; exact hi'.symm
  · intro Wf hW
    have hstep : ∀ j, j ≤ k → b2f (Wf.getD (o + j) false) =
        b2f (decide (e i + (k : ZMod 2) = 1)) +
          ∑ l ∈ Finset.range j,
            ((if h : l < k then v i ⟨l, h⟩ else 0) * b2f (Wf.getD l false) + 1) := by
      intro j
      induction j with
      | zero =>
        intro _
        have := hW 0 (by rw [hlen]; omega)
        simp only [leafGates, List.getElem_cons_zero, List.map_nil, Nat.add_zero] at this
        simp only [Finset.range_zero, Finset.sum_empty, add_zero, Nat.add_zero]
        rw [this]
        cases decide (e i + (k : ZMod 2) = 1) <;> rfl
      | succ j ih =>
        intro hj
        have := hW (j + 1) (by rw [hlen]; omega)
        simp only [leafGates, List.getElem_cons_succ, List.getElem_map,
          List.getElem_range] at this
        rw [this, Finset.sum_range_succ, ← add_assoc, ← ih (by omega)]
        by_cases hv : (if h : j < k then v i ⟨j, h⟩ else 0) = 1
        · rw [if_pos hv]
          simp only [List.map_cons, List.map_nil, eval_mod2_two, b2f_xnor, hv, one_mul]
          ring
        · rw [if_neg hv]
          simp only [List.map_cons, List.map_nil, eval_mod2_one, b2f_not]
          have h0 : (if h : j < k then v i ⟨j, h⟩ else 0) = 0 := by
            generalize (if h : j < k then v i ⟨j, h⟩ else 0) = z at hv ⊢
            revert z; decide
          rw [h0, zero_mul, zero_add]
    have hk := hstep k le_rfl
    apply eq_decide_of_b2f
    rw [hk, Finset.sum_range
      (fun l => (if h : l < k then v i ⟨l, h⟩ else 0) * b2f (Wf.getD l false) + 1)]
    simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [show b2f (decide (e i + (k : ZMod 2) = 1)) = e i + k by unfold b2f; exact z2_bit _]
    simp only [dotProduct, xOf]
    have hkk : (k : ZMod 2) + k = 0 := by
      generalize (k : ZMod 2) = z; revert z; decide
    linear_combination hkk

def combGates (k b out0 out1 o2 : ℕ) : List Gate :=
  [⟨.mod 2, [out0, out1]⟩, ⟨.not, [o2]⟩, ⟨.and, [k + b, o2 + 1]⟩, ⟨.mod 2, [out0, o2 + 2]⟩,
    ⟨.not, [o2 + 3]⟩]

theorem comb_block (k t m : ℕ) (v : Fin m → (Fin k → ZMod 2)) (e : Fin m → ZMod 2)
    (addr : Fin m → (Fin t → Bool)) (S S0 S1 : Finset (Fin m)) (b : Fin t)
    (h0sub : S0 ⊆ S) (h1sub : S1 ⊆ S) (hcard : S0.card + S1.card = S.card)
    (hS0 : ∀ i ∈ S, addr i b = false → i ∈ S0) (hS1 : ∀ i ∈ S, addr i b = true → i ∈ S1)
    (o : ℕ) (ho : k + t ≤ o) (gs0 gs1 : List Gate) (out0 out1 : ℕ)
    (h0 : Block k t m v e addr S0 o gs0 out0)
    (h1 : Block k t m v e addr S1 (o + gs0.length) gs1 out1) :
    Block k t m v e addr S o
      (gs0 ++ gs1 ++ combGates k b out0 out1 (o + gs0.length + gs1.length))
      (o + gs0.length + gs1.length + 4) := by
  obtain ⟨l0, r0, o0, c0, leaf0, m0, f0, s0⟩ := h0
  obtain ⟨l1, r1, o1, c1, leaf1, m1, f1, s1⟩ := h1
  have hb := b.isLt
  refine ⟨?_, ?_, ?_, ?_, fun a => if a b then leaf1 a else leaf0 a, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact l0 g hg
    · exact l1 g hg
    · simp only [combGates, List.mem_cons, List.mem_nil_iff, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp [legalG]
  · apply reads_append (reads_append r0 r1)
    intro j hj i hi
    simp only [combGates, List.length_cons, List.length_nil] at hj
    simp only [List.length_append]
    interval_cases j <;> simp [combGates] at hi <;> omega
  · simp [combGates]; omega
  · simp only [List.countP_append]
    have : (combGates k b out0 out1 (o + gs0.length + gs1.length)).countP counted = 1 := by
      simp [combGates, counted, List.countP_cons]
    omega
  · intro a
    by_cases h : a b = true
    · simp only [h, ↓reduceIte]; exact h1sub (m1 a)
    · simp only [h, ↓reduceIte]; exact h0sub (m0 a)
  · intro i hi
    by_cases h : addr i b = true
    · simp only [h, ↓reduceIte]; exact f1 i (hS1 i hi h)
    · simp only [h, ↓reduceIte]
      exact f0 i (hS0 i hi (by simpa using h))
  · intro Wf hW
    obtain ⟨hW01, hWc⟩ := consistent_append hW
    obtain ⟨hW0, hW1⟩ := consistent_append hW01
    have y0 := s0 Wf hW0
    have y1 := s1 Wf hW1
    have hN : o + (gs0 ++ gs1).length = o + gs0.length + gs1.length := by
      simp only [List.length_append]; omega
    rw [hN] at hWc
    have e0 := hWc 0 (by simp [combGates])
    have e1 := hWc 1 (by simp [combGates])
    have e2 := hWc 2 (by simp [combGates])
    have e3 := hWc 3 (by simp [combGates])
    have e4 := hWc 4 (by simp [combGates])
    simp only [combGates, List.getElem_cons_zero, List.getElem_cons_succ, List.map_cons,
      List.map_nil, add_zero] at e0 e1 e2 e3 e4
    rw [eval_mod2_two] at e0 e3
    rw [eval_and_two] at e2
    rw [eval_not_one] at e1 e4
    have hab : Wf.getD (k + ↑b) false = aOf k t Wf b := rfl
    rw [e4, e3, e2, e1, e0, hab, sel_lemma]
    beta_reduce
    by_cases h : aOf k t Wf b = true
    · simp only [h, ↓reduceIte]; exact y1
    · simp only [h, ↓reduceIte, Bool.false_eq_true]; exact y0

theorem build (k t m : ℕ) (v : Fin m → (Fin k → ZMod 2)) (e : Fin m → ZMod 2)
    (addr : Fin m → (Fin t → Bool)) (hinj : Function.Injective addr) (S : Finset (Fin m)) :
    S.Nonempty → ∀ o, k + t ≤ o → ∃ gs out, Block k t m v e addr S o gs out := by
  classical
  refine Finset.strongInduction
    (p := fun S => S.Nonempty → ∀ o, k + t ≤ o → ∃ gs out, Block k t m v e addr S o gs out)
    ?_ S
  intro S ih hne o ho
  by_cases h1 : S.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    exact ⟨_, _, leaf_block k t m v e addr i o⟩
  · have h2 : 1 < S.card := by
      have := Finset.card_pos.mpr hne; omega
    obtain ⟨i1, hi1, i2, hi2, hne12⟩ := Finset.one_lt_card.mp h2
    have hadd : addr i1 ≠ addr i2 := fun h => hne12 (hinj h)
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hadd
    have key : (addr i1 b = true ∧ addr i2 b = false) ∨ (addr i1 b = false ∧ addr i2 b = true) := by
      revert hb; cases addr i1 b <;> cases addr i2 b <;> simp
    have hS1ne : (S.filter (fun i => addr i b = true)).Nonempty := by
      rcases key with ⟨ha, _⟩ | ⟨_, ha⟩
      · exact ⟨i1, Finset.mem_filter.mpr ⟨hi1, ha⟩⟩
      · exact ⟨i2, Finset.mem_filter.mpr ⟨hi2, ha⟩⟩
    have hS0ne : (S.filter (fun i => ¬ addr i b = true)).Nonempty := by
      rcases key with ⟨_, ha⟩ | ⟨ha, _⟩
      · exact ⟨i2, Finset.mem_filter.mpr ⟨hi2, by simp [ha]⟩⟩
      · exact ⟨i1, Finset.mem_filter.mpr ⟨hi1, by simp [ha]⟩⟩
    have hS1ss : S.filter (fun i => addr i b = true) ⊂ S := by
      rw [Finset.filter_ssubset]
      obtain ⟨x, hx⟩ := hS0ne
      exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    have hS0ss : S.filter (fun i => ¬ addr i b = true) ⊂ S := by
      rw [Finset.filter_ssubset]
      obtain ⟨x, hx⟩ := hS1ne
      exact ⟨x, (Finset.mem_filter.mp hx).1, not_not.mpr (Finset.mem_filter.mp hx).2⟩
    have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun i => addr i b = true)
    obtain ⟨gs0, out0, h0⟩ := ih _ hS0ss hS0ne o ho
    obtain ⟨gs1, out1, h1⟩ := ih _ hS1ss hS1ne (o + gs0.length) (by omega)
    refine ⟨_, _, comb_block k t m v e addr S _ _ b (Finset.filter_subset _ _)
      (Finset.filter_subset _ _) (by omega) ?_ ?_ o ho gs0 gs1 out0 out1 h0 h1⟩
    · intro i hi h
      exact Finset.mem_filter.mpr ⟨hi, by simp [h]⟩
    · intro i hi h
      exact Finset.mem_filter.mpr ⟨hi, h⟩

theorem part2 (k t m : ℕ) (v : Fin m → (Fin k → ZMod 2)) (hv : Function.Injective v)
    (addr : Fin m → (Fin t → Bool)) (hinj : Function.Injective addr) (e : Fin m → ZMod 2)
    (w : Fin m → ℕ) (S : Finset (Fin m)) (hS : S.Nonempty) :
    ∃ C : Circuit, (PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+t) C ∧
        ∀ g ∈ C.gates, legalG g) ∧
      C.output < k + t + C.size ∧ C.gates.countP counted ≤ S.card - 1 ∧
      2 * (∑ j : Fin m, w j * (agr k t C (addr j) (v j) (e j) Finset.univ).card) -
        2^k * (∑ j : Fin m, w j) = 2^k * ∑ j ∈ S, w j := by
  classical
  obtain ⟨gs, out, hl, hr, hout, hc, leaf, hleafS, hleaf, hsem⟩ :=
    build k t m v e addr hinj S hS (k + t) le_rfl
  refine ⟨⟨gs, out⟩, ⟨?_, hl⟩, hout, by simp only; omega, ?_⟩
  · intro j hj i hi
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
    rw [List.getD_eq_getElem _ _ hj] at hi
    exact hr j hj i hi
  · have hev : ∀ (x : Fin k → ZMod 2) (a : Fin t → Bool),
        (⟨gs, out⟩ : Circuit).eval (List.ofFn (fun l : Fin k => decide (x l = 1)) ++ List.ofFn a)
          = decide (v (leaf a) ⬝ᵥ x + e (leaf a) = 1) := by
      intro x a
      have hW := hsem (run gs (inp k t x a)) (fun j hj => by
        have := run_getD_gate gs (inp k t x a) j hj (by rw [inp_length]; exact hr j hj)
        rw [inp_length] at this; exact this)
      have ha : aOf k t (run gs (inp k t x a)) = a := by
        funext l; unfold aOf; rw [run_getD_lt _ _ _ (by rw [inp_length]; omega)]
        unfold inp; rw [List.getD_append_right _ _ _ _ (by simp)]
        simp [List.getD_eq_getElem?_getD]
      have hx : xOf k (run gs (inp k t x a)) = x := by
        funext l
        have hg : (inp k t x a).getD l false = decide (x l = 1) := by
          unfold inp; rw [List.getD_append _ _ _ _ (by simp)]; simp [List.getD_eq_getElem?_getD]
        unfold xOf; rw [run_getD_lt _ _ _ (by rw [inp_length]; omega), hg]
        exact z2_bit _
      rw [ha, hx] at hW
      exact hW
    have hcount : ∀ j, 2 * (agr k t ⟨gs, out⟩ (addr j) (v j) (e j) Finset.univ).card =
        2^k * (1 + if j ∈ S then 1 else 0) := by
      intro j
      have hagr : agr k t ⟨gs, out⟩ (addr j) (v j) (e j) Finset.univ =
          Finset.univ.filter (fun x => decide (v (leaf (addr j)) ⬝ᵥ x + e (leaf (addr j)) = 1) =
            decide (v j ⬝ᵥ x + e j = 1)) := by
        unfold agr; apply Finset.filter_congr; intro x _; rw [hev]
      rw [hagr]
      by_cases hj : j ∈ S
      · rw [if_pos hj, hleaf j hj, Finset.filter_true_of_mem (fun x _ => rfl), card_fun_zmod]
        ring
      · rw [if_neg hj, add_zero, mul_one, ← card_fun_zmod]
        have hi : leaf (addr j) ≠ j := fun h => hj (h ▸ hleafS (addr j))
        have hvi : v (leaf (addr j)) ≠ v j := fun h => hi (hv h)
        obtain ⟨l, hl⟩ := Function.ne_iff.mp hvi
        apply half_card _ (Pi.single l 1) _ (fun x _ => Finset.mem_univ _)
        intro x _
        rw [dotProduct_add, dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one]
        exact z2_agree _ _ _ _ _ _ (sub_ne_zero.mpr (Ne.symm hl))
    have hS' : ∑ j ∈ S, w j = ∑ j, if j ∈ S then w j else 0 := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have htot : 2 * (∑ j : Fin m, w j * (agr k t ⟨gs, out⟩ (addr j) (v j) (e j) Finset.univ).card)
        = 2^k * ∑ j, w j + 2^k * ∑ j ∈ S, w j := by
      rw [Finset.mul_sum, hS', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have := hcount j
      split_ifs at this ⊢ with hj
      · rw [show 2 * (w j * (agr k t ⟨gs, out⟩ (addr j) (v j) (e j) Finset.univ).card) =
          w j * (2 * (agr k t ⟨gs, out⟩ (addr j) (v j) (e j) Finset.univ).card) by ring, this]
        ring
      · rw [show 2 * (w j * (agr k t ⟨gs, out⟩ (addr j) (v j) (e j) Finset.univ).card) =
          w j * (2 * (agr k t ⟨gs, out⟩ (addr j) (v j) (e j) Finset.univ).card) by ring, this]
        ring
    rw [htot, Nat.add_sub_cancel_left]

end PEqualNP.Outside.L_meta_29741_aux

theorem PEqualNP.Outside.L_meta_29741 : ∀ (k t m s : ℕ),
  let F := ZMod 2
  let V := Fin k → F
  ∀ (v : Fin m ↪ V) (addr : Fin m ↪ (Fin t → Bool)) (e : Fin m → F) (w : Fin m → ℕ),
    let legal := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+t) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
    let cost := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.gates.countP (fun g => @decide
        ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
    let gain := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      let hits := ∑ j : Fin m, w j * ((Finset.univ : Finset V).filter (fun x =>
        C.eval (List.ofFn (fun l : Fin k => decide (x l = 1)) ++ List.ofFn (addr j)) =
          decide (dotProduct (v j) x + e j = 1))).card
      2*hits - 2^k*(∑ j : Fin m, w j)
    ((∀ R : Finset (Fin m), R.Nonempty → R.card % 2 = 0 → R.card ≤ s+2 →
        (∑ j ∈ R, v j) ≠ 0) →
      ∀ C, legal C → cost C ≤ s → ∃ S : Finset (Fin m), S.card ≤ s+1 ∧
        gain C ≤ 2^k*(∑ j ∈ S, w j)) ∧
    (∀ S : Finset (Fin m), S.Nonempty →
      ∃ C, legal C ∧ C.output < k+t+C.size ∧ cost C ≤ S.card-1 ∧
        gain C = 2^k*(∑ j ∈ S, w j)) := by
  intro k t m s F V v addr e w legal cost gain
  refine ⟨?_, ?_⟩
  · intro hyp C hC hcost
    exact PEqualNP.Outside.L_meta_29741_aux.part1 k t m s v addr e w hyp C hC.2 hcost
  · intro S hS
    obtain ⟨C, hleg, hout, hcost, hgain⟩ :=
      PEqualNP.Outside.L_meta_29741_aux.part2 k t m v v.injective addr addr.injective e w S hS
    exact ⟨C, hleg, hout, hcost, hgain⟩
