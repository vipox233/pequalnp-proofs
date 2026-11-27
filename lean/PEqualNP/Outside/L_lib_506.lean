import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_506_aux

open PEqualNP.CircuitLowerBounds

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem b2z_decide_eq_one (t : ZMod 2) : b2z (decide (t = 1)) = t := by
  revert t
  decide

private theorem bool_eq_decide_of_b2z (b : Bool) (t : ZMod 2) (h : b2z b = t) :
    b = decide (t = 1) := by
  cases b <;> revert t h <;> decide

private theorem b2z_not (b : Bool) : b2z (!b) = b2z b + 1 := by
  revert b
  decide

private theorem b2z_and (b1 b2 : Bool) : b2z (b1 && b2) = b2z b1 * b2z b2 := by
  revert b1 b2
  decide

private theorem b2z_mod2_one (b1 : Bool) :
    b2z (decide ([b1].count true % 2 = 0)) = b2z b1 + 1 := by
  revert b1
  decide

private theorem b2z_mod2_two (b1 b2 : Bool) :
    b2z (decide ([b1, b2].count true % 2 = 0)) = b2z b1 + b2z b2 + 1 := by
  revert b1 b2
  decide

private theorem zmod2_ne_zero (t : ZMod 2) (h : t ≠ 0) : t = 1 := by
  revert t h
  decide

private theorem zmod2_add_self (t : ZMod 2) : t + t = 0 := by
  revert t
  decide

private theorem zmod2_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t
  decide

private theorem zmod2_vec_add_self {n : ℕ} (x : Fin n → ZMod 2) : x + x = 0 := by
  ext i
  exact zmod2_add_self (x i)

private def inputVec {n : ℕ} (x : Fin n → ZMod 2) : List Bool :=
  List.ofFn (fun i : Fin n => decide (x i = 1))

private def wiresOf {n : ℕ} (gs : List Gate) (x : Fin n → ZMod 2) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (inputVec x)

private theorem foldl_wires_length (gs : List Gate) (w0 : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length =
      w0.length + gs.length := by
  induction gs generalizing w0 with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private theorem wiresOf_length {n : ℕ} (gs : List Gate) (x : Fin n → ZMod 2) :
    (wiresOf gs x).length = n + gs.length := by
  unfold wiresOf inputVec
  rw [foldl_wires_length, List.length_ofFn]

private theorem wiresOf_append_singleton {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → ZMod 2) :
    wiresOf (gs ++ [g]) x =
      wiresOf gs x ++ [g.op.eval (g.inputs.map fun i => (wiresOf gs x).getD i false)] := by
  unfold wiresOf
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem getD_append_singleton_lt (l : List Bool) (v : Bool) (k : ℕ) (hk : k < l.length) :
    (l ++ [v]).getD k false = l.getD k false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hk]

private theorem getD_append_singleton_eq (l : List Bool) (v : Bool) :
    (l ++ [v]).getD l.length false = v := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
  simp

private theorem getD_append_singleton_gt (l : List Bool) (v : Bool) (k : ℕ) (hk : l.length < k) :
    (l ++ [v]).getD k false = false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none]
  · rfl
  · rw [List.length_append, List.length_singleton]
    omega

private noncomputable def andCost (gs : List Gate) : ℕ :=
  gs.countP (fun x => @decide (x.op = .and) (Classical.propDecidable _))

private theorem gate_ok_and_count_pos (gs : List Gate) (g : Gate) (h : g.op = .and) :
    andCost (gs ++ [g]) = andCost gs + 1 := by
  unfold andCost
  rw [List.countP_append, List.countP_cons, List.countP_nil]
  simp [h]

private theorem gate_ok_and_count_neg (gs : List Gate) (g : Gate) (h : g.op ≠ .and) :
    andCost (gs ++ [g]) = andCost gs := by
  unfold andCost
  rw [List.countP_append, List.countP_cons, List.countP_nil]
  simp [h]

private theorem finrank_ker_dot {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (a : Fin n → ZMod 2) :
    ∃ U' : Submodule (ZMod 2) (Fin n → ZMod 2),
      U' ≤ U ∧
      (∀ x ∈ U', dotProduct a x = 0) ∧
      Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) U' + 1 := by
  let phi : U →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun u => dotProduct a u.1
      map_add' := fun u v => dotProduct_add a u.1 v.1
      map_smul' := fun c u => by
        simp only [SetLike.val_smul, dotProduct_smul, smul_eq_mul, RingHom.id_apply] }
  let U' : Submodule (ZMod 2) (Fin n → ZMod 2) := (LinearMap.ker phi).map U.subtype
  refine ⟨U', ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨u, _, rfl⟩
    exact u.2
  · intro x hx
    rcases hx with ⟨u, hu, rfl⟩
    exact hu
  · have heq : Module.finrank (ZMod 2) (LinearMap.ker phi) = Module.finrank (ZMod 2) U' :=
      (Submodule.equivMapOfInjective U.subtype (Submodule.injective_subtype U)
        (LinearMap.ker phi)).finrank_eq
    have hrn := LinearMap.finrank_range_add_finrank_ker phi
    have hle : Module.finrank (ZMod 2) (LinearMap.range phi) ≤
        Module.finrank (ZMod 2) (ZMod 2) := Submodule.finrank_le _
    rw [Module.finrank_self] at hle
    omega

private def AdmGates (gs : List Gate) : Prop :=
  ∀ g ∈ gs,
    (g.op = .and ∧ g.inputs.length = 2) ∨
    (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
    (g.op = .not ∧ g.inputs.length = 1)

private theorem gates_affine_restrict {n : ℕ} (gs : List Gate) (hgs : AdmGates gs) :
    ∃ (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (p : Fin n → ZMod 2),
      n ≤ Module.finrank (ZMod 2) U + andCost gs ∧
      ∀ k : ℕ, ∃ (a : Fin n → ZMod 2) (b : ZMod 2),
        ∀ x ∈ U, b2z ((wiresOf gs (p + x)).getD k false) = dotProduct a (p + x) + b := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨⊤, 0, ?_, ?_⟩
    · simp [andCost, finrank_top]
    · intro k
      by_cases hk : k < n
      · refine ⟨Pi.single ⟨k, hk⟩ (1 : ZMod 2), 0, ?_⟩
        intro x _
        unfold wiresOf inputVec
        simp [List.getD_eq_getElem?_getD, hk, b2z_decide_eq_one, dotProduct, Pi.single_apply]
      · refine ⟨0, 0, ?_⟩
        intro x _
        unfold wiresOf inputVec
        simp [List.getD_eq_getElem?_getD, hk, b2z]
  | append_singleton gs g ih =>
    have hgs' : AdmGates gs := fun h hh => hgs h (List.mem_append_left [g] hh)
    have hg : (g.op = .and ∧ g.inputs.length = 2) ∨
        (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
        (g.op = .not ∧ g.inputs.length = 1) :=
      hgs g (List.mem_append_right gs (List.mem_singleton_self g))
    obtain ⟨U, p, hdim, haff⟩ := ih hgs'
    have hstep_same :
        ∀ (a_new : Fin n → ZMod 2) (b_new : ZMod 2),
        (∀ x ∈ U, b2z (g.op.eval (g.inputs.map fun i => (wiresOf gs (p + x)).getD i false)) =
          dotProduct a_new (p + x) + b_new) →
        ∀ k : ℕ, ∃ (a : Fin n → ZMod 2) (b : ZMod 2),
          ∀ x ∈ U, b2z ((wiresOf (gs ++ [g]) (p + x)).getD k false) =
            dotProduct a (p + x) + b := by
      intro a_new b_new hnew k
      by_cases hlt : k < n + gs.length
      · obtain ⟨a, b, hab⟩ := haff k
        refine ⟨a, b, ?_⟩
        intro x hx
        rw [wiresOf_append_singleton, getD_append_singleton_lt]
        · exact hab x hx
        · rw [wiresOf_length]; exact hlt
      · by_cases heq : k = n + gs.length
        · subst heq
          refine ⟨a_new, b_new, ?_⟩
          intro x hx
          rw [wiresOf_append_singleton, ← wiresOf_length gs (p + x), getD_append_singleton_eq]
          exact hnew x hx
        · refine ⟨0, 0, ?_⟩
          intro x _
          rw [wiresOf_append_singleton, getD_append_singleton_gt]
          · simp [b2z]
          · rw [wiresOf_length]; omega
    rcases hg with ⟨hop, hlen⟩ | ⟨hop, hlen⟩ | ⟨hop, hlen⟩
    · rcases hgi : g.inputs with _ | ⟨i1, _ | ⟨i2, _ | _⟩⟩
      · simp [hgi] at hlen
      · simp [hgi] at hlen
      · obtain ⟨a1, b1, ha1⟩ := haff i1
        obtain ⟨a2, b2, ha2⟩ := haff i2
        by_cases hconst : ∀ x ∈ U, dotProduct a1 x = 0
        · refine ⟨U, p, ?_, ?_⟩
          · rw [gate_ok_and_count_pos gs g hop]
            omega
          · let c : ZMod 2 := dotProduct a1 p + b1
            refine hstep_same (c • a2) (c * b2) ?_
            intro x hx
            rw [hop, hgi]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
              List.all_nil, id_eq, Bool.and_true]
            rw [b2z_and, ha1 x hx, ha2 x hx]
            have h1 : dotProduct a1 (p + x) + b1 = c := by
              rw [dotProduct_add, hconst x hx, add_zero]
            rw [h1, smul_dotProduct, smul_eq_mul, mul_add]
        · have hex : ∃ v ∈ U, dotProduct a1 v = 1 := by
            by_contra hno
            apply hconst
            intro x hx
            by_contra hne
            exact hno ⟨x, hx, zmod2_ne_zero _ hne⟩
          obtain ⟨v, hvU, hv1⟩ := hex
          obtain ⟨U', hU'le, hU'ker, hU'dim⟩ := finrank_ker_dot U a1
          let p' : Fin n → ZMod 2 := if dotProduct a1 p + b1 = 0 then p else p + v
          have hp'_mem : ∀ x ∈ U', ∃ y ∈ U, p' + x = p + y := by
            intro x hx
            by_cases hc : dotProduct a1 p + b1 = 0
            · refine ⟨x, hU'le hx, ?_⟩
              simp [p', hc]
            · refine ⟨v + x, U.add_mem hvU (hU'le hx), ?_⟩
              simp [p', hc, add_assoc]
          have hp'_zero : ∀ x ∈ U', dotProduct a1 (p' + x) + b1 = 0 := by
            intro x hx
            by_cases hc : dotProduct a1 p + b1 = 0
            · simp [p', hc, dotProduct_add, hU'ker x hx]
            · have hc1 : dotProduct a1 p + b1 = 1 := zmod2_ne_zero _ hc
              simp only [p', hc, ↓reduceIte]
              have hsum : dotProduct a1 (p + v + x) + b1 =
                  (dotProduct a1 p + b1) + dotProduct a1 v + dotProduct a1 x := by
                rw [dotProduct_add, dotProduct_add]
                ring
              rw [hsum, hc1, hv1, hU'ker x hx, add_zero]
              exact zmod2_add_self 1
          refine ⟨U', p', ?_, ?_⟩
          · rw [gate_ok_and_count_pos gs g hop]
            omega
          · intro k
            by_cases hlt : k < n + gs.length
            · obtain ⟨a, b, hab⟩ := haff k
              refine ⟨a, b, ?_⟩
              intro x hx
              obtain ⟨y, hyU, hpy⟩ := hp'_mem x hx
              rw [wiresOf_append_singleton, getD_append_singleton_lt]
              · rw [hpy]; exact hab y hyU
              · rw [wiresOf_length]; exact hlt
            · by_cases heq : k = n + gs.length
              · subst heq
                refine ⟨0, 0, ?_⟩
                intro x hx
                obtain ⟨y, hyU, hpy⟩ := hp'_mem x hx
                rw [wiresOf_append_singleton, ← wiresOf_length gs (p' + x),
                  getD_append_singleton_eq, hop, hgi]
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
                  List.all_nil, id_eq, Bool.and_true]
                rw [b2z_and, hpy, ha1 y hyU, ← hpy, hp'_zero x hx, zero_mul,
                  zero_dotProduct, add_zero]
              · refine ⟨0, 0, ?_⟩
                intro x _
                rw [wiresOf_append_singleton, getD_append_singleton_gt]
                · simp [b2z]
                · rw [wiresOf_length]; omega
      · simp [hgi] at hlen
    · refine ⟨U, p, ?_, ?_⟩
      · rw [gate_ok_and_count_neg gs g (by rw [hop]; exact GateOp.noConfusion)]
        exact hdim
      · rcases hgi : g.inputs with _ | ⟨i1, _ | ⟨i2, _ | _⟩⟩
        · refine hstep_same 0 1 ?_
          intro x _
          rw [hop, hgi]
          simp [GateOp.eval, b2z]
        · obtain ⟨a1, b1, ha1⟩ := haff i1
          refine hstep_same a1 (b1 + 1) ?_
          intro x hx
          rw [hop, hgi]
          simp only [List.map_cons, List.map_nil, GateOp.eval]
          rw [b2z_mod2_one, ha1 x hx]
          ring
        · obtain ⟨a1, b1, ha1⟩ := haff i1
          obtain ⟨a2, b2, ha2⟩ := haff i2
          refine hstep_same (a1 + a2) (b1 + b2 + 1) ?_
          intro x hx
          rw [hop, hgi]
          simp only [List.map_cons, List.map_nil, GateOp.eval]
          rw [b2z_mod2_two, ha1 x hx, ha2 x hx, add_dotProduct]
          ring
        · simp [hgi] at hlen
    · refine ⟨U, p, ?_, ?_⟩
      · rw [gate_ok_and_count_neg gs g (by rw [hop]; exact GateOp.noConfusion)]
        exact hdim
      · rcases hgi : g.inputs with _ | ⟨i1, _ | _⟩
        · simp [hgi] at hlen
        · obtain ⟨a1, b1, ha1⟩ := haff i1
          refine hstep_same a1 (b1 + 1) ?_
          intro x hx
          rw [hop, hgi]
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
          rw [b2z_not, ha1 x hx]
          ring
        · simp [hgi] at hlen

private theorem exists_dotProduct_eq {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (L : U →ₗ[ZMod 2] ZMod 2) :
    ∃ a : Fin n → ZMod 2, ∀ x : U, dotProduct x.1 a = L x := by
  obtain ⟨W, hUW⟩ := Submodule.exists_isCompl U
  let L' : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := L.comp (Submodule.projectionOnto U W hUW)
  refine ⟨fun i => L' (Pi.single i 1), fun x => ?_⟩
  have hsum : ∑ i : Fin n, x.1 i • Pi.single i (1 : ZMod 2) = x.1 := by
    ext j
    simp [Pi.single_apply]
  have hdot : dotProduct x.1 (fun i => L' (Pi.single i 1)) = L' x.1 := by
    conv_rhs => rw [← hsum]
    rw [map_sum]
    unfold dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
  rw [hdot]
  change L (Submodule.projectionOnto U W hUW x.1) = L x
  rw [Submodule.projectionOnto_apply_left hUW x]

private theorem rank_add_ker {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    M.rank + Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) = n := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fin_fun] at h
  exact h

private theorem iso_of_affine {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (p a : Fin n → ZMod 2) (b : ZMod 2)
    (haff : ∀ x ∈ U, f (p + x) = dotProduct a (p + x) + b) :
    ∀ x ∈ U, ∀ y ∈ U, dotProduct x (M.mulVec y) = 0 := by
  intro x hx y hy
  have e1 := haff (x + y) (U.add_mem hx hy)
  have e2 := haff x hx
  have e3 := haff y hy
  have e4 := haff 0 U.zero_mem
  have hsum_aff : f (p + (x + y)) + f (p + x) + f (p + y) + f (p + 0) = 0 := by
    rw [e1, e2, e3, e4]
    simp only [dotProduct_add, add_zero]
    have hs : ∀ u v w t : ZMod 2,
        (u + (v + w) + t) + (u + v + t) + (u + w + t) + (u + t) = 0 := by
      intro u v w t
      fin_cases u <;> fin_cases v <;> fin_cases w <;> fin_cases t <;> rfl
    exact hs (dotProduct a p) (dotProduct a x) (dotProduct a y) b
  have hblin : dotProduct p (M.mulVec (x + y)) =
      dotProduct p (M.mulVec x) + dotProduct p (M.mulVec y) := by
    rw [Matrix.mulVec_add, dotProduct_add]
  have hcomb : (f (p + (x + y)) + f p + f (x + y) + f 0) +
      (f (p + x) + f p + f x + f 0) +
      (f (p + y) + f p + f y + f 0) +
      (f (x + y) + f x + f y + f 0) =
      dotProduct p (M.mulVec (x + y)) + dotProduct p (M.mulVec x) +
      dotProduct p (M.mulVec y) + dotProduct x (M.mulVec y) := by
    rw [hf p (x + y), hf p x, hf p y, hf x y]
  have hLHS : (f (p + (x + y)) + f p + f (x + y) + f 0) +
      (f (p + x) + f p + f x + f 0) +
      (f (p + y) + f p + f y + f 0) +
      (f (x + y) + f x + f y + f 0) =
      f (p + (x + y)) + f (p + x) + f (p + y) + f (p + 0) := by
    rw [add_zero]
    calc (f (p + (x + y)) + f p + f (x + y) + f 0) +
          (f (p + x) + f p + f x + f 0) +
          (f (p + y) + f p + f y + f 0) +
          (f (x + y) + f x + f y + f 0)
        = (f (p + (x + y)) + f (p + x) + f (p + y) + f p) + (f p + f p) +
          (f (x + y) + f (x + y)) + (f x + f x) + (f y + f y) +
          ((f 0 + f 0) + (f 0 + f 0)) := by ring
      _ = f (p + (x + y)) + f (p + x) + f (p + y) + f p := by
          simp only [zmod2_add_self, add_zero]
  have hRHS : dotProduct p (M.mulVec (x + y)) + dotProduct p (M.mulVec x) +
      dotProduct p (M.mulVec y) + dotProduct x (M.mulVec y) =
      dotProduct x (M.mulVec y) := by
    rw [hblin]
    calc dotProduct p (M.mulVec x) + dotProduct p (M.mulVec y) +
          dotProduct p (M.mulVec x) + dotProduct p (M.mulVec y) + dotProduct x (M.mulVec y)
        = (dotProduct p (M.mulVec x) + dotProduct p (M.mulVec x)) +
          (dotProduct p (M.mulVec y) + dotProduct p (M.mulVec y)) + dotProduct x (M.mulVec y) := by
            ring
      _ = dotProduct x (M.mulVec y) := by simp only [zmod2_add_self, zero_add]
  rw [hLHS, hRHS, hsum_aff] at hcomb
  exact hcomb.symm

private theorem iso_dim_upper {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hiso : ∀ x ∈ U, ∀ y ∈ U, dotProduct x (M.mulVec y) = 0) :
    2 * Module.finrank (ZMod 2) U + M.rank ≤ 2 * n := by
  let b := Module.finBasis (ZMod 2) U
  let ψ : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) U) → ZMod 2) :=
    { toFun := fun v j => dotProduct (b j).1 v
      map_add' := fun v w => by ext j; simp [dotProduct_add]
      map_smul' := fun c v => by ext j; simp [dotProduct_smul] }
  have hψsurj : Function.Surjective ψ := by
    intro y
    let L : U →ₗ[ZMod 2] ZMod 2 := b.constr (ZMod 2) y
    obtain ⟨v, hv⟩ := exists_dotProduct_eq U L
    refine ⟨v, ?_⟩
    ext j
    change dotProduct (b j).1 v = y j
    rw [hv (b j)]
    simp [L]
  have hψrk : Module.finrank (ZMod 2) (LinearMap.ker ψ) + Module.finrank (ZMod 2) U = n := by
    have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    rw [LinearMap.range_eq_top.mpr hψsurj, finrank_top, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at h1
    omega
  let T : U →ₗ[ZMod 2] (Fin n → ZMod 2) := M.mulVecLin.comp U.subtype
  have hTrk : Module.finrank (ZMod 2) (LinearMap.range T) +
      Module.finrank (ZMod 2) (LinearMap.ker T) = Module.finrank (ZMod 2) U :=
    LinearMap.finrank_range_add_finrank_ker T
  have hRle : Module.finrank (ZMod 2) (LinearMap.range T) ≤
      Module.finrank (ZMod 2) (LinearMap.ker ψ) := by
    refine Submodule.finrank_mono ?_
    rintro v ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    ext j
    exact hiso (b j).1 (b j).2 x.1 x.2
  have hKle : Module.finrank (ZMod 2) (LinearMap.ker T) ≤
      Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) := by
    have heq : Module.finrank (ZMod 2) ((LinearMap.ker T).map U.subtype) =
        Module.finrank (ZMod 2) (LinearMap.ker T) :=
      Submodule.finrank_map_subtype_eq U (LinearMap.ker T)
    rw [← heq]
    refine Submodule.finrank_mono ?_
    rintro v ⟨x, hx, rfl⟩
    exact hx
  have hMrk := rank_add_ker M
  omega

private theorem forward_bound {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (t : ℕ) (C : Circuit) (hAdm : AdmGates C.gates) (hCost : andCost C.gates ≤ t)
    (hEval : ∀ x : Fin n → ZMod 2, C.eval (inputVec x) = decide (f x = 1)) :
    M.rank ≤ 2 * t := by
  obtain ⟨U, p, hdim, haff⟩ := gates_affine_restrict C.gates hAdm
  obtain ⟨a, b, hab⟩ := haff C.output
  have hfaff : ∀ x ∈ U, f (p + x) = dotProduct a (p + x) + b := by
    intro x hx
    have h1 := hab x hx
    have h2 := hEval (p + x)
    have h3 : (wiresOf C.gates (p + x)).getD C.output false = C.eval (inputVec (p + x)) := rfl
    rw [h3, h2, b2z_decide_eq_one] at h1
    exact h1
  have hiso := iso_of_affine f M hf U p a b hfaff
  have hup := iso_dim_upper M U hiso
  omega

private theorem polar_self {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (x : Fin n → ZMod 2) : dotProduct x (M.mulVec x) = 0 := by
  have h := hf x x
  rw [zmod2_vec_add_self] at h
  have h1 : f 0 + f x + f x + f 0 = 0 := by
    calc f 0 + f x + f x + f 0 = (f 0 + f 0) + (f x + f x) := by ring
      _ = 0 := by simp [zmod2_add_self]
  rw [h1] at h
  exact h.symm

private theorem polar_symm {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (x y : Fin n → ZMod 2) :
    dotProduct x (M.mulVec y) = dotProduct y (M.mulVec x) := by
  rw [← hf x y, ← hf y x, add_comm x y]
  ring

private theorem affine_of_rank_zero {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (h0 : M.rank = 0) :
    ∃ (a : Fin n → ZMod 2) (b : ZMod 2), ∀ x, f x = dotProduct a x + b := by
  have hker : LinearMap.ker M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hr := rank_add_ker M
    rw [Module.finrank_fin_fun]
    omega
  have hM0 : ∀ y, M.mulVec y = 0 := by
    intro y
    have hy : y ∈ LinearMap.ker M.mulVecLin := by rw [hker]; trivial
    exact hy
  let L : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => f x + f 0
      map_add' := fun x y => by
        have h := hf x y
        rw [hM0 y, dotProduct_zero] at h
        have hh : ∀ a1 a2 a3 a4 : ZMod 2, a1 + a2 + a3 + a4 = 0 → a1 + a4 = a2 + a4 + (a3 + a4) := by
          intro a1 a2 a3 a4 hz
          fin_cases a1 <;> fin_cases a2 <;> fin_cases a3 <;> fin_cases a4 <;> revert hz <;> decide
        exact hh (f (x + y)) (f x) (f y) (f 0) h
      map_smul' := fun c x => by
        rcases zmod2_cases c with rfl | rfl
        · simp [zmod2_add_self]
        · simp }
  refine ⟨fun i => L (Pi.single i 1), f 0, fun x => ?_⟩
  have hsum : ∑ i : Fin n, x i • Pi.single i (1 : ZMod 2) = x := by
    ext j
    simp [Pi.single_apply]
  have hdot : dotProduct (fun i => L (Pi.single i 1)) x = L x := by
    conv_rhs => rw [← hsum]
    rw [map_sum]
    unfold dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [hdot]
  change f x = (f x + f 0) + f 0
  rw [add_assoc, zmod2_add_self, add_zero]

private theorem quad_decomp {n : ℕ} :
    ∀ (t : ℕ) (f : (Fin n → ZMod 2) → ZMod 2) (M : Matrix (Fin n) (Fin n) (ZMod 2)),
      (∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y)) →
      M.rank ≤ 2 * t →
      ∃ (ps : List ((Fin n → ZMod 2) × (Fin n → ZMod 2))) (a : Fin n → ZMod 2) (b : ZMod 2),
        ps.length ≤ t ∧
        ∀ x, f x = (ps.map (fun p => dotProduct p.1 x * dotProduct p.2 x)).sum +
          dotProduct a x + b := by
  intro t
  induction t with
  | zero =>
    intro f M hf hle
    have h0 : M.rank = 0 := by omega
    obtain ⟨a, b, hab⟩ := affine_of_rank_zero f M hf h0
    exact ⟨[], a, b, by simp, fun x => by simp [hab x]⟩
  | succ t ih =>
    intro f M hf hle
    by_cases h0 : M.rank = 0
    · obtain ⟨a, b, hab⟩ := affine_of_rank_zero f M hf h0
      exact ⟨[], a, b, by simp, fun x => by simp [hab x]⟩
    · have hexv : ∃ v : Fin n → ZMod 2, M.mulVec v ≠ 0 := by
        by_contra hno
        have hker : LinearMap.ker M.mulVecLin = ⊤ := by
          rw [eq_top_iff]
          intro y _
          rw [LinearMap.mem_ker]
          by_contra hy
          exact hno ⟨y, hy⟩
        have hr := rank_add_ker M
        rw [hker, finrank_top, Module.finrank_fin_fun] at hr
        omega
      obtain ⟨v, hv⟩ := hexv
      have hexi : ∃ i : Fin n, M.mulVec v i = 1 := by
        by_contra hno
        apply hv
        ext i
        by_contra hi
        exact hno ⟨i, zmod2_ne_zero _ hi⟩
      obtain ⟨i, hi⟩ := hexi
      let u : Fin n → ZMod 2 := Pi.single i 1
      have huv : dotProduct u (M.mulVec v) = 1 := by
        unfold u
        simp [dotProduct, Pi.single_apply, hi]
      let c1 : Fin n → ZMod 2 := M.mulVec u
      let c2 : Fin n → ZMod 2 := M.mulVec v
      have hc1 : ∀ x, dotProduct c1 x = dotProduct u (M.mulVec x) := by
        intro x
        rw [dotProduct_comm, polar_symm f M hf]
      have hc2 : ∀ x, dotProduct c2 x = dotProduct v (M.mulVec x) := by
        intro x
        rw [dotProduct_comm, polar_symm f M hf]
      let f' : (Fin n → ZMod 2) → ZMod 2 := fun x => f x + dotProduct c1 x * dotProduct c2 x
      let M' : Matrix (Fin n) (Fin n) (ZMod 2) :=
        Matrix.of fun r s => M r s + c1 r * c2 s + c2 r * c1 s
      have hM'mul : ∀ y r, M'.mulVec y r =
          M.mulVec y r + c1 r * dotProduct c2 y + c2 r * dotProduct c1 y := by
        intro y r
        simp only [Matrix.mulVec, dotProduct, M', Matrix.of_apply]
        have heq : ∀ s, (M r s + c1 r * c2 s + c2 r * c1 s) * y s =
            M r s * y s + c1 r * (c2 s * y s) + c2 r * (c1 s * y s) := fun s => by ring
        simp only [heq, Finset.sum_add_distrib, ← Finset.mul_sum]
      have hf' : ∀ x y, f' (x + y) + f' x + f' y + f' 0 = dotProduct x (M'.mulVec y) := by
        intro x y
        have hdot : dotProduct x (M'.mulVec y) =
            dotProduct x (M.mulVec y) + dotProduct x c1 * dotProduct c2 y +
            dotProduct x c2 * dotProduct c1 y := by
          unfold dotProduct
          simp only [hM'mul, dotProduct]
          have heq : ∀ r, x r * (M.mulVec y r + c1 r * ∑ s, c2 s * y s +
              c2 r * ∑ s, c1 s * y s) =
              x r * M.mulVec y r + (x r * c1 r) * (∑ s, c2 s * y s) +
              (x r * c2 r) * (∑ s, c1 s * y s) := fun r => by ring
          simp only [heq, Finset.sum_add_distrib, ← Finset.sum_mul]
        rw [hdot, ← hf x y]
        simp only [f', dotProduct_add, dotProduct_zero, mul_zero, add_zero]
        rw [dotProduct_comm x c1, dotProduct_comm x c2]
        have h2 : ∀ z : ZMod 2, z + z = 0 := zmod2_add_self
        calc f (x + y) + (dotProduct c1 x + dotProduct c1 y) * (dotProduct c2 x + dotProduct c2 y) +
              (f x + dotProduct c1 x * dotProduct c2 x) +
              (f y + dotProduct c1 y * dotProduct c2 y) + f 0
            = (f (x + y) + f x + f y + f 0) +
              dotProduct c1 x * dotProduct c2 y + dotProduct c2 x * dotProduct c1 y +
              (dotProduct c1 x * dotProduct c2 x + dotProduct c1 x * dotProduct c2 x) +
              (dotProduct c1 y * dotProduct c2 y + dotProduct c1 y * dotProduct c2 y) := by ring
          _ = f (x + y) + f x + f y + f 0 +
              dotProduct c1 x * dotProduct c2 y + dotProduct c2 x * dotProduct c1 y := by
              simp only [h2, add_zero]
      have hker_sub : LinearMap.ker M.mulVecLin ≤ LinearMap.ker M'.mulVecLin := by
        intro y hy
        rw [LinearMap.mem_ker] at hy ⊢
        ext r
        change M'.mulVec y r = 0
        rw [hM'mul y r, hc2 y, hc1 y]
        have hy0 : M.mulVec y = 0 := hy
        rw [hy0]
        simp
      have hu_ker : u ∈ LinearMap.ker M'.mulVecLin := by
        rw [LinearMap.mem_ker]
        ext r
        change M'.mulVec u r = 0
        rw [hM'mul u r, hc2 u, hc1 u, polar_self f M hf u, polar_symm f M hf v u, huv]
        change c1 r + c1 r * 1 + c2 r * 0 = 0
        simp [zmod2_add_self]
      have hv_ker : v ∈ LinearMap.ker M'.mulVecLin := by
        rw [LinearMap.mem_ker]
        ext r
        change M'.mulVec v r = 0
        rw [hM'mul v r, hc2 v, hc1 v, polar_self f M hf v, huv]
        change c2 r + c1 r * 0 + c2 r * 1 = 0
        simp [zmod2_add_self]
      let S : Submodule (ZMod 2) (Fin n → ZMod 2) :=
        Submodule.span (ZMod 2) {u} ⊔ Submodule.span (ZMod 2) {v}
      have hS_sub : LinearMap.ker M.mulVecLin ⊔ S ≤ LinearMap.ker M'.mulVecLin := by
        refine sup_le hker_sub (sup_le ?_ ?_)
        · rw [Submodule.span_singleton_le_iff_mem]; exact hu_ker
        · rw [Submodule.span_singleton_le_iff_mem]; exact hv_ker
      have hdisj_uv : Submodule.span (ZMod 2) {u} ⊓ Submodule.span (ZMod 2) {v} = ⊥ := by
        rw [eq_bot_iff]
        intro w hw
        rw [Submodule.mem_inf, Submodule.mem_span_singleton, Submodule.mem_span_singleton] at hw
        obtain ⟨⟨a1, rfl⟩, ⟨a2, ha2⟩⟩ := hw
        rw [Submodule.mem_bot]
        rcases zmod2_cases a1 with rfl | rfl
        · simp
        · rcases zmod2_cases a2 with rfl | rfl
          · simp at ha2
            rw [← ha2, zero_dotProduct] at huv
            exact absurd huv (by decide)
          · simp only [one_smul] at ha2
            rw [← ha2, polar_self f M hf v] at huv
            exact absurd huv (by decide)
      have hune : u ≠ 0 := by
        intro h
        rw [h, zero_dotProduct] at huv
        exact absurd huv (by decide)
      have hvne : v ≠ 0 := by
        intro h
        rw [h, Matrix.mulVec_zero, dotProduct_zero] at huv
        exact absurd huv (by decide)
      have hSdim : Module.finrank (ZMod 2) S = 2 := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq
          (Submodule.span (ZMod 2) {u}) (Submodule.span (ZMod 2) {v})
        rw [hdisj_uv, finrank_bot, add_zero, finrank_span_singleton hune,
          finrank_span_singleton hvne] at h
        exact h
      have hdisj_kS : LinearMap.ker M.mulVecLin ⊓ S = ⊥ := by
        rw [eq_bot_iff]
        intro w hw
        rw [Submodule.mem_inf] at hw
        obtain ⟨hwk, hwS⟩ := hw
        rw [Submodule.mem_sup] at hwS
        obtain ⟨x1, hx1, x2, hx2, rfl⟩ := hwS
        rw [Submodule.mem_span_singleton] at hx1 hx2
        obtain ⟨a1, rfl⟩ := hx1
        obtain ⟨a2, rfl⟩ := hx2
        have hm0 : M.mulVec (a1 • u + a2 • v) = 0 := hwk
        have hdu : dotProduct u (M.mulVec (a1 • u + a2 • v)) = 0 := by rw [hm0, dotProduct_zero]
        have hdv : dotProduct v (M.mulVec (a1 • u + a2 • v)) = 0 := by rw [hm0, dotProduct_zero]
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
          smul_eq_mul, polar_self f M hf, huv, polar_symm f M hf v u] at hdu hdv
        have ha2 : a2 = 0 := by simpa using hdu
        have ha1 : a1 = 0 := by simpa using hdv
        rw [Submodule.mem_bot, ha1, ha2]
        simp
      have hker_le : Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) + 2 ≤
          Module.finrank (ZMod 2) (LinearMap.ker M'.mulVecLin) := by
        have hsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker M.mulVecLin) S
        rw [hdisj_kS, finrank_bot, add_zero, hSdim] at hsup
        have hmono := Submodule.finrank_mono hS_sub
        omega
      have hrM := rank_add_ker M
      have hrM' := rank_add_ker M'
      have hM'rk : M'.rank ≤ 2 * t := by omega
      obtain ⟨ps, a, b, hlen, hrep⟩ := ih f' M' hf' hM'rk
      refine ⟨(c1, c2) :: ps, a, b, by simp; omega, fun x => ?_⟩
      have hfx := hrep x
      dsimp only [f'] at hfx
      simp only [List.map_cons, List.sum_cons]
      have hadd := congrArg (· + dotProduct c1 x * dotProduct c2 x) hfx
      calc f x = f x + (dotProduct c1 x * dotProduct c2 x + dotProduct c1 x * dotProduct c2 x) := by
            rw [zmod2_add_self, add_zero]
        _ = (f x + dotProduct c1 x * dotProduct c2 x) + dotProduct c1 x * dotProduct c2 x := by ring
        _ = ((ps.map (fun p => dotProduct p.1 x * dotProduct p.2 x)).sum + dotProduct a x + b) +
            dotProduct c1 x * dotProduct c2 x := hadd
        _ = dotProduct c1 x * dotProduct c2 x +
            (ps.map (fun p => dotProduct p.1 x * dotProduct p.2 x)).sum + dotProduct a x + b := by
            ring

private def ReadsBackList (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

private theorem readsBackList_append (n : ℕ) (gs : List Gate) (g : Gate)
    (hrb : ReadsBackList n gs) (hg : ∀ i ∈ g.inputs, i < n + gs.length) :
    ReadsBackList n (gs ++ [g]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < gs.length
  · have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left hlt]
    rw [hget] at hi
    exact hrb j hlt i hi
  · have heq : j = gs.length := by omega
    subst heq
    have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
      simp
    rw [hget] at hi
    exact hg i hi

private theorem admGates_append (gs : List Gate) (g : Gate) (hgs : AdmGates gs)
    (hg : (g.op = .and ∧ g.inputs.length = 2) ∨
      (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)) :
    AdmGates (gs ++ [g]) := by
  intro h hh
  rcases List.mem_append.mp hh with hh | hh
  · exact hgs h hh
  · rw [List.mem_singleton] at hh
    rw [hh]
    exact hg

private theorem wiresOf_append_preserves {n : ℕ} (gs ext : List Gate) (x : Fin n → ZMod 2)
    (k : ℕ) (hk : k < n + gs.length) :
    (wiresOf (gs ++ ext) x).getD k false = (wiresOf gs x).getD k false := by
  induction ext using List.reverseRecOn with
  | nil => simp
  | append_singleton ext g ih =>
    rw [← List.append_assoc, wiresOf_append_singleton, getD_append_singleton_lt]
    · exact ih
    · rw [wiresOf_length, List.length_append]
      omega

private theorem build_const0 {n : ℕ} (gs : List Gate) (hrb : ReadsBackList n gs)
    (hadm : AdmGates gs) :
    ∃ (ext : List Gate) (w : ℕ),
      ReadsBackList n (gs ++ ext) ∧
      AdmGates (gs ++ ext) ∧
      andCost (gs ++ ext) = andCost gs ∧
      w < n + (gs ++ ext).length ∧
      ∀ x : Fin n → ZMod 2, b2z ((wiresOf (gs ++ ext) x).getD w false) = 0 := by
  let g1 : Gate := ⟨.mod 2, []⟩
  let g2 : Gate := ⟨.not, [n + gs.length]⟩
  refine ⟨[g1, g2], n + gs.length + 1, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : ReadsBackList n (gs ++ [g1]) :=
      readsBackList_append n gs g1 hrb (by simp [g1])
    have h2 : ReadsBackList n ((gs ++ [g1]) ++ [g2]) :=
      readsBackList_append n (gs ++ [g1]) g2 h1 (by simp [g2])
    simpa [List.append_assoc] using h2
  · have h1 : AdmGates (gs ++ [g1]) := admGates_append gs g1 hadm (Or.inr (Or.inl ⟨rfl, by simp [g1]⟩))
    have h2 : AdmGates ((gs ++ [g1]) ++ [g2]) :=
      admGates_append (gs ++ [g1]) g2 h1 (Or.inr (Or.inr ⟨rfl, by simp [g2]⟩))
    simpa [List.append_assoc] using h2
  · have h1 : gs ++ [g1, g2] = (gs ++ [g1]) ++ [g2] := by simp
    rw [h1, gate_ok_and_count_neg _ g2 (by simp [g2]), gate_ok_and_count_neg _ g1 (by simp [g1])]
  · simp; omega
  · intro x
    have h1 : gs ++ [g1, g2] = (gs ++ [g1]) ++ [g2] := by simp
    rw [h1, wiresOf_append_singleton]
    have hlen : (wiresOf (gs ++ [g1]) x).length = n + gs.length + 1 := by
      rw [wiresOf_length, List.length_append, List.length_singleton]
      omega
    rw [← hlen, getD_append_singleton_eq]
    simp only [g2, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    rw [wiresOf_append_singleton, ← wiresOf_length gs x, getD_append_singleton_eq]
    simp [g1, GateOp.eval, b2z]

private theorem build_not {n : ℕ} (gs : List Gate) (hrb : ReadsBackList n gs)
    (hadm : AdmGates gs) (w1 : ℕ) (hw1 : w1 < n + gs.length)
    (h1 : (Fin n → ZMod 2) → ZMod 2)
    (hv1 : ∀ x, b2z ((wiresOf gs x).getD w1 false) = h1 x) :
    ∃ (ext : List Gate) (w : ℕ),
      ReadsBackList n (gs ++ ext) ∧
      AdmGates (gs ++ ext) ∧
      andCost (gs ++ ext) = andCost gs ∧
      w < n + (gs ++ ext).length ∧
      ∀ x : Fin n → ZMod 2, b2z ((wiresOf (gs ++ ext) x).getD w false) = h1 x + 1 := by
  let g : Gate := ⟨.not, [w1]⟩
  refine ⟨[g], n + gs.length, ?_, ?_, ?_, ?_, ?_⟩
  · exact readsBackList_append n gs g hrb (by simp [g, hw1])
  · exact admGates_append gs g hadm (Or.inr (Or.inr ⟨rfl, by simp [g]⟩))
  · exact gate_ok_and_count_neg gs g (by simp [g])
  · simp
  · intro x
    rw [wiresOf_append_singleton, ← wiresOf_length gs x, getD_append_singleton_eq]
    simp only [g, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    rw [b2z_not, hv1 x]

private theorem build_xor {n : ℕ} (gs : List Gate) (hrb : ReadsBackList n gs)
    (hadm : AdmGates gs) (w1 w2 : ℕ) (hw1 : w1 < n + gs.length) (hw2 : w2 < n + gs.length)
    (h1 h2 : (Fin n → ZMod 2) → ZMod 2)
    (hv1 : ∀ x, b2z ((wiresOf gs x).getD w1 false) = h1 x)
    (hv2 : ∀ x, b2z ((wiresOf gs x).getD w2 false) = h2 x) :
    ∃ (ext : List Gate) (w : ℕ),
      ReadsBackList n (gs ++ ext) ∧
      AdmGates (gs ++ ext) ∧
      andCost (gs ++ ext) = andCost gs ∧
      w < n + (gs ++ ext).length ∧
      ∀ x : Fin n → ZMod 2, b2z ((wiresOf (gs ++ ext) x).getD w false) = h1 x + h2 x := by
  let g1 : Gate := ⟨.mod 2, [w1, w2]⟩
  let g2 : Gate := ⟨.not, [n + gs.length]⟩
  refine ⟨[g1, g2], n + gs.length + 1, ?_, ?_, ?_, ?_, ?_⟩
  · have ha : ReadsBackList n (gs ++ [g1]) :=
      readsBackList_append n gs g1 hrb (by intro i hi; simp [g1] at hi; rcases hi with rfl | rfl <;> assumption)
    have hb : ReadsBackList n ((gs ++ [g1]) ++ [g2]) :=
      readsBackList_append n (gs ++ [g1]) g2 ha (by simp [g2])
    simpa [List.append_assoc] using hb
  · have ha : AdmGates (gs ++ [g1]) := admGates_append gs g1 hadm (Or.inr (Or.inl ⟨rfl, by simp [g1]⟩))
    have hb : AdmGates ((gs ++ [g1]) ++ [g2]) :=
      admGates_append (gs ++ [g1]) g2 ha (Or.inr (Or.inr ⟨rfl, by simp [g2]⟩))
    simpa [List.append_assoc] using hb
  · have ha : gs ++ [g1, g2] = (gs ++ [g1]) ++ [g2] := by simp
    rw [ha, gate_ok_and_count_neg _ g2 (by simp [g2]), gate_ok_and_count_neg _ g1 (by simp [g1])]
  · simp; omega
  · intro x
    have ha : gs ++ [g1, g2] = (gs ++ [g1]) ++ [g2] := by simp
    rw [ha, wiresOf_append_singleton]
    have hlen : (wiresOf (gs ++ [g1]) x).length = n + gs.length + 1 := by
      rw [wiresOf_length, List.length_append, List.length_singleton]
      omega
    rw [← hlen, getD_append_singleton_eq]
    simp only [g2, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    rw [wiresOf_append_singleton, ← wiresOf_length gs x, getD_append_singleton_eq]
    simp only [g1, List.map_cons, List.map_nil, GateOp.eval]
    rw [b2z_not, b2z_mod2_two, hv1 x, hv2 x, add_assoc, add_assoc, zmod2_add_self, add_zero]

private theorem build_and {n : ℕ} (gs : List Gate) (hrb : ReadsBackList n gs)
    (hadm : AdmGates gs) (w1 w2 : ℕ) (hw1 : w1 < n + gs.length) (hw2 : w2 < n + gs.length)
    (h1 h2 : (Fin n → ZMod 2) → ZMod 2)
    (hv1 : ∀ x, b2z ((wiresOf gs x).getD w1 false) = h1 x)
    (hv2 : ∀ x, b2z ((wiresOf gs x).getD w2 false) = h2 x) :
    ∃ (ext : List Gate) (w : ℕ),
      ReadsBackList n (gs ++ ext) ∧
      AdmGates (gs ++ ext) ∧
      andCost (gs ++ ext) = andCost gs + 1 ∧
      w < n + (gs ++ ext).length ∧
      ∀ x : Fin n → ZMod 2, b2z ((wiresOf (gs ++ ext) x).getD w false) = h1 x * h2 x := by
  let g : Gate := ⟨.and, [w1, w2]⟩
  refine ⟨[g], n + gs.length, ?_, ?_, ?_, ?_, ?_⟩
  · exact readsBackList_append n gs g hrb (by intro i hi; simp [g] at hi; rcases hi with rfl | rfl <;> assumption)
  · exact admGates_append gs g hadm (Or.inl ⟨rfl, by simp [g]⟩)
  · exact gate_ok_and_count_pos gs g rfl
  · simp
  · intro x
    rw [wiresOf_append_singleton, ← wiresOf_length gs x, getD_append_singleton_eq]
    simp only [g, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq,
      Bool.and_true]
    rw [b2z_and, hv1 x, hv2 x]

private theorem build_linear_prefix {n : ℕ} (c : Fin n → ZMod 2) :
    ∀ (k : ℕ) (_hk : k ≤ n) (gs : List Gate) (_hrb : ReadsBackList n gs) (_hadm : AdmGates gs),
      ∃ (ext : List Gate) (w : ℕ),
        ReadsBackList n (gs ++ ext) ∧
        AdmGates (gs ++ ext) ∧
        andCost (gs ++ ext) = andCost gs ∧
        w < n + (gs ++ ext).length ∧
        ∀ x : Fin n → ZMod 2,
          b2z ((wiresOf (gs ++ ext) x).getD w false) =
            ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), c i * x i := by
  intro k
  induction k with
  | zero =>
    intro _ gs hrb hadm
    obtain ⟨ext, w, h1, h2, h3, h4, h5⟩ := build_const0 gs hrb hadm
    refine ⟨ext, w, h1, h2, h3, h4, fun x => ?_⟩
    rw [h5 x]
    simp
  | succ k ih =>
    intro hk gs hrb hadm
    obtain ⟨ext1, w1, hrb1, hadm1, hcost1, hw1, hv1⟩ := ih (by omega) gs hrb hadm
    let ik : Fin n := ⟨k, by omega⟩
    have hfilt : Finset.univ.filter (fun i : Fin n => i.val < k + 1) =
        insert ik (Finset.univ.filter (fun i : Fin n => i.val < k)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, ik]
      omega
    have hnotmem : ik ∉ Finset.univ.filter (fun i : Fin n => i.val < k) := by
      simp [ik]
    rcases zmod2_cases (c ik) with hc0 | hc1
    · refine ⟨ext1, w1, hrb1, hadm1, hcost1, hw1, fun x => ?_⟩
      rw [hv1 x, hfilt, Finset.sum_insert hnotmem, hc0, zero_mul, zero_add]
    · have hinput : ∀ x : Fin n → ZMod 2,
          b2z ((wiresOf (gs ++ ext1) x).getD k false) = x ik := by
        intro x
        have heq := wiresOf_append_preserves ([] : List Gate) (gs ++ ext1) x k (by simp; omega)
        simp only [List.nil_append] at heq
        rw [heq]
        unfold wiresOf inputVec
        simp [List.getD_eq_getElem?_getD, ik.isLt, b2z_decide_eq_one, ik]
      obtain ⟨ext2, w2, hrb2, hadm2, hcost2, hw2, hv2⟩ := build_xor (gs ++ ext1) hrb1 hadm1 w1 k
        hw1 (by omega) _ _ hv1 hinput
      refine ⟨ext1 ++ ext2, w2, ?_, ?_, ?_, ?_, fun x => ?_⟩
      · simpa [List.append_assoc] using hrb2
      · simpa [List.append_assoc] using hadm2
      · rw [← List.append_assoc, hcost2, hcost1]
      · simpa [List.append_assoc] using hw2
      · rw [← List.append_assoc, hv2 x, hfilt, Finset.sum_insert hnotmem, hc1, one_mul, add_comm]

private theorem build_linear {n : ℕ} (c : Fin n → ZMod 2) (gs : List Gate)
    (hrb : ReadsBackList n gs) (hadm : AdmGates gs) :
    ∃ (ext : List Gate) (w : ℕ),
      ReadsBackList n (gs ++ ext) ∧
      AdmGates (gs ++ ext) ∧
      andCost (gs ++ ext) = andCost gs ∧
      w < n + (gs ++ ext).length ∧
      ∀ x : Fin n → ZMod 2, b2z ((wiresOf (gs ++ ext) x).getD w false) = dotProduct c x := by
  obtain ⟨ext, w, h1, h2, h3, h4, h5⟩ := build_linear_prefix c n (le_refl n) gs hrb hadm
  refine ⟨ext, w, h1, h2, h3, h4, fun x => ?_⟩
  rw [h5 x]
  have hf : Finset.univ.filter (fun i : Fin n => i.val < n) = Finset.univ := by
    ext i
    simp [i.isLt]
  rw [hf]
  rfl

private theorem build_pairs {n : ℕ} :
    ∀ (ps : List ((Fin n → ZMod 2) × (Fin n → ZMod 2))) (gs : List Gate)
      (_hrb : ReadsBackList n gs) (_hadm : AdmGates gs),
      ∃ (ext : List Gate) (w : ℕ),
        ReadsBackList n (gs ++ ext) ∧
        AdmGates (gs ++ ext) ∧
        andCost (gs ++ ext) = andCost gs + ps.length ∧
        w < n + (gs ++ ext).length ∧
        ∀ x : Fin n → ZMod 2,
          b2z ((wiresOf (gs ++ ext) x).getD w false) =
            (ps.map (fun p => dotProduct p.1 x * dotProduct p.2 x)).sum := by
  intro ps
  induction ps with
  | nil =>
    intro gs hrb hadm
    obtain ⟨ext, w, h1, h2, h3, h4, h5⟩ := build_const0 gs hrb hadm
    refine ⟨ext, w, h1, h2, by simpa using h3, h4, fun x => by simpa using h5 x⟩
  | cons p ps ih =>
    intro gs hrb hadm
    obtain ⟨ext0, w0, hrb0, hadm0, hcost0, hw0, hv0⟩ := ih gs hrb hadm
    obtain ⟨ext1, w1, hrb1, hadm1, hcost1, hw1, hv1⟩ := build_linear p.1 (gs ++ ext0) hrb0 hadm0
    obtain ⟨ext2, w2, hrb2, hadm2, hcost2, hw2, hv2⟩ :=
      build_linear p.2 ((gs ++ ext0) ++ ext1) hrb1 hadm1
    have hw1' : w1 < n + (((gs ++ ext0) ++ ext1) ++ ext2).length := by
      simp only [List.length_append] at hw1 ⊢; omega
    have hv1' : ∀ x, b2z ((wiresOf (((gs ++ ext0) ++ ext1) ++ ext2) x).getD w1 false) =
        dotProduct p.1 x := by
      intro x
      rw [wiresOf_append_preserves _ ext2 x w1 hw1, hv1 x]
    obtain ⟨ext3, w3, hrb3, hadm3, hcost3, hw3, hv3⟩ :=
      build_and (((gs ++ ext0) ++ ext1) ++ ext2) hrb2 hadm2 w1 w2 hw1' hw2 _ _ hv1' hv2
    have hw0' : w0 < n + ((((gs ++ ext0) ++ ext1) ++ ext2) ++ ext3).length := by
      simp only [List.length_append] at hw0 ⊢; omega
    have hv0' : ∀ x, b2z ((wiresOf ((((gs ++ ext0) ++ ext1) ++ ext2) ++ ext3) x).getD w0 false) =
        (ps.map (fun q => dotProduct q.1 x * dotProduct q.2 x)).sum := by
      intro x
      have heq : (((gs ++ ext0) ++ ext1) ++ ext2) ++ ext3 =
          (gs ++ ext0) ++ (ext1 ++ ext2 ++ ext3) := by simp [List.append_assoc]
      rw [heq, wiresOf_append_preserves _ (ext1 ++ ext2 ++ ext3) x w0 hw0, hv0 x]
    obtain ⟨ext4, w4, hrb4, hadm4, hcost4, hw4, hv4⟩ :=
      build_xor ((((gs ++ ext0) ++ ext1) ++ ext2) ++ ext3) hrb3 hadm3 w3 w0 hw3 hw0' _ _ hv3 hv0'
    refine ⟨ext0 ++ ext1 ++ ext2 ++ ext3 ++ ext4, w4, ?_, ?_, ?_, ?_, fun x => ?_⟩
    · simpa [List.append_assoc] using hrb4
    · simpa [List.append_assoc] using hadm4
    · have heq : gs ++ (ext0 ++ ext1 ++ ext2 ++ ext3 ++ ext4) =
          ((((gs ++ ext0) ++ ext1) ++ ext2) ++ ext3) ++ ext4 := by simp [List.append_assoc]
      rw [heq, hcost4, hcost3, hcost2, hcost1, hcost0, List.length_cons]
      omega
    · simpa [List.append_assoc] using hw4
    · have heq : gs ++ (ext0 ++ ext1 ++ ext2 ++ ext3 ++ ext4) =
          ((((gs ++ ext0) ++ ext1) ++ ext2) ++ ext3) ++ ext4 := by simp [List.append_assoc]
      rw [heq, hv4 x, List.map_cons, List.sum_cons]

private theorem backward_construct {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (t : ℕ) (hle : M.rank ≤ 2 * t) :
    ∃ C : Circuit,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      AdmGates C.gates ∧
      andCost C.gates ≤ t ∧
      ∀ x : Fin n → ZMod 2, C.eval (inputVec x) = decide (f x = 1) := by
  obtain ⟨ps, a, b, hpslen, hrep⟩ := quad_decomp t f M hf hle
  have hrb0 : ReadsBackList n [] := fun j hj => by simp at hj
  have hadm0 : AdmGates [] := fun g hg => by simp at hg
  obtain ⟨gs1, w1, hrb1, hadm1, hcost1, hw1, hv1⟩ := build_pairs ps [] hrb0 hadm0
  simp only [List.nil_append] at hrb1 hadm1 hcost1 hw1 hv1
  obtain ⟨ext2, w2, hrb2, hadm2, hcost2, hw2, hv2⟩ := build_linear a gs1 hrb1 hadm1
  have hw1' : w1 < n + (gs1 ++ ext2).length := by
    simp only [List.length_append] at hw1 ⊢; omega
  have hv1' : ∀ x, b2z ((wiresOf (gs1 ++ ext2) x).getD w1 false) =
      (ps.map (fun p => dotProduct p.1 x * dotProduct p.2 x)).sum := by
    intro x
    rw [wiresOf_append_preserves gs1 ext2 x w1 hw1, hv1 x]
  obtain ⟨ext3, w3, hrb3, hadm3, hcost3, hw3, hv3⟩ :=
    build_xor (gs1 ++ ext2) hrb2 hadm2 w1 w2 hw1' hw2 _ _ hv1' hv2
  rcases zmod2_cases b with rfl | rfl
  · refine ⟨⟨(gs1 ++ ext2) ++ ext3, w3⟩, hrb3, hadm3, ?_, fun x => ?_⟩
    · rw [hcost3, hcost2, hcost1]
      simp [andCost]
      omega
    · apply bool_eq_decide_of_b2z
      change b2z ((wiresOf ((gs1 ++ ext2) ++ ext3) x).getD w3 false) = f x
      rw [hv3 x, hrep x, add_zero]
  · obtain ⟨ext4, w4, hrb4, hadm4, hcost4, _, hv4⟩ :=
      build_not ((gs1 ++ ext2) ++ ext3) hrb3 hadm3 w3 hw3 _ hv3
    refine ⟨⟨((gs1 ++ ext2) ++ ext3) ++ ext4, w4⟩, hrb4, hadm4, ?_, fun x => ?_⟩
    · rw [hcost4, hcost3, hcost2, hcost1]
      simp [andCost]
      omega
    · apply bool_eq_decide_of_b2z
      change b2z ((wiresOf (((gs1 ++ ext2) ++ ext3) ++ ext4) x).getD w4 false) = f x
      rw [hv4 x, hrep x]

theorem main_aux (n : ℕ) (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (t : ℕ) :
    (∃ C : Circuit,
      (PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ AdmGates C.gates) ∧
      andCost C.gates ≤ t ∧
      ∀ x : Fin n → ZMod 2, C.eval (inputVec x) = decide (f x = 1)) ↔ M.rank ≤ 2 * t := by
  constructor
  · rintro ⟨C, ⟨_, hadm⟩, hcost, heval⟩
    exact forward_bound f M hf t C hadm hcost heval
  · intro hle
    obtain ⟨C, hrb, hadm, hcost, heval⟩ := backward_construct f M hf t hle
    exact ⟨C, ⟨hrb, hadm⟩, hcost, heval⟩

end PEqualNP.Outside.L_lib_506_aux

theorem PEqualNP.Outside.L_lib_506 : ∀ n : ℕ,
  let V := Fin n → ZMod 2
  let admissible := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
    (∀ g ∈ C.gates,
      (g.op = .and ∧ g.inputs.length = 2) ∨
      (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
      (g.op = .not ∧ g.inputs.length = 1))
  let cost := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    C.gates.countP (fun g => @decide (g.op = .and) (Classical.propDecidable _))
  let input := fun (x : V) => List.ofFn (fun i : Fin n => decide (x i = 1))
  ∀ (f : V → ZMod 2) (M : Matrix (Fin n) (Fin n) (ZMod 2)),
    (∀ x y : V, f (x+y) + f x + f y + f 0 = dotProduct x (M.mulVec y)) →
    ∀ t : ℕ, (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      admissible C ∧ cost C ≤ t ∧ ∀ x : V, C.eval (input x) = decide (f x = 1)) ↔
      M.rank ≤ 2*t := by
  intro n V admissible cost input f M hf t
  exact PEqualNP.Outside.L_lib_506_aux.main_aux n f M hf t
