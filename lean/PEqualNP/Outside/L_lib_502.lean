import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_502_aux

open PEqualNP.CircuitLowerBounds

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem b2z_decide_eq_one (t : ZMod 2) : b2z (decide (t = 1)) = t := by
  revert t
  decide

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

private theorem gate_ok_and_count_pos (gs : List Gate) (g : Gate) (h : g.op = .and) :
    (gs ++ [g]).countP (fun x => @decide (x.op = .and) (Classical.propDecidable _)) =
      gs.countP (fun x => @decide (x.op = .and) (Classical.propDecidable _)) + 1 := by
  rw [List.countP_append, List.countP_cons, List.countP_nil]
  simp [h]

private theorem gate_ok_and_count_neg (gs : List Gate) (g : Gate) (h : g.op ≠ .and) :
    (gs ++ [g]).countP (fun x => @decide (x.op = .and) (Classical.propDecidable _)) =
      gs.countP (fun x => @decide (x.op = .and) (Classical.propDecidable _)) := by
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

private theorem gates_affine_restrict {n : ℕ} (gs : List Gate)
    (hgs : ∀ g ∈ gs,
      (g.op = .and ∧ g.inputs.length = 2) ∨
      (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)) :
    ∃ (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (p : Fin n → ZMod 2),
      n ≤ Module.finrank (ZMod 2) U +
        gs.countP (fun g => @decide (g.op = .and) (Classical.propDecidable _)) ∧
      ∀ k : ℕ, ∃ (a : Fin n → ZMod 2) (b : ZMod 2),
        ∀ x ∈ U, b2z ((wiresOf gs (p + x)).getD k false) = dotProduct a (p + x) + b := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨⊤, 0, ?_, ?_⟩
    · simp [finrank_top]
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
    have hgs' : ∀ h ∈ gs,
        (h.op = .and ∧ h.inputs.length = 2) ∨
        (h.op = .mod 2 ∧ h.inputs.length ≤ 2) ∨
        (h.op = .not ∧ h.inputs.length = 1) :=
      fun h hh => hgs h (List.mem_append_left [g] hh)
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

theorem main_aux (n : ℕ) (C : Circuit) (f : (Fin n → ZMod 2) → ZMod 2)
    (hC : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      (∀ g ∈ C.gates,
        (g.op = .and ∧ g.inputs.length = 2) ∨
        (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
        (g.op = .not ∧ g.inputs.length = 1)))
    (hf : ∀ x : Fin n → ZMod 2,
      C.eval (List.ofFn (fun i : Fin n => decide (x i = 1))) = decide (f x = 1)) :
    ∃ (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (p a : Fin n → ZMod 2) (b : ZMod 2),
      n ≤ Module.finrank (ZMod 2) U +
        C.gates.countP (fun g => @decide (g.op = .and) (Classical.propDecidable _)) ∧
      ∀ x ∈ U, f (p + x) = dotProduct a (p + x) + b := by
  obtain ⟨U, p, hdim, haff⟩ := gates_affine_restrict C.gates hC.2
  obtain ⟨a, b, hab⟩ := haff C.output
  refine ⟨U, p, a, b, hdim, ?_⟩
  intro x hx
  have h1 := hab x hx
  have h2 := hf (p + x)
  have h3 : (wiresOf C.gates (p + x)).getD C.output false =
      C.eval (List.ofFn (fun i : Fin n => decide ((p + x) i = 1))) := rfl
  rw [h3, h2, b2z_decide_eq_one] at h1
  exact h1

end PEqualNP.Outside.L_lib_502_aux

theorem PEqualNP.Outside.L_lib_502 :
∀ n : ℕ,
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
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (f : V → ZMod 2),
    admissible C → (∀ x : V, C.eval (input x) = decide (f x = 1)) →
    ∃ (U : Submodule (ZMod 2) V) (p a : V) (b : ZMod 2),
      n ≤ Module.finrank (ZMod 2) U + cost C ∧
      ∀ x ∈ U, f (p+x) = dotProduct a (p+x) + b := by
  intro n V admissible cost input C f hC hf
  exact PEqualNP.Outside.L_lib_502_aux.main_aux n C f hC hf
