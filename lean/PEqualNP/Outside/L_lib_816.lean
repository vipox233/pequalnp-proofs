import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_816_aux

private abbrev F2 := ZMod 2
private abbrev V (k : ℕ) := Fin k → F2
private abbrev Z (t : ℕ) := Fin t → Bool

private lemma z2_eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma z2_add_self (a : F2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma z2_sub_eq_add (a b : F2) : a - b = a + b := by
  rcases z2_eq_zero_or_one a with rfl | rfl <;> rcases z2_eq_zero_or_one b with rfl | rfl <;> decide

private lemma z2_ne_zero_iff (a : F2) : a ≠ 0 ↔ a = 1 := by
  fin_cases a
  · exact ⟨fun h => absurd rfl h, fun h => absurd h zero_ne_one⟩
  · exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩

private lemma dot_add_right {k : ℕ} (a x y : V k) :
    dotProduct a (x + y) = dotProduct a x + dotProduct a y := by
  simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma dot_add_left {k : ℕ} (a b x : V k) :
    dotProduct (a + b) x = dotProduct a x + dotProduct b x := by
  simp only [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma dot_smul_right {k : ℕ} (a : V k) (c : F2) (x : V k) :
    dotProduct a (c • x) = c * dotProduct a x := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

private lemma dot_sub_right {k : ℕ} (a x y : V k) :
    dotProduct a (x - y) = dotProduct a x + dotProduct a y := by
  have h : x - y = x + y := by funext i; exact z2_sub_eq_add (x i) (y i)
  rw [h, dot_add_right]

private def dotLin {k : ℕ} (a : V k) : V k →ₗ[F2] F2 where
  toFun := fun x => dotProduct a x
  map_add' := fun x y => dot_add_right a x y
  map_smul' := fun c x => by simp only [RingHom.id_apply, smul_eq_mul]; exact dot_smul_right a c x

private def enc (k t : ℕ) (x : V k) (z : Z t) : List Bool :=
  List.ofFn (fun j : Fin k => decide (x j = 1)) ++ List.ofFn z

private lemma enc_length (k t : ℕ) (x : V k) (z : Z t) : (enc k t x z).length = k + t := by
  simp [enc]

private def wiresOf (gs : List PEqualNP.CircuitLowerBounds.Gate) (inp : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp

private lemma wiresOf_nil (inp : List Bool) : wiresOf [] inp = inp := rfl

private lemma wiresOf_append_singleton (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (g : PEqualNP.CircuitLowerBounds.Gate) (inp : List Bool) :
    wiresOf (gs ++ [g]) inp =
      wiresOf gs inp ++ [g.op.eval (g.inputs.map fun i => (wiresOf gs inp).getD i false)] := by
  simp [wiresOf]

private lemma wiresOf_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (inp : List Bool) :
    (wiresOf gs inp).length = inp.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresOf]
  | append_singleton gs g ih =>
    rw [wiresOf_append_singleton, List.length_append, List.length_singleton, ih, List.length_append,
      List.length_singleton]
    omega

private lemma getD_append_singleton (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false =
      if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases hlt : w < l.length
  · simp only [hlt, ↓reduceIte, List.getElem?_append_left hlt]
  · by_cases heq : w = l.length
    · subst heq
      simp only [lt_irrefl, ↓reduceIte, List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
    · have hgt : l.length + 1 ≤ w := by omega
      have hge : l.length ≤ w := by omega
      have hnone : (l ++ [b])[w]? = none := List.getElem?_eq_none (by simp; omega)
      simp only [hlt, heq, ↓reduceIte, hnone, Option.getD_none]

private lemma getD_enc (k t : ℕ) (x : V k) (z : Z t) (w : ℕ) :
    (enc k t x z).getD w false =
      if hw : w < k then decide (x ⟨w, hw⟩ = 1)
      else if hwt : w < k + t then z ⟨w - k, by omega⟩
      else false := by
  simp only [enc, List.getD_eq_getElem?_getD]
  by_cases hw : w < k
  · have hlen : w < (List.ofFn (fun j : Fin k => decide (x j = 1))).length := by simp [hw]
    rw [List.getElem?_append_left hlen, List.getElem?_ofFn]
    simp only [hw, ↓reduceDIte, Option.getD_some]
  · by_cases hwt : w < k + t
    · have hge : (List.ofFn (fun j : Fin k => decide (x j = 1))).length ≤ w := by simp; omega
      rw [List.getElem?_append_right hge, List.length_ofFn, List.getElem?_ofFn]
      have hsub : w - k < t := by omega
      simp only [hw, hwt, hsub, ↓reduceDIte, Option.getD_some]
    · have hnone : (List.ofFn (fun j : Fin k => decide (x j = 1)) ++ List.ofFn z)[w]? = none :=
        List.getElem?_eq_none (by simp; omega)
      simp only [hw, hwt, ↓reduceDIte, hnone, Option.getD_none]

private structure Piece (k t : ℕ) where
  U : Submodule F2 (V k)
  p : Z t → V k
  aw : ℕ → V k
  cw : ℕ → Z t → F2

private def Piece.Valid {k t : ℕ} (gs : List PEqualNP.CircuitLowerBounds.Gate) (P : Piece k t) : Prop :=
  ∀ (z : Z t) (u : V k), u ∈ P.U → ∀ w : ℕ,
    (wiresOf gs (enc k t (P.p z + u) z)).getD w false = decide (dotProduct (P.aw w) u + P.cw w z = 1)

private def Piece.updateWire {k t : ℕ} (P : Piece k t) (n : ℕ) (a : V k) (c : Z t → F2) : Piece k t where
  U := P.U
  p := P.p
  aw := fun w => if w = n then a else P.aw w
  cw := fun w z => if w = n then c z else P.cw w z

private lemma Piece.valid_updateWire {k t : ℕ} {gs : List PEqualNP.CircuitLowerBounds.Gate}
    {g : PEqualNP.CircuitLowerBounds.Gate} {P : Piece k t}
    (hP : P.Valid gs) (a : V k) (c : Z t → F2)
    (hnew : ∀ (z : Z t) (u : V k), u ∈ P.U →
      g.op.eval (g.inputs.map fun i => (wiresOf gs (enc k t (P.p z + u) z)).getD i false) =
        decide (dotProduct a u + c z = 1)) :
    (P.updateWire (k + t + gs.length) a c).Valid (gs ++ [g]) := by
  intro z u hu w
  dsimp only [Piece.updateWire] at hu ⊢
  have hlen : (wiresOf gs (enc k t (P.p z + u) z)).length = k + t + gs.length := by
    rw [wiresOf_length, enc_length]
  rw [wiresOf_append_singleton, getD_append_singleton, hlen]
  by_cases hlt : w < k + t + gs.length
  · have hne : w ≠ k + t + gs.length := by omega
    simp only [hlt, hne, ↓reduceIte]
    exact hP z u hu w
  · by_cases heq : w = k + t + gs.length
    · subst heq
      simp only [lt_irrefl, ↓reduceIte]
      exact hnew z u hu
    · simp only [hlt, heq, ↓reduceIte]
      have hge : (wiresOf gs (enc k t (P.p z + u) z)).length ≤ w := by omega
      have hnone : (wiresOf gs (enc k t (P.p z + u) z)).getD w false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
      have := hP z u hu w
      rw [hnone] at this
      exact this

private lemma finrank_inf_ker_dotLin {k : ℕ} (U : Submodule F2 (V k)) (a : V k)
    (u0 : V k) (hu0 : u0 ∈ U) (hdot : dotProduct a u0 = 1) :
    Module.finrank F2 (U ⊓ LinearMap.ker (dotLin a) : Submodule F2 (V k)) + 1 = Module.finrank F2 U := by
  let L : U →ₗ[F2] F2 := (dotLin a).comp U.subtype
  have hsurj : LinearMap.range L = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨c • ⟨u0, hu0⟩, ?_⟩
    rw [map_smul]
    dsimp only [L, dotLin, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hdot, smul_eq_mul, mul_one]
  have hrk : Module.finrank F2 (LinearMap.range L) + Module.finrank F2 (LinearMap.ker L) =
      Module.finrank F2 U := LinearMap.finrank_range_add_finrank_ker L
  rw [hsurj, finrank_top, Module.finrank_self] at hrk
  have hmap : Submodule.map U.subtype (LinearMap.ker L) = U ⊓ LinearMap.ker (dotLin a) := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf, Submodule.subtype_apply]
    constructor
    · rintro ⟨⟨y, hy⟩, hyker, rfl⟩
      exact ⟨hy, hyker⟩
    · rintro ⟨hxU, hxker⟩
      exact ⟨⟨x, hxU⟩, hxker, rfl⟩
  have hfin_eq : Module.finrank F2 (U ⊓ LinearMap.ker (dotLin a) : Submodule F2 (V k)) =
      Module.finrank F2 (LinearMap.ker L) := by
    rw [← hmap]
    exact (Submodule.equivMapOfInjective U.subtype Subtype.val_injective (LinearMap.ker L)).symm.finrank_eq
  omega

private def splitBranch {k t : ℕ} (P : Piece k t) (a : V k) (c0 : Z t → F2) (u0 : V k) (b : F2) :
    Piece k t where
  U := P.U ⊓ LinearMap.ker (dotLin a)
  p := fun z => P.p z + (c0 z + b) • u0
  aw := P.aw
  cw := fun w z => P.cw w z + (c0 z + b) * dotProduct (P.aw w) u0

private lemma splitBranch_valid {k t : ℕ} {gs : List PEqualNP.CircuitLowerBounds.Gate}
    {P : Piece k t} (hP : P.Valid gs) (a : V k) (c0 : Z t → F2) (u0 : V k) (hu0 : u0 ∈ P.U) (b : F2) :
    (splitBranch P a c0 u0 b).Valid gs := by
  intro z u hu w
  dsimp only [splitBranch]
  have huP : u ∈ P.U := hu.1
  have hcomb : (c0 z + b) • u0 + u ∈ P.U := P.U.add_mem (P.U.smul_mem _ hu0) huP
  have hadd : P.p z + (c0 z + b) • u0 + u = P.p z + ((c0 z + b) • u0 + u) := add_assoc _ _ _
  rw [hadd, hP z ((c0 z + b) • u0 + u) hcomb w]
  congr 1
  rw [dot_add_right, dot_smul_right]
  ring

private lemma splitBranch_eval_const {k t : ℕ} (P : Piece k t) (a : V k) (c0 : Z t → F2)
    (u0 : V k) (hdot : dotProduct a u0 = 1) (b : F2) (z : Z t) (u : V k)
    (hu : u ∈ (splitBranch P a c0 u0 b).U) :
    dotProduct a ((c0 z + b) • u0 + u) + c0 z = b := by
  have huKer : dotProduct a u = 0 := hu.2
  rw [dot_add_right, dot_smul_right, hdot, mul_one, huKer, add_zero]
  have hcc := z2_add_self (c0 z)
  linear_combination hcc

private lemma splitBranch_partition {k t : ℕ} (P : Piece k t) (a : V k) (c0 : Z t → F2)
    (u0 : V k) (hu0 : u0 ∈ P.U) (hdot : dotProduct a u0 = 1) (z : Z t) (x : V k) :
    (x - (splitBranch P a c0 u0 0).p z ∈ (splitBranch P a c0 u0 0).U ∨
      x - (splitBranch P a c0 u0 1).p z ∈ (splitBranch P a c0 u0 1).U) ↔
      x - P.p z ∈ P.U := by
  constructor
  · rintro (h0 | h1)
    · have hsub : x - P.p z = (x - (splitBranch P a c0 u0 0).p z) + (c0 z + 0) • u0 := by
        dsimp only [splitBranch]; abel
      rw [hsub]
      exact P.U.add_mem h0.1 (P.U.smul_mem _ hu0)
    · have hsub : x - P.p z = (x - (splitBranch P a c0 u0 1).p z) + (c0 z + 1) • u0 := by
        dsimp only [splitBranch]; abel
      rw [hsub]
      exact P.U.add_mem h1.1 (P.U.smul_mem _ hu0)
  · intro hx
    let b : F2 := dotProduct a (x - P.p z) + c0 z
    have hmem : x - (splitBranch P a c0 u0 b).p z ∈ (splitBranch P a c0 u0 b).U := by
      dsimp only [splitBranch]
      refine ⟨?_, ?_⟩
      · have hsub : x - (P.p z + (c0 z + b) • u0) = (x - P.p z) - (c0 z + b) • u0 := by abel
        rw [hsub]
        exact P.U.sub_mem hx (P.U.smul_mem _ hu0)
      · show dotProduct a (x - (P.p z + (c0 z + b) • u0)) = 0
        have hsub : x - (P.p z + (c0 z + b) • u0) = (x - P.p z) - (c0 z + b) • u0 := by abel
        rw [hsub, dot_sub_right, dot_smul_right, hdot, mul_one]
        dsimp only [b]
        have h1 := z2_add_self (dotProduct a (x - P.p z))
        have h2 := z2_add_self (c0 z)
        linear_combination h1 + h2
    rcases z2_eq_zero_or_one b with hb0 | hb1
    · left; simpa [hb0] using hmem
    · right; simpa [hb1] using hmem

private lemma splitBranch_disjoint {k t : ℕ} (P : Piece k t) (a : V k) (c0 : Z t → F2)
    (u0 : V k) (hdot : dotProduct a u0 = 1) (z : Z t) (x : V k) :
    ¬(x - (splitBranch P a c0 u0 0).p z ∈ (splitBranch P a c0 u0 0).U ∧
      x - (splitBranch P a c0 u0 1).p z ∈ (splitBranch P a c0 u0 1).U) := by
  rintro ⟨h0, h1⟩
  have hd0 : dotProduct a (x - (P.p z + (c0 z + 0) • u0)) = 0 := h0.2
  have hd1 : dotProduct a (x - (P.p z + (c0 z + 1) • u0)) = 0 := h1.2
  have hdiff : (x - (P.p z + (c0 z + 0) • u0)) - (x - (P.p z + (c0 z + 1) • u0)) = u0 := by
    have h1' : (c0 z + 1) • u0 - (c0 z + 0) • u0 = (1 : F2) • u0 := by
      rw [← sub_smul]; congr 1; ring
    calc (x - (P.p z + (c0 z + 0) • u0)) - (x - (P.p z + (c0 z + 1) • u0))
        = (c0 z + 1) • u0 - (c0 z + 0) • u0 := by abel
      _ = (1 : F2) • u0 := h1'
      _ = u0 := one_smul F2 u0
  have hzero : dotProduct a u0 = 0 := by
    rw [← hdiff, dot_sub_right, hd0, hd1, add_zero]
  rw [hdot] at hzero
  exact one_ne_zero hzero

private lemma exists_nonzero_dot {k : ℕ} (U : Submodule F2 (V k)) (hpos : 0 < Module.finrank F2 U) :
    ∃ (a u0 : V k), u0 ∈ U ∧ dotProduct a u0 = 1 := by
  have hne : U ≠ ⊥ := by
    intro hbot; rw [hbot, finrank_bot] at hpos; omega
  obtain ⟨u0, hu0, hu0_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hex : ∃ j : Fin k, u0 j = 1 := by
    by_contra hnot; push Not at hnot
    apply hu0_ne; funext j
    rcases z2_eq_zero_or_one (u0 j) with h0 | h1
    · exact h0
    · exact absurd h1 (hnot j)
  obtain ⟨j, hj⟩ := hex
  refine ⟨Pi.single j 1, u0, hu0, ?_⟩
  simp only [dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, hj]

private lemma bool_eq_decide_ite (b : Bool) :
    b = decide ((if b = true then (1 : F2) else 0) = 1) := by
  cases b <;> decide

private lemma eval_mod2_zero :
    PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [] = decide ((1 : F2) = 1) := by decide

private lemma eval_mod2_one (a : F2) :
    PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [decide (a = 1)] = decide (a + 1 = 1) := by
  rcases z2_eq_zero_or_one a with rfl | rfl <;> decide

private lemma eval_mod2_two (a b : F2) :
    PEqualNP.CircuitLowerBounds.GateOp.eval (.mod 2) [decide (a = 1), decide (b = 1)] =
      decide (a + b + 1 = 1) := by
  rcases z2_eq_zero_or_one a with rfl | rfl <;> rcases z2_eq_zero_or_one b with rfl | rfl <;> decide

private lemma eval_not_one (a : F2) :
    PEqualNP.CircuitLowerBounds.GateOp.eval .not [decide (a = 1)] = decide (a + 1 = 1) := by
  rcases z2_eq_zero_or_one a with rfl | rfl <;> decide

private noncomputable def isNL (g : PEqualNP.CircuitLowerBounds.Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

private lemma step_affine_piece {k t : ℕ} {gs : List PEqualNP.CircuitLowerBounds.Gate}
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hg_len : g.inputs.length ≤ 2)
    (hg_op : g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))
    (hnl : isNL g = false)
    (P : Piece k t) (hP : P.Valid gs) :
    ∃ P' : Piece k t, P'.U = P.U ∧ P'.p = P.p ∧ P'.Valid (gs ++ [g]) := by
  have hnot_nl : ¬((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) := by
    simpa [isNL] using hnl
  rcases hg_op with hop | hop | hop | ⟨hop, hlen1⟩
  · cases hgi : g.inputs with
    | nil =>
      refine ⟨P.updateWire (k + t + gs.length) 0 (fun _ => 1), rfl, rfl, ?_⟩
      apply P.valid_updateWire hP
      intro z u _
      simp [hop, hgi, PEqualNP.CircuitLowerBounds.GateOp.eval]
    | cons i rest =>
      cases rest with
      | nil =>
        refine ⟨P.updateWire (k + t + gs.length) (P.aw i) (P.cw i), rfl, rfl, ?_⟩
        apply P.valid_updateWire hP
        intro z u hu
        simp only [hop, hgi, List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
          List.all_cons, List.all_nil, id_eq, Bool.and_true]
        exact hP z u hu i
      | cons j rest2 =>
        cases rest2 with
        | nil =>
          exfalso; apply hnot_nl; exact ⟨Or.inl hop, by simp [hgi]⟩
        | cons _ _ =>
          simp [hgi] at hg_len
  · cases hgi : g.inputs with
    | nil =>
      refine ⟨P.updateWire (k + t + gs.length) 0 (fun _ => 0), rfl, rfl, ?_⟩
      apply P.valid_updateWire hP
      intro z u _
      simp [hop, hgi, PEqualNP.CircuitLowerBounds.GateOp.eval]
    | cons i rest =>
      cases rest with
      | nil =>
        refine ⟨P.updateWire (k + t + gs.length) (P.aw i) (P.cw i), rfl, rfl, ?_⟩
        apply P.valid_updateWire hP
        intro z u hu
        simp only [hop, hgi, List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
          List.any_cons, List.any_nil, id_eq, Bool.or_false]
        exact hP z u hu i
      | cons j rest2 =>
        cases rest2 with
        | nil =>
          exfalso; apply hnot_nl; exact ⟨Or.inr hop, by simp [hgi]⟩
        | cons _ _ =>
          simp [hgi] at hg_len
  · cases hgi : g.inputs with
    | nil =>
      refine ⟨P.updateWire (k + t + gs.length) 0 (fun _ => 1), rfl, rfl, ?_⟩
      apply P.valid_updateWire hP
      intro z u _
      simp only [hop, hgi, List.map_nil, zero_dotProduct, zero_add]
      exact eval_mod2_zero
    | cons i rest =>
      cases rest with
      | nil =>
        refine ⟨P.updateWire (k + t + gs.length) (P.aw i) (fun z => P.cw i z + 1), rfl, rfl, ?_⟩
        apply P.valid_updateWire hP
        intro z u hu
        simp only [hop, hgi, List.map_cons, List.map_nil, hP z u hu i]
        rw [eval_mod2_one, add_assoc]
      | cons j rest2 =>
        cases rest2 with
        | nil =>
          refine ⟨P.updateWire (k + t + gs.length) (P.aw i + P.aw j) (fun z => P.cw i z + P.cw j z + 1),
            rfl, rfl, ?_⟩
          apply P.valid_updateWire hP
          intro z u hu
          simp only [hop, hgi, List.map_cons, List.map_nil, hP z u hu i, hP z u hu j]
          rw [eval_mod2_two, dot_add_left]
          congr 1; ring
        | cons _ _ =>
          simp [hgi] at hg_len
  · cases hgi : g.inputs with
    | nil => simp [hgi] at hlen1
    | cons i rest =>
      cases rest with
      | nil =>
        refine ⟨P.updateWire (k + t + gs.length) (P.aw i) (fun z => P.cw i z + 1), rfl, rfl, ?_⟩
        apply P.valid_updateWire hP
        intro z u hu
        simp only [hop, hgi, List.map_cons, List.map_nil, hP z u hu i]
        rw [eval_not_one, add_assoc]
      | cons _ _ => simp [hgi] at hlen1

private lemma step_nl_zero_dim {k t : ℕ} {gs : List PEqualNP.CircuitLowerBounds.Gate}
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (P : Piece k t) (hP : P.Valid gs) (hdim : Module.finrank F2 P.U = 0) :
    ∃ P' : Piece k t, P'.U = P.U ∧ P'.p = P.p ∧ P'.Valid (gs ++ [g]) := by
  have hbot : P.U = ⊥ := Submodule.finrank_eq_zero.mp hdim
  let valZ : Z t → F2 := fun z =>
    if g.op.eval (g.inputs.map fun i => decide (P.cw i z = 1)) then 1 else 0
  refine ⟨P.updateWire (k + t + gs.length) 0 valZ, rfl, rfl, ?_⟩
  apply P.valid_updateWire hP
  intro z u hu
  rw [hbot] at hu
  have hu0 : u = 0 := hu
  subst hu0
  have hmap : (g.inputs.map fun i => (wiresOf gs (enc k t (P.p z + 0) z)).getD i false) =
      (g.inputs.map fun i => decide (P.cw i z = 1)) := by
    refine List.map_congr_left fun i _ => ?_
    rw [hP z 0 (P.U.zero_mem) i, dotProduct_zero, zero_add]
  rw [hmap, zero_dotProduct, zero_add]
  exact bool_eq_decide_ite _

private lemma step_nl_split {k t : ℕ} {gs : List PEqualNP.CircuitLowerBounds.Gate}
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hnl : isNL g = true)
    (P : Piece k t) (hP : P.Valid gs) (hpos : 0 < Module.finrank F2 P.U) :
    ∃ (P0 P1 : Piece k t),
      Module.finrank F2 P0.U + 1 = Module.finrank F2 P.U ∧
      Module.finrank F2 P1.U + 1 = Module.finrank F2 P.U ∧
      P0.Valid (gs ++ [g]) ∧ P1.Valid (gs ++ [g]) ∧
      (∀ z x, (x - P0.p z ∈ P0.U ∨ x - P1.p z ∈ P1.U) ↔ x - P.p z ∈ P.U) ∧
      (∀ z x, ¬(x - P0.p z ∈ P0.U ∧ x - P1.p z ∈ P1.U)) := by
  classical
  have hnl' : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by simpa [isNL] using hnl
  rcases hnl' with ⟨hop, hlen2⟩
  cases hgi : g.inputs with
  | nil => simp [hgi] at hlen2
  | cons i rest =>
    cases rest with
    | nil => simp [hgi] at hlen2
    | cons j rest2 =>
      cases rest2 with
      | cons _ _ => simp [hgi] at hlen2
      | nil =>
        by_cases h1 : ∃ u0 ∈ P.U, dotProduct (P.aw i) u0 = 1
        · obtain ⟨u0, hu0, hdot⟩ := h1
          let B0 := splitBranch P (P.aw i) (P.cw i) u0 0
          let B1 := splitBranch P (P.aw i) (P.cw i) u0 1
          have hB0v : B0.Valid gs := splitBranch_valid hP _ _ u0 hu0 0
          have hB1v : B1.Valid gs := splitBranch_valid hP _ _ u0 hu0 1
          have hdimB : Module.finrank F2 (P.U ⊓ LinearMap.ker (dotLin (P.aw i)) : Submodule F2 (V k)) + 1 =
              Module.finrank F2 P.U := finrank_inf_ker_dotLin P.U (P.aw i) u0 hu0 hdot
          have hval0 : ∀ (z : Z t) (u : V k), u ∈ B0.U →
              (wiresOf gs (enc k t (B0.p z + u) z)).getD i false = false := by
            intro z u hu
            have h1' := hB0v z u hu i
            have h2' := splitBranch_eval_const P (P.aw i) (P.cw i) u0 hdot 0 z u hu
            rw [h1']
            have harg : dotProduct (B0.aw i) u + B0.cw i z =
                dotProduct (P.aw i) ((P.cw i z + 0) • u0 + u) + P.cw i z := by
              dsimp only [B0, splitBranch]; rw [dot_add_right, dot_smul_right]; ring
            rw [harg, h2']; decide
          have hval1 : ∀ (z : Z t) (u : V k), u ∈ B1.U →
              (wiresOf gs (enc k t (B1.p z + u) z)).getD i false = true := by
            intro z u hu
            have h1' := hB1v z u hu i
            have h2' := splitBranch_eval_const P (P.aw i) (P.cw i) u0 hdot 1 z u hu
            rw [h1']
            have harg : dotProduct (B1.aw i) u + B1.cw i z =
                dotProduct (P.aw i) ((P.cw i z + 1) • u0 + u) + P.cw i z := by
              dsimp only [B1, splitBranch]; rw [dot_add_right, dot_smul_right]; ring
            rw [harg, h2']; decide
          rcases hop with hand | hor
          · let P0 := B0.updateWire (k + t + gs.length) 0 (fun _ => 0)
            let P1 := B1.updateWire (k + t + gs.length) (B1.aw j) (B1.cw j)
            refine ⟨P0, P1, hdimB, hdimB, ?_, ?_,
              splitBranch_partition P _ _ u0 hu0 hdot, splitBranch_disjoint P _ _ u0 hdot⟩
            · apply B0.valid_updateWire hB0v
              intro z u hu
              simp only [hand, hgi, List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
                List.all_cons, List.all_nil, id_eq, hval0 z u hu, Bool.false_and, zero_dotProduct, add_zero]
              decide
            · apply B1.valid_updateWire hB1v
              intro z u hu
              simp only [hand, hgi, List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
                List.all_cons, List.all_nil, id_eq, hval1 z u hu, Bool.true_and, Bool.and_true]
              exact hB1v z u hu j
          · let P0 := B0.updateWire (k + t + gs.length) (B0.aw j) (B0.cw j)
            let P1 := B1.updateWire (k + t + gs.length) 0 (fun _ => 1)
            refine ⟨P0, P1, hdimB, hdimB, ?_, ?_,
              splitBranch_partition P _ _ u0 hu0 hdot, splitBranch_disjoint P _ _ u0 hdot⟩
            · apply B0.valid_updateWire hB0v
              intro z u hu
              simp only [hor, hgi, List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
                List.any_cons, List.any_nil, id_eq, hval0 z u hu, Bool.false_or, Bool.or_false]
              exact hB0v z u hu j
            · apply B1.valid_updateWire hB1v
              intro z u hu
              simp only [hor, hgi, List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
                List.any_cons, List.any_nil, id_eq, hval1 z u hu, Bool.true_or, zero_dotProduct, zero_add]
              decide
        · have hi_zero : ∀ u ∈ P.U, dotProduct (P.aw i) u = 0 := by
            intro u hu
            rcases z2_eq_zero_or_one (dotProduct (P.aw i) u) with h0 | h1'
            · exact h0
            · exact absurd ⟨u, hu, h1'⟩ h1
          by_cases h2 : ∃ u0 ∈ P.U, dotProduct (P.aw j) u0 = 1
          · obtain ⟨u0, hu0, hdot⟩ := h2
            let B0 := splitBranch P (P.aw j) (P.cw j) u0 0
            let B1 := splitBranch P (P.aw j) (P.cw j) u0 1
            have hB0v : B0.Valid gs := splitBranch_valid hP _ _ u0 hu0 0
            have hB1v : B1.Valid gs := splitBranch_valid hP _ _ u0 hu0 1
            have hdimB : Module.finrank F2 (P.U ⊓ LinearMap.ker (dotLin (P.aw j)) : Submodule F2 (V k)) + 1 =
                Module.finrank F2 P.U := finrank_inf_ker_dotLin P.U (P.aw j) u0 hu0 hdot
            have hval0 : ∀ (z : Z t) (u : V k), u ∈ B0.U →
                (wiresOf gs (enc k t (B0.p z + u) z)).getD j false = false := by
              intro z u hu
              have h1' := hB0v z u hu j
              have h2' := splitBranch_eval_const P (P.aw j) (P.cw j) u0 hdot 0 z u hu
              rw [h1']
              have harg : dotProduct (B0.aw j) u + B0.cw j z =
                  dotProduct (P.aw j) ((P.cw j z + 0) • u0 + u) + P.cw j z := by
                dsimp only [B0, splitBranch]; rw [dot_add_right, dot_smul_right]; ring
              rw [harg, h2']; decide
            have hval1 : ∀ (z : Z t) (u : V k), u ∈ B1.U →
                (wiresOf gs (enc k t (B1.p z + u) z)).getD j false = true := by
              intro z u hu
              have h1' := hB1v z u hu j
              have h2' := splitBranch_eval_const P (P.aw j) (P.cw j) u0 hdot 1 z u hu
              rw [h1']
              have harg : dotProduct (B1.aw j) u + B1.cw j z =
                  dotProduct (P.aw j) ((P.cw j z + 1) • u0 + u) + P.cw j z := by
                dsimp only [B1, splitBranch]; rw [dot_add_right, dot_smul_right]; ring
              rw [harg, h2']; decide
            have hvali0 : ∀ (z : Z t) (u : V k), u ∈ B0.U →
                (wiresOf gs (enc k t (B0.p z + u) z)).getD i false = decide (P.cw i z = 1) := by
              intro z u hu
              rw [hB0v z u hu i]
              exact congrArg (fun x => decide (x = 1)) (by
                dsimp only [B0, splitBranch]
                rw [hi_zero u hu.1, hi_zero u0 hu0]
                ring)
            have hvali1 : ∀ (z : Z t) (u : V k), u ∈ B1.U →
                (wiresOf gs (enc k t (B1.p z + u) z)).getD i false = decide (P.cw i z = 1) := by
              intro z u hu
              rw [hB1v z u hu i]
              exact congrArg (fun x => decide (x = 1)) (by
                dsimp only [B1, splitBranch]
                rw [hi_zero u hu.1, hi_zero u0 hu0]
                ring)
            rcases hop with hand | hor
            · let P0 := B0.updateWire (k + t + gs.length) 0 (fun _ => 0)
              let P1 := B1.updateWire (k + t + gs.length) 0 (P.cw i)
              refine ⟨P0, P1, hdimB, hdimB, ?_, ?_,
                splitBranch_partition P _ _ u0 hu0 hdot, splitBranch_disjoint P _ _ u0 hdot⟩
              · apply B0.valid_updateWire hB0v
                intro z u hu
                simp only [hand, hgi, List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
                  List.all_cons, List.all_nil, id_eq, hval0 z u hu, Bool.false_and, Bool.and_false,
                  zero_dotProduct, add_zero]
                decide
              · apply B1.valid_updateWire hB1v
                intro z u hu
                simp only [hand, hgi, List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
                  List.all_cons, List.all_nil, id_eq, hval1 z u hu, hvali1 z u hu, Bool.and_true,
                  zero_dotProduct, zero_add]
            · let P0 := B0.updateWire (k + t + gs.length) 0 (P.cw i)
              let P1 := B1.updateWire (k + t + gs.length) 0 (fun _ => 1)
              refine ⟨P0, P1, hdimB, hdimB, ?_, ?_,
                splitBranch_partition P _ _ u0 hu0 hdot, splitBranch_disjoint P _ _ u0 hdot⟩
              · apply B0.valid_updateWire hB0v
                intro z u hu
                simp only [hor, hgi, List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
                  List.any_cons, List.any_nil, id_eq, hval0 z u hu, hvali0 z u hu, Bool.or_false,
                  zero_dotProduct, zero_add]
              · apply B1.valid_updateWire hB1v
                intro z u hu
                simp only [hor, hgi, List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
                  List.any_cons, List.any_nil, id_eq, hval1 z u hu, Bool.true_or, Bool.or_true,
                  zero_dotProduct, zero_add]
                decide
          · have hj_zero : ∀ u ∈ P.U, dotProduct (P.aw j) u = 0 := by
              intro u hu
              rcases z2_eq_zero_or_one (dotProduct (P.aw j) u) with h0 | h1'
              · exact h0
              · exact absurd ⟨u, hu, h1'⟩ h2
            let valZ : Z t → F2 := fun z =>
              if g.op.eval [decide (P.cw i z = 1), decide (P.cw j z = 1)] then 1 else 0
            let Pmid := P.updateWire (k + t + gs.length) 0 valZ
            have hPmid_v : Pmid.Valid (gs ++ [g]) := by
              apply P.valid_updateWire hP
              intro z u hu
              simp only [hgi, List.map_cons, List.map_nil, hP z u hu i, hP z u hu j,
                hi_zero u hu, hj_zero u hu, zero_dotProduct, zero_add]
              exact bool_eq_decide_ite _
            obtain ⟨a', u0, hu0, hdot⟩ := exists_nonzero_dot P.U hpos
            let P0 := splitBranch Pmid a' (fun _ => 0) u0 0
            let P1 := splitBranch Pmid a' (fun _ => 0) u0 1
            have hdimB : Module.finrank F2 (P.U ⊓ LinearMap.ker (dotLin a') : Submodule F2 (V k)) + 1 =
                Module.finrank F2 P.U := finrank_inf_ker_dotLin P.U a' u0 hu0 hdot
            exact ⟨P0, P1, hdimB, hdimB,
              splitBranch_valid hPmid_v a' (fun _ => 0) u0 hu0 0,
              splitBranch_valid hPmid_v a' (fun _ => 0) u0 hu0 1,
              splitBranch_partition Pmid a' (fun _ => 0) u0 hu0 hdot,
              splitBranch_disjoint Pmid a' (fun _ => 0) u0 hdot⟩

private lemma partition_build (k t : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hgs : ∀ g ∈ gs, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) :
    let b := min (gs.countP isNL) k
    ∃ ps : Fin (2 ^ b) → Piece k t,
      (∀ i, Module.finrank F2 (ps i).U = k - b) ∧
      (∀ (z : Z t) (x : V k), ∃! i : Fin (2 ^ b), x - (ps i).p z ∈ (ps i).U) ∧
      (∀ i, (ps i).Valid gs) := by
  induction gs using List.reverseRecOn with
  | nil =>
    dsimp only
    have hb0 : min (([] : List PEqualNP.CircuitLowerBounds.Gate).countP isNL) k = 0 := by simp
    let P0 : Piece k t :=
      { U := ⊤
        p := fun _ => 0
        aw := fun w => if hw : w < k then Pi.single ⟨w, hw⟩ 1 else 0
        cw := fun w z => if hw : w < k then 0 else if hwt : w < k + t then if z ⟨w - k, by omega⟩ then 1 else 0 else 0 }
    refine ⟨fun _ => P0, ?_, ?_, ?_⟩
    · intro _; dsimp only [P0]; rw [finrank_top, Module.finrank_fin_fun]; omega
    · intro z x
      refine ⟨⟨0, by simp⟩, by dsimp only [P0]; exact Submodule.mem_top, fun j _ => ?_⟩
      apply Fin.ext
      have hj := j.isLt
      have hpow1 : 2 ^ min (([] : List PEqualNP.CircuitLowerBounds.Gate).countP isNL) k = 1 := by simp
      dsimp only
      omega
    · intro _ z u _ w
      dsimp only [P0]
      rw [wiresOf_nil, zero_add, getD_enc]
      by_cases hw : w < k
      · simp only [hw, ↓reduceDIte, add_zero]
        have hdot : dotProduct (Pi.single (⟨w, hw⟩ : Fin k) (1 : F2)) u = u ⟨w, hw⟩ := by
          simp only [dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
            Finset.mem_univ, ↓reduceIte]
        rw [hdot]
      · by_cases hwt : w < k + t
        · simp only [hw, hwt, ↓reduceDIte, zero_dotProduct, zero_add]
          exact bool_eq_decide_ite _
        · simp only [hw, hwt, ↓reduceDIte, zero_dotProduct, zero_add]
          decide
  | append_singleton gs g ih =>
    dsimp only
    have hgs' : ∀ g' ∈ gs, g'.inputs.length ≤ 2 ∧
        (g'.op = .and ∨ g'.op = .or ∨ g'.op = .mod 2 ∨ (g'.op = .not ∧ g'.inputs.length = 1)) :=
      fun g' hg' => hgs g' (List.mem_append_left _ hg')
    have hg := hgs g (List.mem_append_right _ (List.mem_singleton_self g))
    obtain ⟨ps, hdim, hpart, hval⟩ := ih hgs'
    let s := gs.countP isNL
    let b := min s k
    have hcnt : (gs ++ [g]).countP isNL = s + if isNL g then 1 else 0 := by
      simp [s, List.countP_append]
    cases hnl : isNL g with
    | false =>
      have hb_eq : min ((gs ++ [g]).countP isNL) k = b := by rw [hcnt, hnl]; simp [b]
      have hstep : ∀ i : Fin (2 ^ b), ∃ P' : Piece k t,
          P'.U = (ps i).U ∧ P'.p = (ps i).p ∧ P'.Valid (gs ++ [g]) :=
        fun i => step_affine_piece g hg.1 hg.2 hnl (ps i) (hval i)
      choose ps' hU' hp' hval' using hstep
      let e : Fin (2 ^ min ((gs ++ [g]).countP isNL) k) ≃ Fin (2 ^ b) :=
        finCongr (by rw [hb_eq])
      refine ⟨fun idx => ps' (e idx), ?_, ?_, ?_⟩
      · intro idx; rw [hU', hdim, hb_eq]
      · intro z x
        obtain ⟨i, hi, huniq⟩ := hpart z x
        refine ⟨e.symm i, ?_, ?_⟩
        · simp only [Equiv.apply_symm_apply, hU', hp']; exact hi
        · intro j hj
          rw [hU', hp'] at hj
          have hej : e j = i := huniq (e j) hj
          rw [← hej, Equiv.symm_apply_apply]
      · intro idx; exact hval' (e idx)
    | true =>
      by_cases hsk : s < k
      · have hb_eq : min ((gs ++ [g]).countP isNL) k = b + 1 := by
          rw [hcnt, hnl]; simp only [↓reduceIte, b]; omega
        have hb_def : min (gs.countP isNL) k = b := rfl
        have h2b : 2 ^ min (gs.countP isNL) k = 2 ^ b := rfl
        have hpos : ∀ i : Fin (2 ^ b), 0 < Module.finrank F2 (ps i).U := by
          intro i; have hdi := hdim i; dsimp only [b, s] at *; omega
        have hstep : ∀ i : Fin (2 ^ b), ∃ P0 P1 : Piece k t,
            Module.finrank F2 P0.U + 1 = Module.finrank F2 (ps i).U ∧
            Module.finrank F2 P1.U + 1 = Module.finrank F2 (ps i).U ∧
            P0.Valid (gs ++ [g]) ∧ P1.Valid (gs ++ [g]) ∧
            (∀ z x, (x - P0.p z ∈ P0.U ∨ x - P1.p z ∈ P1.U) ↔ x - (ps i).p z ∈ (ps i).U) ∧
            (∀ z x, ¬(x - P0.p z ∈ P0.U ∧ x - P1.p z ∈ P1.U)) :=
          fun i => step_nl_split g hnl (ps i) (hval i) (hpos i)
        choose P0 P1 hdim0 hdim1 hval0 hval1 hcov hdisj using hstep
        have hpow : 2 ^ min ((gs ++ [g]).countP isNL) k = 2 ^ b + 2 ^ b := by
          rw [hb_eq, pow_succ, mul_two]
        let ps' : Fin (2 ^ min ((gs ++ [g]).countP isNL) k) → Piece k t := fun idx =>
          if hlt : idx.val < 2 ^ b then P0 ⟨idx.val, hlt⟩
          else P1 ⟨idx.val - 2 ^ b, by have := idx.isLt; omega⟩
        refine ⟨ps', ?_, ?_, ?_⟩
        · intro idx
          by_cases hlt : idx.val < 2 ^ b
          · have hps : ps' idx = P0 ⟨idx.val, hlt⟩ := by dsimp only [ps']; simp only [hlt, ↓reduceDIte]
            rw [hps]
            have h1 := hdim0 ⟨idx.val, hlt⟩
            have h2 := hdim ⟨idx.val, hlt⟩
            omega
          · have hsublt : idx.val - 2 ^ b < 2 ^ b := by have := idx.isLt; omega
            have hps : ps' idx = P1 ⟨idx.val - 2 ^ b, hsublt⟩ := by dsimp only [ps']; simp only [hlt, ↓reduceDIte]
            rw [hps]
            have h1 := hdim1 ⟨idx.val - 2 ^ b, hsublt⟩
            have h2 := hdim ⟨idx.val - 2 ^ b, hsublt⟩
            omega
        · intro z x
          obtain ⟨i, hi, huniq⟩ := hpart z x
          have hi_lt : i.val < 2 ^ b := by have := i.isLt; omega
          have h01 := (hcov i z x).mpr hi
          have hidx_uniq : ∀ j : Fin (2 ^ min ((gs ++ [g]).countP isNL) k),
              x - (ps' j).p z ∈ (ps' j).U →
              (j.val < 2 ^ b ∧ j.val = i.val ∧ x - (P0 i).p z ∈ (P0 i).U) ∨
              (¬j.val < 2 ^ b ∧ j.val - 2 ^ b = i.val ∧ x - (P1 i).p z ∈ (P1 i).U) := by
            intro j hj
            dsimp only [ps'] at hj
            by_cases hlt : j.val < 2 ^ b
            · simp only [hlt, ↓reduceDIte] at hj
              have hm : x - (ps ⟨j.val, hlt⟩).p z ∈ (ps ⟨j.val, hlt⟩).U :=
                (hcov ⟨j.val, hlt⟩ z x).mp (Or.inl hj)
              have heq : (⟨j.val, hlt⟩ : Fin (2 ^ b)) = i := huniq _ hm
              have hv : j.val = i.val := congrArg Fin.val heq
              left; exact ⟨hlt, hv, by rwa [← heq]⟩
            · simp only [hlt, ↓reduceDIte] at hj
              have hsublt : j.val - 2 ^ b < 2 ^ b := by have := j.isLt; omega
              have hm : x - (ps ⟨j.val - 2 ^ b, hsublt⟩).p z ∈ (ps ⟨j.val - 2 ^ b, hsublt⟩).U :=
                (hcov ⟨j.val - 2 ^ b, hsublt⟩ z x).mp (Or.inr hj)
              have heq : (⟨j.val - 2 ^ b, hsublt⟩ : Fin (2 ^ b)) = i := huniq _ hm
              have hv : j.val - 2 ^ b = i.val := congrArg Fin.val heq
              right; exact ⟨hlt, hv, by rwa [← heq]⟩
          rcases h01 with hx0 | hx1
          · refine ⟨⟨i.val, by omega⟩, ?_, ?_⟩
            · dsimp only [ps']; simp only [hi_lt, ↓reduceDIte]; exact hx0
            · intro j hj
              rcases hidx_uniq j hj with ⟨_, hv, _⟩ | ⟨_, _, hx1'⟩
              · exact Fin.ext hv
              · exact absurd ⟨hx0, hx1'⟩ (hdisj i z x)
          · refine ⟨⟨i.val + 2 ^ b, by omega⟩, ?_, ?_⟩
            · dsimp only [ps']
              have hnotlt : ¬(i.val + 2 ^ b < 2 ^ b) := by omega
              simp only [hnotlt, ↓reduceDIte, Nat.add_sub_cancel]
              exact hx1
            · intro j hj
              rcases hidx_uniq j hj with ⟨_, _, hx0'⟩ | ⟨hnlt, hv, _⟩
              · exact absurd ⟨hx0', hx1⟩ (hdisj i z x)
              · exact Fin.ext (by dsimp only; omega)
        · intro idx
          dsimp only [ps']
          by_cases hlt : idx.val < 2 ^ b
          · simp only [hlt, ↓reduceDIte]; exact hval0 ⟨idx.val, hlt⟩
          · simp only [hlt, ↓reduceDIte]; exact hval1 ⟨idx.val - 2 ^ b, by have := idx.isLt; omega⟩
      · have hb_eq : min ((gs ++ [g]).countP isNL) k = b := by
          rw [hcnt, hnl]; simp only [↓reduceIte, b]; omega
        have hb_def : min (gs.countP isNL) k = b := rfl
        have hzero : ∀ i : Fin (2 ^ b), Module.finrank F2 (ps i).U = 0 := by
          intro i; have hdi := hdim i; dsimp only [b, s] at *; omega
        have hstep : ∀ i : Fin (2 ^ b), ∃ P' : Piece k t,
            P'.U = (ps i).U ∧ P'.p = (ps i).p ∧ P'.Valid (gs ++ [g]) :=
          fun i => step_nl_zero_dim g (ps i) (hval i) (hzero i)
        choose ps' hU' hp' hval' using hstep
        let e : Fin (2 ^ min ((gs ++ [g]).countP isNL) k) ≃ Fin (2 ^ b) :=
          finCongr (by rw [hb_eq])
        refine ⟨fun idx => ps' (e idx), ?_, ?_, ?_⟩
        · intro idx; rw [hU', hdim, hb_eq]
        · intro z x
          obtain ⟨i, hi, huniq⟩ := hpart z x
          refine ⟨e.symm i, ?_, ?_⟩
          · simp only [Equiv.apply_symm_apply, hU', hp']; exact hi
          · intro j hj
            rw [hU', hp'] at hj
            have hej : e j = i := huniq (e j) hj
            rw [← hej, Equiv.symm_apply_apply]
        · intro idx; exact hval' (e idx)

private lemma main_816 (k t : ℕ)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (_hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + t) C)
    (hC : ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) :
    let s := C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
    let b := min s k
    let I := Fin (2 ^ b)
    ∃ (U : I → Submodule F2 (V k)) (a : I → V k) (p : I → Z t → V k) (c : I → Z t → F2),
      (∀ i, Module.finrank F2 (U i) = k - b) ∧
      (∀ (z : Z t) (x : V k), ∃! i : I, x - p i z ∈ U i) ∧
      ∀ (i : I) (z : Z t) (u : V k), u ∈ U i →
        C.eval (List.ofFn (fun j : Fin k => decide ((p i z + u) j = 1)) ++ List.ofFn z) =
          decide (dotProduct (a i) u + c i z = 1) := by
  intro s b I
  obtain ⟨ps, hdim, hpart, hval⟩ := partition_build k t C.gates hC
  refine ⟨fun i => (ps i).U, fun i => (ps i).aw C.output, fun i => (ps i).p,
    fun i => (ps i).cw C.output, hdim, hpart, ?_⟩
  intro i z u hu
  exact hval i z u hu C.output

end PEqualNP.Outside.L_lib_816_aux

theorem PEqualNP.Outside.L_lib_816 : ∀ (k t : ℕ),
  let F := ZMod 2
  let V := Fin k → F
  let Z := Fin t → Bool
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+t) C →
    (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))) →
    let s := C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
    let b := min s k
    let I := Fin (2^b)
    ∃ (U : I → Submodule F V) (a : I → V) (p : I → Z → V) (c : I → Z → F),
      (∀ i, Module.finrank F (U i) = k-b) ∧
      (∀ (z : Z) (x : V), ∃! i : I, x-p i z ∈ U i) ∧
      ∀ (i : I) (z : Z) (u : V), u ∈ U i →
        C.eval (List.ofFn (fun j : Fin k => decide ((p i z + u) j = 1)) ++ List.ofFn z) =
          decide (dotProduct (a i) u + c i z = 1) := by
  intro k t F V Z C hrb hC
  exact PEqualNP.Outside.L_lib_816_aux.main_816 k t C hrb hC
