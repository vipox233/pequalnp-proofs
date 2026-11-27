import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_507

-- Adapted from ovolee37's L-lib-501 proof in open-goat/pequalnp-proofs PR 38961, Apache-2.0.
-- Changes: rename declarations for use as local helpers of L-lib-507.

namespace AgreementAux

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma zmod2_add_one_ne (a : ZMod 2) : a + 1 ≠ a := by
  rcases zmod2_cases a with rfl | rfl <;> decide

private lemma zmod2_ne_iff_eq_add_one (a b : ZMod 2) : a ≠ b ↔ a = b + 1 := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

private lemma dotProduct_of_linearMap {n : ℕ} (ψ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (v : Fin n → ZMod 2) :
    dotProduct (fun i => ψ (Pi.single i 1)) v = ψ v := by
  have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ZMod 2) := by
    funext j
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ j]
    simp
  conv_rhs => rw [hv]
  rw [map_sum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

private lemma exists_annihilator {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (v : Fin n → ZMod 2) (hv : v ∉ U) :
    ∃ u : Fin n → ZMod 2, (∀ x ∈ U, dotProduct u x = 0) ∧ dotProduct u v = 1 := by
  classical
  let q : (Fin n → ZMod 2) ⧸ U := U.mkQ v
  have hq : q ≠ 0 := by
    intro h
    exact hv ((Submodule.Quotient.mk_eq_zero U).mp h)
  let K : Submodule (ZMod 2) ((Fin n → ZMod 2) ⧸ U) := Submodule.span (ZMod 2) {q}
  have hmemK : ∀ z ∈ K, z = 0 ∨ z = q := by
    intro z hz
    rcases Submodule.mem_span_singleton.mp hz with ⟨a, rfl⟩
    rcases zmod2_cases a with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  have hqq : q + q = 0 := by
    have h2 : (1 + 1 : ZMod 2) • q = 0 := by
      have : (1 + 1 : ZMod 2) = 0 := by decide
      rw [this, zero_smul]
    rwa [add_smul, one_smul] at h2
  let coord : K →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun z => if (z : (Fin n → ZMod 2) ⧸ U) = 0 then 0 else 1,
       map_add' := by
         intro x y
         rcases hmemK x.1 x.2 with hx | hx <;> rcases hmemK y.1 y.2 with hy | hy
         · simp [hx, hy]
         · simp [hx, hy, hq]
         · simp [hx, hy, hq]
         · simp only [Submodule.coe_add, hx, hy, hqq, ↓reduceIte, hq]
           decide,
       map_smul' := by
         intro c x
         rcases zmod2_cases c with rfl | rfl
         · simp
         · simp }
  obtain ⟨W, hKW⟩ := Submodule.exists_isCompl K
  let proj : ((Fin n → ZMod 2) ⧸ U) →ₗ[ZMod 2] K := Submodule.projectionOnto K W hKW
  let ψ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := (coord.comp proj).comp U.mkQ
  refine ⟨fun i => ψ (Pi.single i 1), ?_, ?_⟩
  · intro x hx
    rw [dotProduct_of_linearMap]
    change coord (proj (U.mkQ x)) = 0
    have h0 : U.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hx
    rw [h0, map_zero, map_zero]
  · rw [dotProduct_of_linearMap]
    change coord (proj q) = 1
    have hqK : q ∈ K := Submodule.subset_span (Set.mem_singleton q)
    have hproj : proj q = ⟨q, hqK⟩ := Submodule.projectionOnto_apply_left hKW ⟨q, hqK⟩
    rw [hproj]
    simp [coord, hq]

private lemma card_flat {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (p : Fin n → ZMod 2) [DecidablePred (fun y : Fin n → ZMod 2 => y - p ∈ U)] :
    ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun y => y - p ∈ U)).card =
      2 ^ (Module.finrank (ZMod 2) U) := by
  classical
  have hbij :
      ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun y => y - p ∈ U)).card =
        Fintype.card U := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun y hy => (⟨y - p, (Finset.mem_filter.mp hy).2⟩ : U))
      (fun _ _ => Finset.mem_univ _)
      (fun y1 _ y2 _ h => by
        have h1 : y1 - p = y2 - p := congrArg Subtype.val h
        exact sub_left_inj.mp h1)
      (fun x _ => ⟨p + x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [x.2]⟩,
        by ext i; simp⟩)
  rw [hbij, Module.card_eq_pow_finrank (K := ZMod 2) (V := U), ZMod.card]

private lemma main_bound (n : ℕ) (f : (Fin n → ZMod 2) → ZMod 2)
    (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (p c : Fin n → ZMod 2) (e : ZMod 2)
    (hagree : ∀ x ∈ U, f (p + x) = dotProduct c (p + x) + e) :
    ∃ (a : Fin n → ZMod 2) (b : ZMod 2),
      2 * ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x => f x ≠ dotProduct a x + b)).card +
        2 ^ (Module.finrank (ZMod 2) U) ≤ 2 ^ n := by
  classical
  let V := Fin n → ZMod 2
  let Uperp : Finset V := Finset.univ.filter (fun u : V => ∀ x ∈ U, dotProduct u x = 0)
  have h0_mem : (0 : V) ∈ Uperp := by
    simp [Uperp]
  have hUperp_add : ∀ u1 u2 : V, u1 ∈ Uperp → u2 ∈ Uperp → u1 + u2 ∈ Uperp := by
    intro u1 u2 h1 h2
    simp only [Uperp, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2 ⊢
    intro x hx
    rw [add_dotProduct, h1 x hx, h2 x hx, add_zero]
  let g : V → V → ZMod 2 := fun u y => dotProduct (c + u) y + (e + dotProduct u p)
  let F : Finset V := Finset.univ.filter (fun y : V => y - p ∈ U)
  have hF_zero : ∀ y ∈ F, ∀ u ∈ Uperp, f y = g u y := by
    intro y hy u hu
    have hyp : y - p ∈ U := (Finset.mem_filter.mp hy).2
    have hu_ann : dotProduct u (y - p) = 0 := (Finset.mem_filter.mp hu).2 (y - p) hyp
    have hy_eq : p + (y - p) = y := add_sub_cancel p y
    have hf : f y = dotProduct c y + e := by
      have h := hagree (y - p) hyp
      rwa [hy_eq] at h
    rw [hf]
    dsimp only [g]
    rw [add_dotProduct]
    have hup : dotProduct u y = dotProduct u p := by
      have hsub : dotProduct u (y - p) = dotProduct u y - dotProduct u p := dotProduct_sub u y p
      rw [hsub] at hu_ann
      exact sub_eq_zero.mp hu_ann
    rw [hup]
    have h2 : dotProduct u p + dotProduct u p = 0 := zmod2_add_self _
    calc
      dotProduct c y + e = dotProduct c y + (e + (dotProduct u p + dotProduct u p)) := by
        rw [h2, add_zero]
      _ = dotProduct c y + dotProduct u p + (e + dotProduct u p) := by ring
  have hnotF_half : ∀ y ∉ F,
      2 * (Uperp.filter (fun u => f y ≠ g u y)).card = Uperp.card := by
    intro y hy
    have hnotU : y - p ∉ U := by
      intro hmem
      exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hmem⟩)
    obtain ⟨u0, hu0_ann, hu0_one⟩ := exists_annihilator U (y - p) hnotU
    have hu0_mem : u0 ∈ Uperp := Finset.mem_filter.mpr ⟨Finset.mem_univ u0, hu0_ann⟩
    have hshift : ∀ u : V, g (u + u0) y = g u y + 1 := by
      intro u
      dsimp only [g]
      have h1 : dotProduct (c + (u + u0)) y = dotProduct (c + u) y + dotProduct u0 y := by
        rw [← add_assoc, add_dotProduct]
      have h2 : dotProduct (u + u0) p = dotProduct u p + dotProduct u0 p := add_dotProduct u u0 p
      have h3 : dotProduct u0 y + dotProduct u0 p = 1 := by
        have hsub : dotProduct u0 (y - p) = dotProduct u0 y - dotProduct u0 p := dotProduct_sub u0 y p
        rw [zmod2_sub_eq_add] at hsub
        rw [← hsub, hu0_one]
      rw [h1, h2]
      calc
        dotProduct (c + u) y + dotProduct u0 y + (e + (dotProduct u p + dotProduct u0 p))
          = dotProduct (c + u) y + (e + dotProduct u p) + (dotProduct u0 y + dotProduct u0 p) := by ring
        _ = dotProduct (c + u) y + (e + dotProduct u p) + 1 := by rw [h3]
    have hpart : (Uperp.filter (fun u => f y ≠ g u y)).card =
        (Uperp.filter (fun u => ¬f y ≠ g u y)).card := by
      refine Finset.card_bij (fun u _ => u + u0) ?_ ?_ ?_
      · intro u hu
        rcases Finset.mem_filter.mp hu with ⟨huU, hne⟩
        refine Finset.mem_filter.mpr ⟨hUperp_add u u0 huU hu0_mem, ?_⟩
        rw [hshift u, not_not]
        exact (zmod2_ne_iff_eq_add_one (f y) (g u y)).mp hne
      · intro u1 _ u2 _ h
        exact add_right_cancel h
      · intro u hu
        rcases Finset.mem_filter.mp hu with ⟨huU, heq⟩
        rw [not_not] at heq
        refine ⟨u + u0, Finset.mem_filter.mpr ⟨hUperp_add u u0 huU hu0_mem, ?_⟩, ?_⟩
        · rw [hshift u, heq]
          exact (zmod2_add_one_ne (g u y)).symm
        · funext i
          change (u i + u0 i) + u0 i = u i
          have : u0 i + u0 i = 0 := zmod2_add_self (u0 i)
          rw [add_assoc, this, add_zero]
    have htot := Finset.card_filter_add_card_filter_not (s := Uperp) (p := fun u => f y ≠ g u y)
    omega
  have hsum :
      ∑ u ∈ Uperp, 2 * ((Finset.univ : Finset V).filter (fun y => f y ≠ g u y)).card =
        (2 ^ n - 2 ^ (Module.finrank (ZMod 2) U)) * Uperp.card := by
    have hswap :
        ∑ u ∈ Uperp, ((Finset.univ : Finset V).filter (fun y => f y ≠ g u y)).card =
          ∑ y : V, (Uperp.filter (fun u => f y ≠ g u y)).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    rw [← Finset.mul_sum, hswap, Finset.mul_sum]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y : V => y ∈ F)]
    have hpart1 :
        ∑ y ∈ Finset.univ.filter (fun y : V => y ∈ F),
          2 * (Uperp.filter (fun u => f y ≠ g u y)).card = 0 := by
      refine Finset.sum_eq_zero fun y hy => ?_
      have hyF : y ∈ F := (Finset.mem_filter.mp hy).2
      have hemp : Uperp.filter (fun u => f y ≠ g u y) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro u hu
        rw [not_not]
        exact hF_zero y hyF u hu
      rw [hemp, Finset.card_empty, mul_zero]
    have hpart2 :
        ∑ y ∈ Finset.univ.filter (fun y : V => ¬y ∈ F),
          2 * (Uperp.filter (fun u => f y ≠ g u y)).card =
        (2 ^ n - 2 ^ (Module.finrank (ZMod 2) U)) * Uperp.card := by
      have hcongr :
          ∑ y ∈ Finset.univ.filter (fun y : V => ¬y ∈ F),
            2 * (Uperp.filter (fun u => f y ≠ g u y)).card =
          ∑ _y ∈ Finset.univ.filter (fun y : V => ¬y ∈ F), Uperp.card := by
        refine Finset.sum_congr rfl fun y hy => ?_
        exact hnotF_half y (Finset.mem_filter.mp hy).2
      rw [hcongr, Finset.sum_const, smul_eq_mul]
      congr 1
      have hfilt : Finset.univ.filter (fun y : V => ¬y ∈ F) = Finset.univ \ F := by
        ext y
        simp
      rw [hfilt, Finset.card_sdiff_of_subset (Finset.subset_univ F),
        Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, card_flat U p]
    rw [hpart1, zero_add, hpart2]
  have hF_le : 2 ^ (Module.finrank (ZMod 2) U) ≤ 2 ^ n := by
    have h1 : F.card ≤ (Finset.univ : Finset V).card := Finset.card_le_card (Finset.subset_univ F)
    rw [card_flat U p, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h1
    exact h1
  have hsum2 :
      ∑ u ∈ Uperp,
        (2 * ((Finset.univ : Finset V).filter (fun y => f y ≠ g u y)).card +
          2 ^ (Module.finrank (ZMod 2) U)) =
        Uperp.card * 2 ^ n := by
    rw [Finset.sum_add_distrib, hsum, Finset.sum_const, smul_eq_mul]
    have hcalc : (2 ^ n - 2 ^ (Module.finrank (ZMod 2) U)) * Uperp.card +
        Uperp.card * 2 ^ (Module.finrank (ZMod 2) U) = Uperp.card * 2 ^ n := by
      rw [mul_comm (2 ^ n - 2 ^ (Module.finrank (ZMod 2) U)) Uperp.card, ← mul_add,
        Nat.sub_add_cancel hF_le]
    exact hcalc
  have hne : Uperp.Nonempty := ⟨0, h0_mem⟩
  obtain ⟨u, _hu, hbound⟩ :
      ∃ u ∈ Uperp,
        2 * ((Finset.univ : Finset V).filter (fun y => f y ≠ g u y)).card +
          2 ^ (Module.finrank (ZMod 2) U) ≤ 2 ^ n := by
    by_contra hall
    push Not at hall
    have hstrict :
        ∑ _u ∈ Uperp, (2 ^ n) <
          ∑ u ∈ Uperp,
            (2 * ((Finset.univ : Finset V).filter (fun y => f y ≠ g u y)).card +
              2 ^ (Module.finrank (ZMod 2) U)) :=
      Finset.sum_lt_sum_of_nonempty hne fun u hu => hall u hu
    rw [Finset.sum_const, smul_eq_mul, hsum2] at hstrict
    exact lt_irrefl _ hstrict
  exact ⟨c + u, e + dotProduct u p, hbound⟩

end AgreementAux

theorem Agreement :
∀ n : ℕ,
  let V := Fin n → ZMod 2
  ∀ (f : V → ZMod 2) (U : Submodule (ZMod 2) V) (p c : V) (e : ZMod 2),
    (∀ x ∈ U, f (p+x) = dotProduct c (p+x) + e) →
    ∃ (a : V) (b : ZMod 2), 2*((Finset.univ : Finset V).filter (fun x => f x ≠ dotProduct a x + b)).card +
      2^(Module.finrank (ZMod 2) U) ≤ 2^n := by
  intro n V f U p c e hagree
  exact AgreementAux.main_bound n f U p c e hagree

-- Adapted from ovolee37's L-lib-502 proof in open-goat/pequalnp-proofs PR 38969, Apache-2.0.
-- Changes: rename declarations for use as local helpers of L-lib-507.

namespace RestrictionAux

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

end RestrictionAux

theorem Restriction :
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
  exact RestrictionAux.main_aux n C f hC hf

namespace Exact507

theorem result :
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
    ∃ (a : V) (b : ZMod 2),
      2*((Finset.univ : Finset V).filter (fun z => f z ≠ dotProduct a z + b)).card + 2^(n - cost C) ≤ 2^n := by
  intro n V admissible cost input C f hc hf
  obtain ⟨U, p, a, b, dim, haf⟩ := Restriction n C f hc hf
  obtain ⟨c, d, bound⟩ := Agreement n f U p a b haf
  change n ≤ Module.finrank (ZMod 2) U + cost C at dim
  have sub : n - cost C ≤ Module.finrank (ZMod 2) U := by omega
  exact ⟨c,d,(Nat.add_le_add_left (Nat.pow_le_pow_right (by decide : 0 < 2) sub) _).trans bound⟩

end Exact507

end PEqualNP.Outside.L_lib_507

theorem PEqualNP.Outside.L_lib_507 :
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
    ∃ (a : V) (b : ZMod 2),
      2*((Finset.univ : Finset V).filter (fun z => f z ≠ dotProduct a z + b)).card + 2^(n - cost C) ≤ 2^n :=
  PEqualNP.Outside.L_lib_507.Exact507.result
