import Mathlib
import PEqualNP.Defs

-- The circuit rank calculation uses the helper closure from PEqualNP/Outside/L_meta_25647.lean
-- at 14f1d40321543ada6b5b9b937060aad03bb935b7, licensed under Apache-2.0.
-- Adapted by restricting it to private declarations and bridging singleton output taps.

namespace PEqualNP.Outside.L_meta_29714_aux

section Growth

open Module
open scoped BigOperators

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]

private theorem growthBit (e : ZMod 2) : e = 0 ∨ e = 1 := by
  fin_cases e
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem growthCard {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] : Fintype.card V = 2 ^ finrank (ZMod 2) V := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

private def growthSquare : K →ₗ[ZMod 2] K := by
  letI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp inferInstance
  exact {
    toFun := fun x => x ^ 2
    map_add' := fun x y => (frobenius K 2).map_add x y
    map_smul' := by
      intro e x
      rcases growthBit e with rfl | rfl <;> simp
  }

private def growthRow (U : Submodule (ZMod 2) K) (x : K) : U × ZMod 2 →ₗ[ZMod 2] K :=
  ((LinearMap.mulRight (ZMod 2) x).comp U.subtype).coprod
    ((LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2).smulRight (x ^ 2))

private def growthCol (U : Submodule (ZMod 2) K) (p : U × ZMod 2) : K →ₗ[ZMod 2] K :=
  LinearMap.mulLeft (ZMod 2) (p.1 : K) + p.2 • growthSquare

private theorem growthNoRoot [Fintype K] (hodd : finrank (ZMod 2) K % 2 = 1)
    (y : K) : y ^ 2 + y ≠ 1 := by
  letI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp inferInstance
  intro hy
  have hz : y ^ 2 + y + 1 = 0 := by rw [hy, CharTwo.add_self_eq_zero]
  have hfour : y ^ 4 = y := by linear_combination (y ^ 2 - y) * hz
  have hiter (j : ℕ) : y ^ (2 ^ (2 * j + 1) : ℕ) = y ^ 2 := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [show 2 * (j + 1) + 1 = 2 + (2 * j + 1) by omega,
        pow_add, pow_mul, show (2 : ℕ) ^ 2 = 4 by decide, hfour, ih]
  obtain ⟨j, hj⟩ : ∃ j : ℕ, finrank (ZMod 2) K = 2 * j + 1 :=
    ⟨finrank (ZMod 2) K / 2, by omega⟩
  have hfix := FiniteField.pow_card y
  rw [growthCard, hj, hiter] at hfix
  rw [hfix, CharTwo.add_self_eq_zero] at hy
  exact zero_ne_one hy

private theorem growthCol_top [FiniteDimensional (ZMod 2) K] [Fintype K]
    (U W : Submodule (ZMod 2) K) (hodd : finrank (ZMod 2) K % 2 = 1)
    (hsq : ∀ a : U, (a : K) ^ 2 ∈ W) (p : U × ZMod 2) (hp : p ≠ 0) :
    LinearMap.range (W.mkQ.comp (growthCol U p)) = ⊤ := by
  letI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp inferInstance
  rw [LinearMap.range_comp, Submodule.map_mkQ_eq_top]
  obtain ⟨a, e⟩ := p
  rcases growthBit e with rfl | rfl
  · have ha : (a : K) ≠ 0 := fun h => hp (Prod.ext (Subtype.ext h) rfl)
    have hr : LinearMap.range (LinearMap.mulLeft (ZMod 2) (a : K)) = ⊤ := by
      apply LinearMap.range_eq_top.mpr
      intro x
      refine ⟨x / (a : K), ?_⟩
      change (a : K) * (x / (a : K)) = x
      field_simp
    change W ⊔ LinearMap.range (LinearMap.mulLeft (ZMod 2) (a : K) + (0 : ZMod 2) • growthSquare) = ⊤
    rw [zero_smul, add_zero, hr, sup_top_eq]
  · change W ⊔ LinearMap.range (LinearMap.mulLeft (ZMod 2) (a : K) + (1 : ZMod 2) • growthSquare) = ⊤
    rw [one_smul]
    by_cases ha : (a : K) = 0
    · have hr : LinearMap.range (growthSquare : K →ₗ[ZMod 2] K) = ⊤ := by
        apply (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank rfl).mp
        exact LinearMap.ker_eq_bot'.mpr fun x hx => sq_eq_zero_iff.mp hx
      rw [ha, LinearMap.mulLeft_zero_eq_zero, zero_add, hr, sup_top_eq]
    · let f := LinearMap.mulLeft (ZMod 2) (a : K) + growthSquare
      change W ⊔ LinearMap.range f = ⊤
      have hzero (x : K) : f x = 0 ↔ x = 0 ∨ x = (a : K) := by
        change (a : K) * x + x ^ 2 = 0 ↔ _
        rw [show (a : K) * x + x ^ 2 = x * (x + (a : K)) by ring,
          mul_eq_zero, CharTwo.add_eq_zero]
      have hker : LinearMap.ker f = Submodule.span (ZMod 2) {(a : K)} := by
        ext x
        rw [LinearMap.mem_ker, hzero, Submodule.mem_span_singleton]
        constructor
        · rintro (rfl | rfl)
          · exact ⟨0, zero_smul _ _⟩
          · exact ⟨1, one_smul _ _⟩
        · rintro ⟨e, he⟩
          rcases growthBit e with rfl | rfl
          · exact Or.inl (by simpa using he.symm)
          · exact Or.inr (by simpa using he.symm)
      have hnot : (a : K) ^ 2 ∉ LinearMap.range f := by
        rintro ⟨x, hx⟩
        change (a : K) * x + x ^ 2 = (a : K) ^ 2 at hx
        apply growthNoRoot hodd (x / (a : K))
        calc
          (x / (a : K)) ^ 2 + x / (a : K) = ((a : K) * x + x ^ 2) / (a : K) ^ 2 := by
            field_simp <;> ring
          _ = 1 := by rw [hx, div_self (pow_ne_zero 2 ha)]
      have hr := f.finrank_range_add_finrank_ker
      rw [hker, finrank_span_singleton ha] at hr
      have ht : LinearMap.range f ⊔ Submodule.span (ZMod 2) {(a : K) ^ 2} = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [Submodule.finrank_sup_span_singleton hnot, hr]
      have hle : LinearMap.range f ⊔ Submodule.span (ZMod 2) {(a : K) ^ 2} ≤
          W ⊔ LinearMap.range f :=
        sup_le le_sup_right ((Submodule.span_singleton_le_iff_mem _ _).mpr (hsq a) |>.trans le_sup_left)
      exact top_le_iff.mp (ht ▸ hle)

private theorem growthRow_range (U : Submodule (ZMod 2) K) (x : K) :
    LinearMap.range (growthRow U x) =
      U.map (LinearMap.mulRight (ZMod 2) x) ⊔ Submodule.span (ZMod 2) {x ^ 2} := by
  rw [growthRow, LinearMap.range_coprod, LinearMap.range_comp, Submodule.range_subtype]
  congr 1
  ext y
  rw [LinearMap.mem_range, Submodule.mem_span_singleton]
  rfl

/-- One-step product growth. Only containment of the squares from `U` in `W` is needed. -/
private theorem growth_exists [FiniteDimensional (ZMod 2) K]
    (U W : Submodule (ZMod 2) K) (hodd : finrank (ZMod 2) K % 2 = 1)
    (hsq : ∀ a : U, (a : K) ^ 2 ∈ W) :
    ∃ x : K, finrank (ZMod 2)
      (W ⊔ U.map (LinearMap.mulRight (ZMod 2) x) ⊔ Submodule.span (ZMod 2) {x ^ 2} :
        Submodule (ZMod 2) K) =
      min (finrank (ZMod 2) K) (finrank (ZMod 2) W + finrank (ZMod 2) U + 1) := by
  classical
  letI : Finite K := Module.finite_of_finite (ZMod 2)
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype U := Fintype.ofFinite U
  let k := finrank (ZMod 2) K
  let w := finrank (ZMod 2) W
  let m := finrank (ZMod 2) (U × ZMod 2)
  let d := min (k - w) m
  let R (x : K) := W.mkQ.comp (growthRow U x)
  let C (p : U × ZMod 2) := W.mkQ.comp (growthCol U p)
  letI (x : K) : Fintype (LinearMap.ker (R x)) := Fintype.ofFinite _
  letI (p : U × ZMod 2) : Fintype (LinearMap.ker (C p)) := Fintype.ofFinite _
  have hW : finrank (ZMod 2) (K ⧸ W) + w = k := W.finrank_quotient_add_finrank
  have hw : w ≤ k := W.finrank_le
  have hm : m = finrank (ZMod 2) U + 1 := by
    simp [m, Module.finrank_prod, Module.finrank_self]
  have hcol (p : U × ZMod 2) (hp : p ≠ 0) : Fintype.card (LinearMap.ker (C p)) = 2 ^ w := by
    have hi := (C p).finrank_range_add_finrank_ker
    have hj : LinearMap.range (C p) = ⊤ := growthCol_top U W hodd hsq p hp
    rw [hj, finrank_top] at hi
    rw [growthCard]
    congr 1
    omega
  have hzero : Fintype.card (LinearMap.ker (C 0)) = 2 ^ k := by
    have hf : C 0 = 0 := by
      ext x
      change W.mkQ ((0 : K) * x + (0 : ZMod 2) • x ^ 2) = 0
      simp
    rw [growthCard, hf, LinearMap.ker_zero, finrank_top]
  -- The two sigma types are the same incidence relation with transposed coordinates.
  let swap : (Σ x : K, LinearMap.ker (R x)) ≃
      (Σ p : U × ZMod 2, LinearMap.ker (C p)) := {
    toFun := fun ⟨x, p, h⟩ => ⟨p, x, h⟩
    invFun := fun ⟨p, x, h⟩ => ⟨x, p, h⟩
    left_inv := fun ⟨_, _, _⟩ => rfl
    right_inv := fun ⟨_, _, _⟩ => rfl
  }
  have hsum : ∑ x : K, Fintype.card (LinearMap.ker (R x)) =
      2 ^ k + (2 ^ m - 1) * 2 ^ w := by
    have h := Fintype.card_congr swap
    rw [Fintype.card_sigma, Fintype.card_sigma] at h
    rw [h, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : U × ZMod 2)), hzero, add_comm]
    congr 1
    rw [Finset.sum_const_nat (fun p hp => hcol p (Finset.mem_erase.mp hp).1),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, growthCard]
  have hex : ∃ x : K, d ≤ finrank (ZMod 2) (LinearMap.range (R x)) := by
    by_contra! hn
    have hl (x : K) : 2 ^ (m - d + 1) ≤ Fintype.card (LinearMap.ker (R x)) := by
      have hx : finrank (ZMod 2) (LinearMap.range (R x)) +
          finrank (ZMod 2) (LinearMap.ker (R x)) = m := (R x).finrank_range_add_finrank_ker
      have hd : d ≤ m := min_le_right _ _
      rw [growthCard]
      exact Nat.pow_le_pow_right (by decide) (by have := hn x; omega)
    have hl' : 2 ^ k * 2 ^ (m - d + 1) ≤ ∑ x : K, Fintype.card (LinearMap.ker (R x)) := by
      simpa [Finset.sum_const, growthCard (V := K), k] using
        (Finset.sum_le_sum (s := (Finset.univ : Finset K)) (f := fun _ => 2 ^ (m - d + 1))
          (fun x _ => hl x))
    have hd₁ : d ≤ k - w := min_le_left _ _
    have hd₂ : d ≤ m := min_le_right _ _
    have ha : 2 ^ k ≤ 2 ^ k * 2 ^ (m - d) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hb : 2 ^ (m + w) ≤ 2 ^ k * 2 ^ (m - d) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hc : 2 ^ k + 2 ^ (m + w) ≤ 2 ^ k * 2 ^ (m - d + 1) := by
      rw [pow_succ, ← Nat.mul_assoc, Nat.mul_two]
      exact Nat.add_le_add ha hb
    have hlt : 2 ^ k + (2 ^ m - 1) * 2 ^ w < 2 ^ k + 2 ^ (m + w) := by
      rw [pow_add]
      have hpos : 0 < (2 : ℕ) ^ m := by positivity
      exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)) _
    exact (Nat.not_lt_of_ge (hc.trans (hl'.trans_eq hsum))) hlt
  obtain ⟨x, hx⟩ := hex
  have hlim₁ := (LinearMap.range (R x)).finrank_le
  have hlim₂ : finrank (ZMod 2) (LinearMap.range (R x)) ≤ m := by
    have hr := (R x).finrank_range_add_finrank_ker
    change finrank (ZMod 2) (LinearMap.range (R x)) + finrank (ZMod 2) (LinearMap.ker (R x)) = m at hr
    omega
  have hmax : finrank (ZMod 2) (LinearMap.range (R x)) = d := by
    apply le_antisymm _ hx
    exact le_min (by omega) hlim₂
  let T := W ⊔ LinearMap.range (growthRow U x)
  have hle : W ≤ T := le_sup_left
  let f := W.mkQ.comp T.subtype
  have hf : LinearMap.range f = LinearMap.range (R x) := by
    rw [LinearMap.range_comp, Submodule.range_subtype, show T = W ⊔ _ from rfl,
      Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
    exact (LinearMap.range_comp _ _).symm
  have hk : LinearMap.ker f = W.comap T.subtype := by
    change LinearMap.ker (W.mkQ.comp T.subtype) = _
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have ht := f.finrank_range_add_finrank_ker
  rw [hf, hk, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq, hmax] at ht
  have hout : W ⊔ U.map (LinearMap.mulRight (ZMod 2) x) ⊔ Submodule.span (ZMod 2) {x ^ 2} = T := by
    rw [sup_assoc, show T = W ⊔ _ from rfl, growthRow_range]
  refine ⟨x, ?_⟩
  rw [hout, ← ht]
  change d + w = min k (w + finrank (ZMod 2) U + 1)
  unfold d
  omega

end Growth

open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

-- Circuit and pairing helpers adapted from lean/PEqualNP/Outside/L_meta_25830.lean
-- at c041cec7a3792f85383b96bde660f88d6fbd8671.
private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp [b2z] at h <;> rfl

private theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

private theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private theorem zmod2_two : (2 : ZMod 2) = 0 := rfl

private theorem zmod2_ite_eq (x : ZMod 2) : (if x = 1 then (1 : ZMod 2) else 0) = x := by
  by_cases h : x = 1
  · simp [h]
  · simp only [h, ite_false]
    fin_cases x
    · rfl
    · exact absurd rfl h

private def nlGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

private def depthsOf (w : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
    (List.replicate w 0)

private def wiresOf (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem wiresOf_length (x : List Bool) (gs : List Gate) :
    (wiresOf x gs).length = x.length + gs.length := by
  unfold wiresOf
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem depthsOf_length (w : ℕ) (gs : List Gate) :
    (depthsOf w gs).length = w + gs.length := by
  unfold depthsOf
  have aux : ∀ (ds : List ℕ) (gs : List Gate),
      (gs.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat]) ds).length =
      ds.length + gs.length := by
    intro ds gs
    induction gs generalizing ds with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  rw [aux, List.length_replicate]

private theorem wiresOf_append (x : List Bool) (gs1 gs2 : List Gate) :
    wiresOf x (gs1 ++ gs2) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (wiresOf x gs1) := by
  unfold wiresOf
  rw [List.foldl_append]

private theorem depthsOf_append (w : ℕ) (gs1 gs2 : List Gate) :
    depthsOf w (gs1 ++ gs2) =
      gs2.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
        (depthsOf w gs1) := by
  unfold depthsOf
  rw [List.foldl_append]

private theorem foldl_append_prefix {α β : Type*} (f : List α → β → α) (l : List β) (init : List α) :
    ∃ ext : List α, l.foldl (fun acc b => acc ++ [f acc b]) init = init ++ ext := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    obtain ⟨ext, hext⟩ := ih (init ++ [f init b])
    exact ⟨f init b :: ext, by rw [hext]; simp⟩

private theorem wiresOf_append_getD_lt (x : List Bool) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < x.length + gs1.length) :
    (wiresOf x (gs1 ++ gs2)).getD k false = (wiresOf x gs1).getD k false := by
  rw [wiresOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_prefix
    (fun (w : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false))
    gs2 (wiresOf x gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [wiresOf_length]; exact hk)]

private theorem depthsOf_append_getD_lt (w : ℕ) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < w + gs1.length) :
    (depthsOf w (gs1 ++ gs2)).getD k 0 = (depthsOf w gs1).getD k 0 := by
  rw [depthsOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_prefix
    (fun (ds : List ℕ) (g : Gate) =>
      (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat)
    gs2 (depthsOf w gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [depthsOf_length]; exact hk)]

private theorem wiresOf_getD_input (x : List Bool) (gs : List Gate) {k : ℕ} (hk : k < x.length) :
    (wiresOf x gs).getD k false = x.getD k false := by
  have h := wiresOf_append_getD_lt x [] gs (by simpa using hk)
  simpa [wiresOf] using h

private theorem depthsOf_getD_input (w : ℕ) (gs : List Gate) {k : ℕ} (hk : k < w) :
    (depthsOf w gs).getD k 0 = 0 := by
  have h := depthsOf_append_getD_lt w [] gs (by simpa using hk)
  simp only [List.nil_append] at h
  rw [h]
  unfold depthsOf
  simp only [List.foldl_nil]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_replicate]

private theorem wiresOf_getD_gate (x : List Bool) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < x.length + idx) :
    (wiresOf x gs).getD (x.length + idx) false =
      (gs[idx]).op.eval ((gs[idx]).inputs.map fun a => (wiresOf x gs).getD a false) := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
  have hlw : (wiresOf x (gs.take idx)).length = x.length + idx := by
    rw [wiresOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlw, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < x.length + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append_getD_lt x (gs.take idx) [gs[idx]] halt]

private theorem depthsOf_getD_gate (w : ℕ) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < w + idx) :
    (depthsOf w gs).getD (w + idx) 0 =
      ((gs[idx]).inputs.map (fun a => (depthsOf w gs).getD a 0)).foldr max 0 +
        (nlGate (gs[idx])).toNat := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
  have hld : (depthsOf w (gs.take idx)).length = w + idx := by
    rw [depthsOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hld, Nat.sub_self, List.getD_cons_zero]
  congr 2
  apply List.map_congr_left
  intro a ha
  have halt : a < w + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [depthsOf_append_getD_lt w (gs.take idx) [gs[idx]] halt]

private theorem oneEach_length {n m : ℕ} (i : Fin n) (j : Fin m) :
    (oneEach i j).length = n + m := by
  simp [oneEach]

private theorem oneEach_getD_left {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk : k < n) :
    (oneEach i j).getD k false = decide (k = i.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp [hk])]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
  simp [Fin.ext_iff]

private theorem oneEach_getD_right {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk1 : n ≤ k)
    (hk2 : k < n + m) :
    (oneEach i j).getD k false = decide (k - n = j.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp [hk1])]
  simp only [List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  simp [Fin.ext_iff]

private theorem anf_one (f : Bool → Bool) (x : Bool) :
    b2z (f x) = b2z (f false) + (b2z (f false) + b2z (f true)) * b2z x := by
  cases x <;> cases h0 : f false <;> cases h1 : f true <;> decide

private theorem anf_two (f : Bool → Bool → Bool) (x y : Bool) :
    b2z (f x y) =
      b2z (f false false) +
      (b2z (f false false) + b2z (f true false)) * b2z x +
      (b2z (f false false) + b2z (f false true)) * b2z y +
      b2z (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
        (b2z x * b2z y) := by
  cases x <;> cases y <;>
    cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;> decide

private def anchor {n m : ℕ} (u : Fin n) (v : Fin m) (h : Fin n → Fin m → ZMod 2) :
    Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun i j => h i j + h i v + h u j + h u v

private theorem anchor_const {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2) :
    anchor u v (fun _ _ => c) = 0 := by
  ext i j
  simp only [anchor, Matrix.zero_apply]
  simp [zmod2_add_self]

private theorem anchor_split {n m : ℕ} (u : Fin n) (v : Fin m) (r : Fin n → ZMod 2) (s : Fin m → ZMod 2) :
    anchor u v (fun i j => r i + s j) = 0 := by
  ext i j
  simp only [anchor, Matrix.zero_apply]
  have h : (r i + s j) + (r i + s v) + (r u + s j) + (r u + s v) =
      (r i + r i) + (r u + r u) + (s j + s j) + (s v + s v) := by ring
  simp [h, zmod2_add_self]

private theorem anchor_add {n m : ℕ} (u : Fin n) (v : Fin m) (h1 h2 : Fin n → Fin m → ZMod 2) :
    anchor u v (fun i j => h1 i j + h2 i j) = anchor u v h1 + anchor u v h2 := by
  ext i j
  simp only [anchor, Matrix.add_apply]
  ring

private theorem anchor_smul {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2) (h : Fin n → Fin m → ZMod 2) :
    anchor u v (fun i j => c * h i j) = c • anchor u v h := by
  ext i j
  simp only [anchor, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem anchor_prod_split {n m : ℕ} (u : Fin n) (v : Fin m)
    (r1 r2 : Fin n → ZMod 2) (s1 s2 : Fin m → ZMod 2) :
    anchor u v (fun i j => (r1 i + s1 j) * (r2 i + s2 j)) =
      Matrix.vecMulVec (fun i => r1 i + r1 u) (fun j => s2 j + s2 v) +
      Matrix.vecMulVec (fun i => r2 i + r2 u) (fun j => s1 j + s1 v) := by
  ext i j
  simp only [anchor, Matrix.add_apply, Matrix.vecMulVec_apply]
  have h : ((r1 i + s1 j) * (r2 i + s2 j) + (r1 i + s1 v) * (r2 i + s2 v) +
      (r1 u + s1 j) * (r2 u + s2 j) + (r1 u + s1 v) * (r2 u + s2 v)) +
      ((r1 i + r1 u) * (s2 j + s2 v) + (r2 i + r2 u) * (s1 j + s1 v)) =
      (2 : ZMod 2) * (r1 i * r2 i + r1 u * r2 u + s1 j * s2 j + s1 v * s2 v +
        r1 i * s2 j + r1 i * s2 v + r1 u * s2 j + r1 u * s2 v +
        r2 i * s1 j + r2 i * s1 v + r2 u * s1 j + r2 u * s1 v) := by ring
  rw [zmod2_two, zero_mul] at h
  have hsub : ∀ a b : ZMod 2, a + b = 0 → a = b := by
    intro a b hab
    calc a = a + 0 := (add_zero a).symm
      _ = a + (b + b) := by rw [zmod2_add_self]
      _ = (a + b) + b := by ring
      _ = 0 + b := by rw [hab]
      _ = b := zero_add b
  exact hsub _ _ h

private theorem factor_of_rank_le {n m K : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod 2)) (h : A.rank ≤ K) :
    ∃ (rowVec : Fin K → Fin n → ZMod 2) (colVec : Fin K → Fin m → ZMod 2),
      ∀ i j, A i j = ∑ k : Fin K, rowVec k i * colVec k j := by
  let r := A.rank
  let b := Module.finBasisOfFinrankEq (ZMod 2) (LinearMap.range A.mulVecLin)
    (rfl : Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) = r)
  have hcol : ∀ j : Fin m, (fun i => A i j) ∈ LinearMap.range A.mulVecLin := by
    intro j
    refine ⟨Pi.single j 1, ?_⟩
    ext i
    simp [Matrix.mulVec_single]
  let rowVec : Fin K → Fin n → ZMod 2 := fun k i =>
    if hk : k.val < r then (b ⟨k.val, hk⟩).val i else 0
  let colVec : Fin K → Fin m → ZMod 2 := fun k j =>
    if hk : k.val < r then b.repr ⟨fun i => A i j, hcol j⟩ ⟨k.val, hk⟩ else 0
  refine ⟨rowVec, colVec, fun i j => ?_⟩
  have hrepr : ∑ t : Fin r, (b.repr ⟨fun i => A i j, hcol j⟩ t) • (b t) =
      ⟨fun i => A i j, hcol j⟩ := b.sum_repr ⟨fun i => A i j, hcol j⟩
  have heval : A i j = ∑ t : Fin r, (b t).val i * b.repr ⟨fun i => A i j, hcol j⟩ t := by
    have h1 := congrArg (fun (v : LinearMap.range A.mulVecLin) => v.val i) hrepr
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul_of_tower,
      Pi.smul_apply, smul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun t _ => mul_comm _ _
  rw [heval]
  symm
  have hfilt : ∑ k : Fin K, rowVec k i * colVec k j =
      ∑ k ∈ Finset.univ.filter (fun k : Fin K => k.val < r), rowVec k i * colVec k j := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hnk
    rw [Finset.mem_filter] at hnk
    have hge : ¬ k.val < r := fun hk => hnk ⟨Finset.mem_univ k, hk⟩
    simp [rowVec, colVec, hge]
  rw [hfilt]
  refine Finset.sum_bij (fun k hk => ⟨k.val, (Finset.mem_filter.mp hk).2⟩) ?_ ?_ ?_ ?_
  · intro _ _
    exact Finset.mem_univ _
  · intro k1 _ k2 _ heq
    exact Fin.ext (Fin.mk.inj heq)
  · intro t _
    refine ⟨⟨t.val, Nat.lt_of_lt_of_le t.isLt h⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩, Fin.ext rfl⟩
  · intro k hk
    have hlt : k.val < r := (Finset.mem_filter.mp hk).2
    simp only [rowVec, colVec, hlt, dite_true]
    rfl

private theorem card_filter_fin_eq_countP {α : Type*} (l : List α) (p : α → Bool) :
    (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons]
    have hsplit : (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true)).card =
        (if p a = true then 1 else 0) +
        (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card := by
      have hsum : ∀ (S : Finset (Fin (l.length + 1))), S.card =
          (if (0 : Fin (l.length + 1)) ∈ S then 1 else 0) +
          (Finset.univ.filter (fun idx : Fin l.length => idx.succ ∈ S)).card := by
        intro S
        have h1 : S.card = ∑ x : Fin (l.length + 1), if x ∈ S then 1 else 0 := by
          simp
        rw [h1, Fin.sum_univ_succ]
        congr 1
        simp
      have h2 := hsum (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true))
      simpa using h2
    rw [hsplit, ih]
    cases p a <;> simp [Nat.add_comm]

private theorem dir_le {n m : ℕ} (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ)
    (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (hrep : Represents G C)
    (hd1 : (depthsOf (n + m) C.gates).getD C.output 0 ≤ 1)
    (hcnt : C.gates.countP nlGate ≤ t) :
    (anchor u v (fun i j => b2z (G i j))).rank ≤ 2 * t := by
  let val : ℕ → Fin n → Fin m → ZMod 2 :=
    fun k i j => b2z ((wiresOf (oneEach i j) C.gates).getD k false)
  let dep : ℕ → ℕ := fun k => (depthsOf (n + m) C.gates).getD k 0
  have hrb' : ∀ (idx : ℕ) (hidx : idx < C.gates.length),
      ∀ a ∈ (C.gates[idx]).inputs, a < n + m + idx := by
    intro idx hidx a ha
    have h := hrb idx hidx a
    unfold gateAt at h
    rw [List.getD_eq_getElem _ _ hidx] at h
    exact h ha
  have hval_gate : ∀ (idx : ℕ) (hidx : idx < C.gates.length) (i : Fin n) (j : Fin m),
      val (n + m + idx) i j =
        b2z ((C.gates[idx]).op.eval ((C.gates[idx]).inputs.map fun a =>
          (wiresOf (oneEach i j) C.gates).getD a false)) := by
    intro idx hidx i j
    unfold val
    have h := wiresOf_getD_gate (oneEach i j) C.gates hidx (by
      intro a ha
      rw [oneEach_length]
      exact hrb' idx hidx a ha)
    rw [oneEach_length] at h
    rw [h]
  have hdep_gate : ∀ (idx : ℕ) (hidx : idx < C.gates.length),
      dep (n + m + idx) =
        ((C.gates[idx]).inputs.map (fun a => dep a)).foldr max 0 +
          (nlGate (C.gates[idx])).toNat := by
    intro idx hidx
    exact depthsOf_getD_gate (n + m) C.gates hidx (hrb' idx hidx)
  have hsplit_zero : ∀ k : ℕ, dep k = 0 →
      ∃ (r : Fin n → ZMod 2) (s : Fin m → ZMod 2), ∀ i j, val k i j = r i + s j := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hdk
      by_cases hk1 : k < n + m
      · by_cases hk0 : k < n
        · refine ⟨fun i => b2z (decide (k = i.val)), fun _ => 0, fun i j => ?_⟩
          unfold val
          rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; exact hk1),
            oneEach_getD_left i j hk0, add_zero]
        · refine ⟨fun _ => 0, fun j => b2z (decide (k - n = j.val)), fun i j => ?_⟩
          unfold val
          rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; exact hk1),
            oneEach_getD_right i j (by omega) hk1, zero_add]
      · by_cases hk2 : k < n + m + C.gates.length
        · let idx := k - (n + m)
          have hidx : idx < C.gates.length := by omega
          have hkeq : k = n + m + idx := by omega
          rw [hkeq] at hdk ⊢
          let g := C.gates[idx]
          have hdg := hdep_gate idx hidx
          change dep (n + m + idx) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
          rw [hdk] at hdg
          have hnl : nlGate g = false := by
            have h0 : (nlGate g).toNat = 0 := by omega
            cases h : nlGate g
            · rfl
            · rw [h] at h0
              simp at h0
          have hgl : g.inputs.length ≤ 2 := hlen g (List.getElem_mem hidx)
          match hg_in : g.inputs with
          | [] =>
            refine ⟨fun _ => b2z (g.op.eval []), fun _ => 0, fun i j => ?_⟩
            rw [hval_gate idx hidx i j]
            change b2z (g.op.eval (g.inputs.map _)) = _
            rw [hg_in, List.map_nil, add_zero]
          | [a] =>
            have ha_lt : a < n + m + idx := hrb' idx hidx a (by rw [hg_in]; simp)
            have ha_d : dep a = 0 := by
              change 0 = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp at hdg
              omega
            obtain ⟨r1, s1, h1⟩ := ih a (by omega) ha_d
            let c0 := b2z (g.op.eval [false])
            let c1 := b2z (g.op.eval [false]) + b2z (g.op.eval [true])
            refine ⟨fun i => c0 + c1 * r1 i, fun j => c1 * s1 j, fun i j => ?_⟩
            rw [hval_gate idx hidx i j]
            change b2z (g.op.eval (g.inputs.map _)) = _
            rw [hg_in, List.map_cons, List.map_nil]
            have hanf := anf_one (fun x => g.op.eval [x]) ((wiresOf (oneEach i j) C.gates).getD a false)
            change b2z (g.op.eval [_]) = c0 + c1 * val a i j at hanf
            rw [hanf, h1 i j]
            ring
          | [a, b] =>
            have ha_lt : a < n + m + idx := hrb' idx hidx a (by rw [hg_in]; simp)
            have hb_lt : b < n + m + idx := hrb' idx hidx b (by rw [hg_in]; simp)
            have hab_d : dep a = 0 ∧ dep b = 0 := by
              change 0 = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdg
              omega
            obtain ⟨r1, s1, h1⟩ := ih a (by omega) hab_d.1
            obtain ⟨r2, s2, h2⟩ := ih b (by omega) hab_d.2
            have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              unfold nlGate at hnl
              rw [hg_in] at hnl
              simpa using hnl
            let c0 := b2z (g.op.eval [false, false])
            let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
            let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
            refine ⟨fun i => c0 + c1 * r1 i + c2 * r2 i, fun j => c1 * s1 j + c2 * s2 j, fun i j => ?_⟩
            rw [hval_gate idx hidx i j]
            change b2z (g.op.eval (g.inputs.map _)) = _
            rw [hg_in, List.map_cons, List.map_cons, List.map_nil]
            have hanf := anf_two (fun x y => g.op.eval [x, y])
              ((wiresOf (oneEach i j) C.gates).getD a false)
              ((wiresOf (oneEach i j) C.gates).getD b false)
            rw [hxor] at hanf
            have hbf : b2z false = 0 := rfl
            change b2z (g.op.eval [_, _]) = c0 + c1 * val a i j + c2 * val b i j + b2z false * _ at hanf
            rw [hbf, zero_mul, add_zero] at hanf
            rw [hanf, h1 i j, h2 i j]
            ring
          | _ :: _ :: _ :: _ =>
            rw [hg_in] at hgl
            simp at hgl
        · refine ⟨fun _ => 0, fun _ => 0, fun i j => ?_⟩
          unfold val
          have hge : (wiresOf (oneEach i j) C.gates).length ≤ k := by
            rw [wiresOf_length, oneEach_length]
            omega
          rw [List.getD_eq_default _ _ hge]
          simp [b2z]
  let NL : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun idx => nlGate (C.gates[idx.val]) = true ∧ dep (n + m + idx.val) ≤ 1)
  have hNL_card : NL.card ≤ t := by
    calc NL.card
        ≤ (Finset.univ.filter (fun idx : Fin C.gates.length => nlGate (C.gates[idx.val]) = true)).card :=
          Finset.card_le_card (fun idx hidx => Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp hidx).2.1⟩)
      _ = C.gates.countP nlGate := card_filter_fin_eq_countP C.gates nlGate
      _ ≤ t := hcnt
  have hNL_outer : ∀ idx ∈ NL,
      ∃ (r1 r2 : Fin n → ZMod 2) (s1 s2 : Fin m → ZMod 2),
        anchor u v (val (n + m + idx.val)) =
          Matrix.vecMulVec r1 s1 + Matrix.vecMulVec r2 s2 := by
    intro idx hidx_mem
    have hnl : nlGate (C.gates[idx.val]) = true := (Finset.mem_filter.mp hidx_mem).2.1
    have hdg1 : dep (n + m + idx.val) ≤ 1 := (Finset.mem_filter.mp hidx_mem).2.2
    let g := C.gates[idx.val]
    have hlen2 : g.inputs.length = 2 := by
      unfold nlGate at hnl
      rw [Bool.and_eq_true] at hnl
      simpa using hnl.1
    obtain ⟨a, b, hab⟩ : ∃ a b, g.inputs = [a, b] := by
      match h : g.inputs with
      | [a, b] => exact ⟨a, b, rfl⟩
      | [] => rw [h] at hlen2; simp at hlen2
      | [_] => rw [h] at hlen2; simp at hlen2
      | _ :: _ :: _ :: _ => rw [h] at hlen2; simp at hlen2
    have hdg := hdep_gate idx.val idx.isLt
    change dep (n + m + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
    rw [hab, hnl] at hdg
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_true] at hdg
    have hda : dep a = 0 := by omega
    have hdb : dep b = 0 := by omega
    obtain ⟨r1, s1, h1⟩ := hsplit_zero a hda
    obtain ⟨r2, s2, h2⟩ := hsplit_zero b hdb
    have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
      unfold nlGate at hnl
      rw [Bool.and_eq_true] at hnl
      exact hnl.2
    let c0 := b2z (g.op.eval [false, false])
    let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
    let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
    have hfun : val (n + m + idx.val) = fun i j =>
        (c0 + c1 * r1 i + c2 * r2 i + (c1 * s1 j + c2 * s2 j)) +
        (r1 i + s1 j) * (r2 i + s2 j) := by
      funext i j
      rw [hval_gate idx.val idx.isLt i j]
      change b2z (g.op.eval (g.inputs.map _)) = _
      rw [hab, List.map_cons, List.map_cons, List.map_nil]
      have hanf := anf_two (fun x y => g.op.eval [x, y])
        ((wiresOf (oneEach i j) C.gates).getD a false)
        ((wiresOf (oneEach i j) C.gates).getD b false)
      rw [hxor] at hanf
      have hbt : b2z true = 1 := rfl
      change b2z (g.op.eval [_, _]) = c0 + c1 * val a i j + c2 * val b i j + b2z true * (val a i j * val b i j) at hanf
      rw [hbt, one_mul] at hanf
      rw [hanf, h1 i j, h2 i j]
      ring
    refine ⟨fun i => r1 i + r1 u, fun i => r2 i + r2 u, fun j => s2 j + s2 v, fun j => s1 j + s1 v, ?_⟩
    rw [hfun, anchor_add, anchor_split, zero_add, anchor_prod_split]
  have hspan : ∀ k : ℕ, dep k ≤ 1 →
      ∃ coeff : Fin C.gates.length → ZMod 2,
        anchor u v (val k) = ∑ idx ∈ NL, coeff idx • anchor u v (val (n + m + idx.val)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hdk
      by_cases hdk0 : dep k = 0
      · obtain ⟨r, s, hrs⟩ := hsplit_zero k hdk0
        refine ⟨fun _ => 0, ?_⟩
        have hfun : val k = fun i j => r i + s j := by funext i j; exact hrs i j
        rw [hfun, anchor_split]
        simp
      · have hk1 : n + m ≤ k := by
          by_contra hlt
          have := depthsOf_getD_input (n + m) C.gates (by omega : k < n + m)
          exact hdk0 this
        have hk2 : k < n + m + C.gates.length := by
          by_contra hge
          have hlen_d : (depthsOf (n + m) C.gates).length ≤ k := by
            rw [depthsOf_length]
            omega
          exact hdk0 (List.getD_eq_default _ _ hlen_d)
        let idx : Fin C.gates.length := ⟨k - (n + m), by omega⟩
        have hkeq : k = n + m + idx.val := by simp [idx]; omega
        rw [hkeq] at hdk ⊢
        let g := C.gates[idx.val]
        by_cases hnl : nlGate g = true
        · have hmem : idx ∈ NL := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnl, hdk⟩
          refine ⟨fun idx' => if idx' = idx then 1 else 0, ?_⟩
          rw [Finset.sum_eq_single idx]
          · simp
          · intro idx' _ hne
            simp [hne]
          · intro h
            exact absurd hmem h
        · have hnlf : nlGate g = false := by cases h : nlGate g <;> simp_all
          have hdg := hdep_gate idx.val idx.isLt
          have hgl : g.inputs.length ≤ 2 := hlen g (List.getElem_mem idx.isLt)
          match hg_in : g.inputs with
          | [] =>
            refine ⟨fun _ => 0, ?_⟩
            have hfun : val (n + m + idx.val) = fun _ _ => b2z (g.op.eval []) := by
              funext i j
              rw [hval_gate idx.val idx.isLt i j]
              change b2z (g.op.eval (g.inputs.map _)) = _
              rw [hg_in, List.map_nil]
            rw [hfun, anchor_const]
            simp
          | [a] =>
            have ha_lt : a < n + m + idx.val := hrb' idx.val idx.isLt a (by rw [hg_in]; simp)
            have ha_d : dep a ≤ 1 := by
              change dep (n + m + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp at hdg
              omega
            obtain ⟨ca, hca⟩ := ih a (by omega) ha_d
            let c0 := b2z (g.op.eval [false])
            let c1 := b2z (g.op.eval [false]) + b2z (g.op.eval [true])
            refine ⟨fun idx' => c1 * ca idx', ?_⟩
            have hfun : val (n + m + idx.val) = fun i j => c0 + c1 * val a i j := by
              funext i j
              rw [hval_gate idx.val idx.isLt i j]
              change b2z (g.op.eval (g.inputs.map _)) = _
              rw [hg_in, List.map_cons, List.map_nil]
              exact anf_one (fun x => g.op.eval [x]) ((wiresOf (oneEach i j) C.gates).getD a false)
            rw [hfun, anchor_add, anchor_const, zero_add, anchor_smul, hca, Finset.smul_sum]
            refine Finset.sum_congr rfl fun idx' _ => by rw [smul_smul]
          | [a, b] =>
            have ha_lt : a < n + m + idx.val := hrb' idx.val idx.isLt a (by rw [hg_in]; simp)
            have hb_lt : b < n + m + idx.val := hrb' idx.val idx.isLt b (by rw [hg_in]; simp)
            have hab_d : dep a ≤ 1 ∧ dep b ≤ 1 := by
              change dep (n + m + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdg
              omega
            obtain ⟨ca, hca⟩ := ih a (by omega) hab_d.1
            obtain ⟨cb, hcb⟩ := ih b (by omega) hab_d.2
            have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              unfold nlGate at hnlf
              rw [hg_in] at hnlf
              simpa using hnlf
            let c0 := b2z (g.op.eval [false, false])
            let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
            let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
            refine ⟨fun idx' => c1 * ca idx' + c2 * cb idx', ?_⟩
            have hfun : val (n + m + idx.val) = fun i j => (c0 + c1 * val a i j) + c2 * val b i j := by
              funext i j
              rw [hval_gate idx.val idx.isLt i j]
              change b2z (g.op.eval (g.inputs.map _)) = _
              rw [hg_in, List.map_cons, List.map_cons, List.map_nil]
              have hanf := anf_two (fun x y => g.op.eval [x, y])
                ((wiresOf (oneEach i j) C.gates).getD a false)
                ((wiresOf (oneEach i j) C.gates).getD b false)
              rw [hxor] at hanf
              have hbf : b2z false = 0 := rfl
              change b2z (g.op.eval [_, _]) = c0 + c1 * val a i j + c2 * val b i j + b2z false * _ at hanf
              rw [hbf, zero_mul, add_zero] at hanf
              exact hanf
            rw [hfun, anchor_add, anchor_add, anchor_const, zero_add, anchor_smul, anchor_smul,
              hca, hcb, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun idx' _ => by
              rw [smul_smul, smul_smul, ← add_smul]
          | _ :: _ :: _ :: _ =>
            rw [hg_in] at hgl
            simp at hgl
  obtain ⟨coeff, hcoeff⟩ := hspan C.output hd1
  have hAeq : anchor u v (fun i j => b2z (G i j)) = anchor u v (val C.output) := by
    congr 1
    funext i j
    unfold val
    rw [← hrep i j]
    rfl
  rw [hAeq, hcoeff]
  choose r1 r2 s1 s2 houter using fun idx : NL => hNL_outer idx.val idx.property
  let P : Matrix (Fin n) (NL ⊕ NL) (ZMod 2) := fun i k =>
    match k with
    | Sum.inl idx => coeff idx.val * r1 idx i
    | Sum.inr idx => coeff idx.val * r2 idx i
  let Q : Matrix (NL ⊕ NL) (Fin m) (ZMod 2) := fun k j =>
    match k with
    | Sum.inl idx => s1 idx j
    | Sum.inr idx => s2 idx j
  have hPQ : ∑ idx ∈ NL, coeff idx • anchor u v (val (n + m + idx.val)) = P * Q := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    simp only [Matrix.sum_apply]
    rw [← Finset.sum_attach NL]
    refine Finset.sum_congr rfl fun idx _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, houter idx, Matrix.add_apply,
      Matrix.vecMulVec_apply, P, Q]
    ring
  rw [hPQ]
  calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
    _ = Module.finrank (ZMod 2) (LinearMap.range P.mulVecLin) := rfl
    _ ≤ Module.finrank (ZMod 2) (NL ⊕ NL → ZMod 2) := LinearMap.finrank_range_le P.mulVecLin
    _ = Fintype.card (NL ⊕ NL) := Module.finrank_pi (ZMod 2)
    _ = NL.card + NL.card := by simp
    _ ≤ 2 * t := by omega

private def Valid (n m : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.inputs.length ≤ 2) ∧ ReadsBack (n + m) ⟨gs, 0⟩

private theorem valid_nil (n m : ℕ) : Valid n m [] := by
  exact ⟨by simp, by simp [ReadsBack]⟩

private theorem valid_snoc {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) (g : Gate)
    (hlen : g.inputs.length ≤ 2) (hbound : ∀ a ∈ g.inputs, a < n + m + gs.length) :
    Valid n m (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hv.1 g' h
    · rw [List.mem_singleton.mp h]
      exact hlen
  · intro j hj a ha
    change j < (gs ++ [g]).length at hj
    change a ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at ha
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at ha
      exact hv.2 j hj' a ha
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at ha
      simp only [Nat.sub_self, List.getD_cons_zero] at ha
      exact hbound a ha

private theorem nlGate_or_nil : nlGate ⟨GateOp.or, []⟩ = false := rfl

private theorem nlGate_mod2 (a b : ℕ) : nlGate ⟨GateOp.mod 2, [a, b]⟩ = false := rfl

private theorem nlGate_not (a : ℕ) : nlGate ⟨GateOp.not, [a]⟩ = false := rfl

private theorem nlGate_and (a b : ℕ) : nlGate ⟨GateOp.and, [a, b]⟩ = true := rfl

private def pushFalse (gs : List Gate) : List Gate := gs ++ [⟨GateOp.or, []⟩]

private def pushXor (n m : ℕ) (gs : List Gate) (a b : ℕ) : List Gate :=
  gs ++ [⟨GateOp.mod 2, [a, b]⟩, ⟨GateOp.not, [n + m + gs.length]⟩]

private def pushAnd (gs : List Gate) (a b : ℕ) : List Gate :=
  gs ++ [⟨GateOp.and, [a, b]⟩]

private theorem pushFalse_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) :
    let gs' := pushFalse gs
    let w := n + m + gs.length
    Valid n m gs' ∧ gs'.length = gs.length + 1 ∧
    gs'.countP nlGate = gs.countP nlGate ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (depthsOf (n + m) gs').getD w 0 = 0 ∧
    (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD w false) = 0) := by
  refine ⟨valid_snoc hv _ (by simp) (by simp), by simp [pushFalse], ?_, ?_, ?_, ?_, ?_⟩
  · simp [pushFalse, List.countP_append, nlGate_or_nil]
  · intro k hk
    exact depthsOf_append_getD_lt (n + m) gs _ hk
  · intro i j k hk
    exact wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  · unfold pushFalse
    rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl : (depthsOf (n + m) gs).length = n + m + gs.length := depthsOf_length (n + m) gs
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl, nlGate_or_nil]
  · intro i j
    unfold pushFalse
    rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl : (wiresOf (oneEach i j) gs).length = n + m + gs.length := by
      rw [wiresOf_length, oneEach_length]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl, GateOp.eval, b2z]

private theorem pushXor_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) {a b : ℕ}
    (ha : a < n + m + gs.length) (hb : b < n + m + gs.length) :
    let gs' := pushXor n m gs a b
    let w := n + m + gs.length + 1
    Valid n m gs' ∧ gs'.length = gs.length + 2 ∧
    gs'.countP nlGate = gs.countP nlGate ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (depthsOf (n + m) gs').getD w 0 =
      max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) ∧
    (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD w false) =
      b2z ((wiresOf (oneEach i j) gs).getD a false) +
      b2z ((wiresOf (oneEach i j) gs).getD b false)) := by
  let g1 : Gate := ⟨GateOp.mod 2, [a, b]⟩
  let g2 : Gate := ⟨GateOp.not, [n + m + gs.length]⟩
  have hsplit : pushXor n m gs a b = (gs ++ [g1]) ++ [g2] := by
    simp [pushXor, g1, g2]
  have hv1 : Valid n m (gs ++ [g1]) := valid_snoc hv g1 (by simp [g1]) (by
    intro x hx; simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption)
  have hv2 : Valid n m ((gs ++ [g1]) ++ [g2]) := valid_snoc hv1 g2 (by simp [g2]) (by
    intro x hx; simp only [g2, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; simp)
  refine ⟨hsplit ▸ hv2, by simp [pushXor], ?_, ?_, ?_, ?_, ?_⟩
  · simp [pushXor, List.countP_append, nlGate_mod2, nlGate_not]
  · intro k hk
    exact depthsOf_append_getD_lt (n + m) gs _ hk
  · intro i j k hk
    exact wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  · rw [hsplit, depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl1 : (depthsOf (n + m) (gs ++ [g1])).length = n + m + gs.length + 1 := by
      rw [depthsOf_length]; simp; omega
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl1, Nat.sub_self, List.getD_cons_zero, g2, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, nlGate_not, Bool.toNat_false, add_zero, Nat.max_zero]
    rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (depthsOf (n + m) gs).length = n + m + gs.length := depthsOf_length (n + m) gs
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, g1, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, nlGate_mod2, Bool.toNat_false, add_zero, Nat.max_zero]
  · intro i j
    rw [hsplit, wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl1 : (wiresOf (oneEach i j) (gs ++ [g1])).length = n + m + gs.length + 1 := by
      rw [wiresOf_length, oneEach_length]; simp; omega
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl1, Nat.sub_self, List.getD_cons_zero, g2, List.map_cons, List.map_nil]
    rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (wiresOf (oneEach i j) gs).length = n + m + gs.length := by
      rw [wiresOf_length, oneEach_length]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, g1, List.map_cons, List.map_nil]
    generalize (wiresOf (oneEach i j) gs).getD a false = va
    generalize (wiresOf (oneEach i j) gs).getD b false = vb
    cases va <;> cases vb <;> decide

private theorem pushAnd_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) {a b : ℕ}
    (ha : a < n + m + gs.length) (hb : b < n + m + gs.length) :
    let gs' := pushAnd gs a b
    let w := n + m + gs.length
    Valid n m gs' ∧ gs'.length = gs.length + 1 ∧
    gs'.countP nlGate = gs.countP nlGate + 1 ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (depthsOf (n + m) gs').getD w 0 =
      max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) + 1 ∧
    (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD w false) =
      b2z ((wiresOf (oneEach i j) gs).getD a false) *
      b2z ((wiresOf (oneEach i j) gs).getD b false)) := by
  refine ⟨valid_snoc hv _ (by simp) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption), by simp [pushAnd], ?_, ?_, ?_, ?_, ?_⟩
  · simp [pushAnd, List.countP_append, nlGate_and]
  · intro k hk
    exact depthsOf_append_getD_lt (n + m) gs _ hk
  · intro i j k hk
    exact wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  · unfold pushAnd
    rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (depthsOf (n + m) gs).length = n + m + gs.length := depthsOf_length (n + m) gs
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, nlGate_and, Bool.toNat_true, Nat.max_zero]
  · intro i j
    unfold pushAnd
    rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (wiresOf (oneEach i j) gs).length = n + m + gs.length := by
      rw [wiresOf_length, oneEach_length]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, List.map_cons, List.map_nil]
    generalize (wiresOf (oneEach i j) gs).getD a false = va
    generalize (wiresOf (oneEach i j) gs).getD b false = vb
    cases va <;> cases vb <;> decide

private theorem build_xor_list {n m : ℕ} (D : ℕ) (ws : List ℕ) (gs : List Gate) (hv : Valid n m gs)
    (hb : ∀ w ∈ ws, w < n + m + gs.length)
    (hd : ∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ D) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 ≤ D ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) =
        (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false))).sum) := by
  induction ws generalizing gs with
  | nil =>
    obtain ⟨hv', hlen', hcnt', hdp', hwp', hdout, hwout⟩ := pushFalse_spec hv
    exact ⟨pushFalse gs, n + m + gs.length, hv', by omega, by omega, hcnt', hdp', hwp',
      by omega, fun i j => by simpa using hwout i j⟩
  | cons w ws ih =>
    have hw_lt : w < n + m + gs.length := hb w List.mem_cons_self
    have hw_d : (depthsOf (n + m) gs).getD w 0 ≤ D := hd w List.mem_cons_self
    obtain ⟨gs1, out1, hv1, hle1, hout1, hcnt1, hdp1, hwp1, hd1, hw1⟩ :=
      ih gs hv (fun a ha => hb a (List.mem_cons_of_mem w ha))
        (fun a ha => hd a (List.mem_cons_of_mem w ha))
    obtain ⟨hv2, hlen2, hcnt2, hdp2, hwp2, hd2, hw2⟩ :=
      pushXor_spec hv1 (by omega : w < n + m + gs1.length) hout1
    refine ⟨pushXor n m gs1 w out1, n + m + gs1.length + 1, hv2, by omega, by omega,
      by omega, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [hdp2 k (by omega), hdp1 k hk]
    · intro i j k hk
      rw [hwp2 i j k (by omega), hwp1 i j k hk]
    · rw [hd2, hdp1 w hw_lt]
      exact max_le hw_d hd1
    · intro i j
      rw [hw2 i j, hwp1 i j w hw_lt, hw1 i j]
      simp

private theorem build_row_fn {n m : ℕ} (f : Fin n → ZMod 2) (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 = 0 ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) = f i) := by
  let ws : List ℕ := ((List.finRange n).filter (fun k : Fin n => decide (f k = 1))).map Fin.val
  have hwb : ∀ w ∈ ws, w < n + m + gs.length := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    omega
  have hwd : ∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ 0 := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    rw [depthsOf_getD_input (n + m) gs (by omega)]
  obtain ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', hdout', hwout'⟩ :=
    build_xor_list 0 ws gs hv hwb hwd
  refine ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', by omega, fun i j => ?_⟩
  rw [hwout' i j]
  have hsum : (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false))).sum =
      ∑ k : Fin n, if f k = 1 then (if k = i then (1 : ZMod 2) else 0) else 0 := by
    have hmap : ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false)) =
        ((List.finRange n).filter (fun k : Fin n => decide (f k = 1))).map
          (fun k : Fin n => if k = i then (1 : ZMod 2) else 0) := by
      unfold ws
      rw [List.map_map]
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_apply]
      rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; omega), oneEach_getD_left i j k.isLt]
      by_cases hki : k = i
      · subst hki; simp [b2z]
      · have hne : k.val ≠ i.val := fun e => hki (Fin.ext e)
        simp [b2z, hki, hne]
    rw [hmap]
    have hfilt : ∀ (l : List (Fin n)),
        ((l.filter (fun k => decide (f k = 1))).map (fun k => if k = i then (1 : ZMod 2) else 0)).sum =
        (l.map (fun k => if f k = 1 then (if k = i then (1 : ZMod 2) else 0) else 0)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ihl =>
        rw [List.filter_cons]
        by_cases hfa : f a = 1 <;> simp [hfa, ihl]
    rw [hfilt]
    rw [← Fin.sum_univ_def]
  rw [hsum]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    exact zmod2_ite_eq (f i)
  · intro k _ hki
    simp [hki]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem build_col_fn {n m : ℕ} (g : Fin m → ZMod 2) (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 = 0 ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) = g j) := by
  let ws : List ℕ :=
    ((List.finRange m).filter (fun k : Fin m => decide (g k = 1))).map (fun k => n + k.val)
  have hwb : ∀ w ∈ ws, w < n + m + gs.length := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    omega
  have hwd : ∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ 0 := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    rw [depthsOf_getD_input (n + m) gs (by omega)]
  obtain ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', hdout', hwout'⟩ :=
    build_xor_list 0 ws gs hv hwb hwd
  refine ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', by omega, fun i j => ?_⟩
  rw [hwout' i j]
  have hsum : (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false))).sum =
      ∑ k : Fin m, if g k = 1 then (if k = j then (1 : ZMod 2) else 0) else 0 := by
    have hmap : ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false)) =
        ((List.finRange m).filter (fun k : Fin m => decide (g k = 1))).map
          (fun k : Fin m => if k = j then (1 : ZMod 2) else 0) := by
      unfold ws
      rw [List.map_map]
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_apply]
      rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; omega),
        oneEach_getD_right i j (by omega) (by omega)]
      simp only [Nat.add_sub_cancel_left]
      by_cases hkj : k = j
      · subst hkj; simp [b2z]
      · have hne : k.val ≠ j.val := fun e => hkj (Fin.ext e)
        simp [b2z, hkj, hne]
    rw [hmap]
    have hfilt : ∀ (l : List (Fin m)),
        ((l.filter (fun k => decide (g k = 1))).map (fun k => if k = j then (1 : ZMod 2) else 0)).sum =
        (l.map (fun k => if g k = 1 then (if k = j then (1 : ZMod 2) else 0) else 0)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ihl =>
        rw [List.filter_cons]
        by_cases hga : g a = 1 <;> simp [hga, ihl]
    rw [hfilt]
    rw [← Fin.sum_univ_def]
  rw [hsum]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true]
    exact zmod2_ite_eq (g j)
  · intro k _ hkj
    simp [hkj]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem build_pair_and {n m : ℕ} (a b : Fin n → ZMod 2) (c d : Fin m → ZMod 2)
    (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate + 1 ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 ≤ 1 ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) =
        (a i + d j) * (b i + c j)) := by
  obtain ⟨gs1, wa, hv1, hl1, hwa, hc1, hd1, hw1, hda, hfa⟩ := build_row_fn a gs hv
  obtain ⟨gs2, wd, hv2, hl2, hwd, hc2, hd2, hw2, hdd, hfd⟩ := build_col_fn d gs1 hv1
  obtain ⟨hv3, hl3, hc3, hd3, hw3, hdL, hwL⟩ :=
    pushXor_spec hv2 (by omega : wa < n + m + gs2.length) hwd
  set gs3 := pushXor n m gs2 wa wd
  let wL := n + m + gs2.length + 1
  obtain ⟨gs4, wb, hv4, hl4, hwb, hc4, hd4, hw4, hdb, hfb⟩ := build_row_fn b gs3 hv3
  obtain ⟨gs5, wc, hv5, hl5, hwc, hc5, hd5, hw5, hdc, hfc⟩ := build_col_fn c gs4 hv4
  obtain ⟨hv6, hl6, hc6, hd6, hw6, hdR, hwR⟩ :=
    pushXor_spec hv5 (by omega : wb < n + m + gs5.length) hwc
  set gs6 := pushXor n m gs5 wb wc
  let wR := n + m + gs5.length + 1
  obtain ⟨hv7, hl7, hc7, hd7, hw7, hdP, hwP⟩ :=
    pushAnd_spec hv6 (by omega : wL < n + m + gs6.length) (by omega : wR < n + m + gs6.length)
  set gs7 := pushAnd gs6 wL wR
  let out := n + m + gs6.length
  refine ⟨gs7, out, hv7, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hd7 k (by omega), hd6 k (by omega), hd5 k (by omega), hd4 k (by omega),
      hd3 k (by omega), hd2 k (by omega), hd1 k hk]
  · intro i j k hk
    rw [hw7 i j k (by omega), hw6 i j k (by omega), hw5 i j k (by omega), hw4 i j k (by omega),
      hw3 i j k (by omega), hw2 i j k (by omega), hw1 i j k hk]
  · rw [hdP]
    have hL0 : (depthsOf (n + m) gs6).getD wL 0 = 0 := by
      rw [hd6 wL (by omega), hd5 wL (by omega), hd4 wL (by omega), hdL, hd2 wa hwa, hda, hdd]
      simp
    have hR0 : (depthsOf (n + m) gs6).getD wR 0 = 0 := by
      rw [hdR, hd5 wb hwb, hdb, hdc]
      simp
    rw [hL0, hR0]
    simp
  · intro i j
    rw [hwP i j]
    have hLv : b2z ((wiresOf (oneEach i j) gs6).getD wL false) = a i + d j := by
      rw [hw6 i j wL (by omega), hw5 i j wL (by omega), hw4 i j wL (by omega),
        hwL i j, hw2 i j wa hwa, hfa i j, hfd i j]
    have hRv : b2z ((wiresOf (oneEach i j) gs6).getD wR false) = b i + c j := by
      rw [hwR i j, hw5 i j wb hwb, hfb i j, hfc i j]
    rw [hLv, hRv]

private theorem build_many_pairs {n m : ℕ} (t : ℕ)
    (a b : Fin t → Fin n → ZMod 2) (c d : Fin t → Fin m → ZMod 2)
    (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (ws : List ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧
      (∀ w ∈ ws, w < n + m + gs'.length) ∧
      (∀ w ∈ ws, (depthsOf (n + m) gs').getD w 0 ≤ 1) ∧
      gs'.countP nlGate = gs.countP nlGate + t ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (∀ (i : Fin n) (j : Fin m), (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs').getD w false))).sum =
        ∑ p : Fin t, (a p i + d p j) * (b p i + c p j)) := by
  induction t generalizing gs with
  | zero =>
    exact ⟨gs, [], hv, le_rfl, by simp, by simp, by simp, fun _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ => by simp⟩
  | succ t ih =>
    obtain ⟨gs1, w0, hv1, hl1, hw0, hc1, hd1, hwp1, hdw0, hfv0⟩ :=
      build_pair_and (a 0) (b 0) (c 0) (d 0) gs hv
    obtain ⟨gs2, ws, hv2, hl2, hws, hdws, hc2, hd2, hwp2, hsum⟩ :=
      ih (fun p => a p.succ) (fun p => b p.succ) (fun p => c p.succ) (fun p => d p.succ) gs1 hv1
    refine ⟨gs2, w0 :: ws, hv2, by omega, ?_, ?_, by omega, ?_, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · omega
      · exact hws w hw
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · rw [hd2 w hw0]; exact hdw0
      · exact hdws w hw
    · intro k hk
      rw [hd2 k (by omega), hd1 k hk]
    · intro i j k hk
      rw [hwp2 i j k (by omega), hwp1 i j k hk]
    · intro i j
      rw [List.map_cons, List.sum_cons, hwp2 i j w0 hw0, hfv0 i j, hsum i j, Fin.sum_univ_succ]

private theorem dir_ge {n m : ℕ} (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ)
    (hr : (anchor u v (fun i j => b2z (G i j))).rank ≤ 2 * t) :
    ∃ C : Circuit,
      ((∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ ReadsBack (n + m) C ∧ Represents G C) ∧
      (depthsOf (n + m) C.gates).getD C.output 0 ≤ 1 ∧
      C.gates.countP nlGate ≤ t := by
  obtain ⟨rowVec, colVec, hfac⟩ := factor_of_rank_le (anchor u v (fun i j => b2z (G i j))) hr
  let a : Fin t → Fin n → ZMod 2 := fun p => rowVec ⟨2 * p.val, by omega⟩
  let b : Fin t → Fin n → ZMod 2 := fun p => rowVec ⟨2 * p.val + 1, by omega⟩
  let c : Fin t → Fin m → ZMod 2 := fun p => colVec ⟨2 * p.val, by omega⟩
  let d : Fin t → Fin m → ZMod 2 := fun p => colVec ⟨2 * p.val + 1, by omega⟩
  let R : Fin n → ZMod 2 := fun i => b2z (G i v) + b2z (G u v) + ∑ p : Fin t, a p i * b p i
  let S : Fin m → ZMod 2 := fun j => b2z (G u j) + ∑ p : Fin t, c p j * d p j
  have hdecomp : ∀ i j, b2z (G i j) = R i + S j + ∑ p : Fin t, (a p i + d p j) * (b p i + c p j) := by
    intro i j
    have hA := hfac i j
    have hpair : ∑ k : Fin (2 * t), rowVec k i * colVec k j =
        ∑ p : Fin t, (a p i * c p j + b p i * d p j) := by
      let e : Fin t × Fin 2 ≃ Fin (2 * t) := {
        toFun := fun x => ⟨2 * x.1.val + x.2.val, by omega⟩
        invFun := fun k => (⟨k.val / 2, by omega⟩, ⟨k.val % 2, by omega⟩)
        left_inv := fun ⟨p, q⟩ => by
          ext
          · simp; omega
          · simp; omega
        right_inv := fun k => by
          ext
          simp
          omega
      }
      rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Fin.sum_univ_two]
      rfl
    rw [hpair] at hA
    simp only [anchor] at hA
    have hterm : ∑ p : Fin t, (a p i + d p j) * (b p i + c p j) =
        ∑ p : Fin t, (a p i * b p i + c p j * d p j) +
        ∑ p : Fin t, (a p i * c p j + b p i * d p j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [hterm, ← hA]
    simp only [R, S, Finset.sum_add_distrib]
    have h2 : (b2z (G i v) + b2z (G u v) + ∑ p : Fin t, a p i * b p i) +
        (b2z (G u j) + ∑ p : Fin t, c p j * d p j) +
        ((∑ p : Fin t, a p i * b p i + ∑ p : Fin t, c p j * d p j) +
        (b2z (G i j) + b2z (G i v) + b2z (G u j) + b2z (G u v))) =
        b2z (G i j) + (2 : ZMod 2) * (b2z (G i v) + b2z (G u j) + b2z (G u v) +
          ∑ p : Fin t, a p i * b p i + ∑ p : Fin t, c p j * d p j) := by ring
    rw [h2, zmod2_two, zero_mul, add_zero]
  obtain ⟨gs1, wR, hv1, hl1, hwR, hc1, _, _, hdR, hfR⟩ := build_row_fn R [] (valid_nil n m)
  obtain ⟨gs2, wS, hv2, hl2, hwS, hc2, hd2, hw2, hdS, hfS⟩ := build_col_fn S gs1 hv1
  obtain ⟨gs3, ws, hv3, hl3, hws, hdws, hc3, hd3, hw3, hsum3⟩ :=
    build_many_pairs t a b c d gs2 hv2
  obtain ⟨gs4, out, hv4, hl4, hout, hc4, hd4, hw4, hdout, hwout⟩ :=
    build_xor_list 1 (wR :: wS :: ws) gs3 hv3
      (by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · omega
        · rcases List.mem_cons.mp hw with rfl | hw
          · omega
          · exact hws w hw)
      (by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · rw [hd3 w (by omega), hd2 w hwR, hdR]; omega
        · rcases List.mem_cons.mp hw with rfl | hw
          · rw [hd3 w hwS, hdS]; omega
          · exact hdws w hw)
  refine ⟨⟨gs4, out⟩, ⟨hv4.1, hv4.2, ?_⟩, hdout, ?_⟩
  · intro i j
    apply b2z_inj
    change b2z ((wiresOf (oneEach i j) gs4).getD out false) = b2z (G i j)
    rw [hwout i j]
    simp only [List.map_cons, List.sum_cons]
    rw [hw3 i j wR (by omega), hw2 i j wR hwR, hfR i j,
      hw3 i j wS hwS, hfS i j, hsum3 i j, hdecomp i j]
    ring
  · change gs4.countP nlGate ≤ t
    simp only [List.countP_nil] at hc1
    omega

private theorem main (n m : ℕ) (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ) :
    (anchor u v (fun i j => b2z (G i j))).rank ≤ 2 * t ↔
      ∃ C : Circuit,
        ((∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ ReadsBack (n + m) C ∧ Represents G C) ∧
        (depthsOf (n + m) C.gates).getD C.output 0 ≤ 1 ∧
        C.gates.countP nlGate ≤ t :=
  ⟨dir_ge G u v t, fun ⟨C, ⟨hlen, hrb, hrep⟩, hd1, hcnt⟩ => dir_le G u v t C hlen hrb hrep hd1 hcnt⟩

private def Cheap {n m : ℕ} (G : Fin n → Fin m → Bool) (t : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : Fin 1 → ℕ), ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nlGate ≤ t ∧
    ∀ j : Fin 1, (depthsOf (n+m) C.gates).getD (tap j) 0 ≤ 1 ∧
      Represents G ⟨C.gates, tap j⟩

private lemma cheap_iff {n m : ℕ} (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ) :
    Cheap G t ↔ (anchor u v (fun i j => b2z (G i j))).rank ≤ 2*t := by
  rw [main n m G u v t]
  constructor
  · rintro ⟨C, tap, rb, arity, budget, hout⟩
    exact ⟨⟨C.gates, tap 0⟩, ⟨arity, rb, (hout 0).2⟩, (hout 0).1, budget⟩
  · rintro ⟨C, ⟨arity, rb, rep⟩, depth, budget⟩
    exact ⟨C, fun _ => C.output, rb, arity, budget, fun _ => ⟨depth, rep⟩⟩

private lemma zmod_of_bool_pred (a : ZMod 2) : b2z (decide (a ≠ 0)) = a := by
  fin_cases a
  · change b2z (decide ((0 : ZMod 2) ≠ 0)) = 0
    decide
  · change b2z (decide ((1 : ZMod 2) ≠ 0)) = 1
    decide

section Pairing

open Module

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {k : ℕ}

private noncomputable def pairCoordinates (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) :
    K →ₗ[F] (Fin k → F) :=
  LinearMap.pi fun i => bit.comp (LinearMap.mulLeft F (b i))

private theorem pairCoordinates_apply (b : Basis (Fin k) F K)
    (bit : K →ₗ[F] F) (x : K) (i : Fin k) :
    pairCoordinates b bit x i = bit (b i * x) := rfl

private noncomputable def pairEquiv (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hbit : bit ≠ 0) :
    K ≃ₗ[F] (Fin k → F) := by
  letI : FiniteDimensional F K := b.finiteDimensional_of_finite
  have dim : finrank F K = finrank F (Fin k → F) := by
    simp [Module.finrank_eq_card_basis b]
  have hinj : Function.Injective (pairCoordinates b bit) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hn
    have hz : bit.comp (LinearMap.mulLeft F x) = 0 := by
      apply b.ext
      intro i
      have hi := congrFun (LinearMap.mem_ker.mp hx) i
      simpa [pairCoordinates_apply, mul_comm x (b i)] using hi
    apply hbit
    ext y
    have hy := DFunLike.congr_fun hz (x⁻¹ * y)
    simpa [← mul_assoc, mul_inv_cancel₀ hn] using hy
  exact LinearEquiv.ofBijective (pairCoordinates b bit)
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mp hinj⟩

private noncomputable def pairMatrix (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (C : K →ₗ[F] K) : Matrix (Fin k) (Fin k) F :=
  fun i j => bit (b i * C (b j))

private theorem pair_toLin_entry (b : Basis (Fin k) F K) (A : Matrix (Fin k) (Fin k) F)
    (i j : Fin k) : Matrix.toLin b (Pi.basisFun F _) A (b j) i = A i j := by
  rw [Matrix.toLin_self]
  simp [Pi.single_apply, mul_ite]

private theorem rank_pairMatrix (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (C : K →ₗ[F] K) :
    (pairMatrix b bit C).rank = finrank F (LinearMap.range C) := by
  rw [Matrix.rank_eq_finrank_range_toLin _ (Pi.basisFun F _) b]
  have h : Matrix.toLin b (Pi.basisFun F _) (pairMatrix b bit C) =
      (pairEquiv b bit hbit).toLinearMap.comp C := by
    apply b.ext
    intro j
    funext i
    rw [pair_toLin_entry]
    rfl
  rw [h, LinearMap.range_comp, LinearEquiv.finrank_map_eq]

private noncomputable def pairAnchor (A : Matrix (Fin k) (Fin k) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F :=
  fun i j => Fin.cases 0 (fun i => Fin.cases 0 (A i) j) i

@[local simp] private theorem pairAnchor_zero_left (A : Matrix (Fin k) (Fin k) F) (j : Fin (k + 1)) :
    pairAnchor A 0 j = 0 := rfl

@[local simp] private theorem pairAnchor_zero_right (A : Matrix (Fin k) (Fin k) F) (i : Fin (k + 1)) :
    pairAnchor A i 0 = 0 := by
  refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

@[local simp] private theorem pairAnchor_succ_succ (A : Matrix (Fin k) (Fin k) F) (i j : Fin k) :
    pairAnchor A i.succ j.succ = A i j := rfl

private theorem rank_pairAnchor (A : Matrix (Fin k) (Fin k) F) : (pairAnchor A).rank = A.rank := by
  classical
  let e : (Fin k → F) →ₗ[F] (Fin (k + 1) → F) :=
    { toFun := Fin.cases 0
      map_add' := by
        intro x y
        funext i
        refine Fin.cases ?_ (fun _ => rfl) i
        simp
      map_smul' := by
        intro a x
        funext i
        refine Fin.cases ?_ (fun _ => rfl) i
        simp }
  let p : (Fin (k + 1) → F) →ₗ[F] (Fin k → F) :=
    { toFun := fun x i => x i.succ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he : Function.Injective e := fun _ _ h => funext fun i => congrFun h i.succ
  have hp : LinearMap.range p = ⊤ :=
    LinearMap.range_eq_top.mpr (fun x => ⟨e x, rfl⟩)
  have heq : (pairAnchor A).mulVecLin = e.comp (A.mulVecLin.comp p) := by
    ext x i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [e, Matrix.mulVec, dotProduct]
    · simp [e, p, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [Matrix.rank, Matrix.rank, heq, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ hp]
  exact (Submodule.equivMapOfInjective e he _).finrank_eq.symm

private theorem rank_pairAnchor_pairMatrix (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (C : K →ₗ[F] K) :
    (pairAnchor (pairMatrix b bit C)).rank = finrank F (LinearMap.range C) :=
  (rank_pairAnchor _).trans (rank_pairMatrix b bit hbit C)

private theorem pairAnchor_pairMatrix_apply (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (C : K →ₗ[F] K) (i j : Fin (k + 1)) :
    pairAnchor (pairMatrix b bit C) i j =
      bit (Fin.cases 0 b i * C (Fin.cases 0 b j)) := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) j) i
  · simp
  · simp
  · rfl

end Pairing
section Bridges

open Module
variable {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
variable {k : ℕ} (b : Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2)

private def pairingDual : K →ₗ[ZMod 2] Module.Dual (ZMod 2) K where
  toFun x := bit.comp (LinearMap.mulLeft (ZMod 2) x)
  map_add' x y := by ext z; simp [add_mul]
  map_smul' a x := by ext z; simp [smul_mul_assoc]

include b in
private theorem pairingDual_bij (hb : bit ≠ 0) : Function.Bijective (pairingDual bit) := by
  have h : Function.Injective (pairingDual bit) := by
    intro x y hxy
    apply (pairEquiv b bit hb).injective
    funext i
    have hi := DFunLike.congr_fun hxy (b i)
    change bit (b i * x) = bit (b i * y)
    simpa [pairingDual, mul_comm] using hi
  exact ⟨h, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ZMod 2) (V := K)).symm).mp h⟩

private noncomputable def servedSet (W : Submodule (ZMod 2) K) : Finset K := by
  classical
  letI : Finite K := Module.finite_of_finite (ZMod 2)
  letI := Fintype.ofFinite K
  exact Finset.univ.filter fun z => ∃ w ∈ W, bit (z⁻¹ * w) ≠ 0

private theorem mem_servedSet (W : Submodule (ZMod 2) K) (z : K) :
    z ∈ servedSet bit W ↔ ∃ w ∈ W, bit (z⁻¹ * w) ≠ 0 := by
  classical
  unfold servedSet
  simp

include b in
private theorem card_servedSet (hb : bit ≠ 0) (W : Submodule (ZMod 2) K) :
    (servedSet bit W).card = 2^k - 2^(k - finrank (ZMod 2) W) := by
  classical
  letI : Finite K := Module.finite_of_finite (ZMod 2)
  letI := Fintype.ofFinite K
  let e := Equiv.inv K |>.trans (Equiv.ofBijective _ (pairingDual_bij b bit hb))
  let P := (Finset.univ : Finset K).filter fun z => ¬ ∃ w ∈ W, bit (z⁻¹ * w) ≠ 0
  have hP : P.card = Nat.card W.dualAnnihilator := by
    rw [← Fintype.card_coe P, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    exact e.subtypeEquiv fun z => by
      simp [P, Submodule.mem_dualAnnihilator, e, pairingDual]
  have hW : Nat.card W.dualAnnihilator = 2^(k - finrank (ZMod 2) W) := by
    letI : Finite W.dualAnnihilator := Module.finite_of_finite (ZMod 2)
    letI := Fintype.ofFinite W.dualAnnihilator
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    have hh := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin] at hh
    congr 1
    omega
  have hK : Fintype.card K = 2^k := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, Module.finrank_eq_card_basis b,
      Fintype.card_fin]
  have ha : (servedSet bit W).card + P.card = Fintype.card K := by
    unfold servedSet
    exact Finset.card_filter_add_card_filter_not _
  omega

private theorem detect_span {ι : Type*} (f : ι → K) (z : K) :
    z ∈ servedSet bit (Submodule.span (ZMod 2) (Set.range f)) ↔
      ∃ i, bit (z⁻¹ * f i) ≠ 0 := by
  rw [mem_servedSet]
  constructor
  · contrapose!
    intro h w hw
    have hk : Submodule.span (ZMod 2) (Set.range f) ≤ (pairingDual bit z⁻¹).ker :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
    exact hk hw
  · rintro ⟨i, hi⟩
    exact ⟨f i, Submodule.subset_span (Set.mem_range_self i), hi⟩

private lemma b2z_and (x y : Bool) : b2z (x && y) = b2z x * b2z y := by
  cases x <;> cases y <;> decide

private lemma b2z_parity {ι : Type*} (S : Finset ι) (f : ι → Bool) :
    b2z (((S.filter (fun i => f i)).card % 2) == 1) = ∑ i ∈ S, b2z (f i) := by
  classical
  have hcast (a : ℕ) : b2z ((a % 2) == 1) = (a : ZMod 2) := by
    obtain ⟨j, h⟩ : ∃ j : Fin 2, a % 2 = j.val := ⟨⟨_, Nat.mod_lt _ (by decide)⟩, rfl⟩
    have he : (a : ZMod 2) = ((a % 2 : ℕ) : ZMod 2) := (ZMod.natCast_mod a 2).symm
    rw [he, h]
    fin_cases j <;> decide
  rw [hcast]
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.filter_insert]
    cases h : f i
    · simpa [h, b2z] using ih
    · rw [if_pos (by simp [h]), Finset.card_insert_of_notMem (by simp [hi]), Nat.cast_add, ih]
      simp [h, b2z, add_comm]

private noncomputable def productTable (z : K) (x y : Fin (k+1)) : Bool :=
  decide (bit (z * Fin.cases 0 b x * Fin.cases 0 b y) ≠ 0)

private noncomputable def residualTable {s : ℕ} (T : Fin s → Fin (k+1) → Fin (k+1) → Bool)
    (S : Finset (Fin s)) (z : K) (x y : Fin (k+1)) : Bool :=
  xor (productTable b bit z x y) (((S.filter (fun i => T i x y)).card % 2) == 1)

private theorem residual_anchor_formula {s : ℕ} (A B : Fin s → Fin (k+1) → Bool)
    (S : Finset (Fin s)) (z : K) (x y : Fin (k+1)) :
    anchor 0 0 (fun x y => b2z (residualTable b bit (fun i x y => A i x && B i y) S z x y)) x y =
      bit (z * Fin.cases 0 b x * Fin.cases 0 b y) +
        ∑ i ∈ S, (b2z (A i x) + b2z (A i 0)) * (b2z (B i y) + b2z (B i 0)) := by
  simp only [anchor, residualTable, productTable, b2z_xor, zmod_of_bool_pred,
    b2z_parity, b2z_and, Fin.cases_zero, zero_mul, mul_zero, map_zero, zero_add]
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  ac_rfl

private theorem represent_factor (hb : bit ≠ 0) (A : Fin (k+1) → Bool) :
    ∃ a : K, ∀ x, b2z (A x) + b2z (A 0) = bit (a * Fin.cases 0 b x) := by
  obtain ⟨a, ha⟩ := (pairEquiv b bit hb).surjective (fun i => b2z (A i.succ) + b2z (A 0))
  refine ⟨a, fun x => Fin.cases ?_ (fun i => ?_) x⟩
  · simp [zmod2_add_self]
  · have h := congrFun ha i
    change bit (b i * a) = _ at h
    simpa [mul_comm] using h.symm

end Bridges
section Chain

open Module
open scoped Pointwise
variable {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]

private def triangle (s : ℕ) : ℕ := s*(s+1)/2

private theorem triangle_succ (s : ℕ) : triangle (s+1) = triangle s + (s+1) := by
  have ht (x : ℕ) : triangle x = ∑ i ∈ Finset.range (x+1), i := by
    rw [Finset.sum_range_id]
    simp [triangle, Nat.mul_comm]
  simp only [ht, Finset.sum_range_succ (n := s+1)]

private abbrev Triangle (s : ℕ) := {ij : Fin s × Fin s // ij.2 ≤ ij.1}

private theorem card_triangle (s : ℕ) : Fintype.card (Triangle s) ≤ triangle s := by
  classical
  let f (ij : Triangle s) : Fin (triangle s) :=
    ⟨triangle ij.1.1.val + ij.1.2.val, by
      have h₁ : ∀ a b, a ≤ b → triangle a ≤ triangle b := by
        intro a b hab
        exact Nat.div_le_div_right (Nat.mul_le_mul hab (by omega : a+1 ≤ b+1))
      have h₂ := h₁ (ij.1.1.val+1) s (by omega)
      have h₃ : ij.1.2.val ≤ ij.1.1.val := ij.2
      rw [triangle_succ] at h₂
      omega⟩
  rw [← Fintype.card_fin (triangle s)]
  apply Fintype.card_le_of_injective f
  intro u v h
  have he : triangle u.1.1.val + u.1.2.val = triangle v.1.1.val + v.1.2.val := congrArg Fin.val h
  have hm : Monotone triangle := by
    intro a b hab
    exact Nat.div_le_div_right (Nat.mul_le_mul hab (by omega : a+1 ≤ b+1))
  have hbound (w : Triangle s) : triangle w.1.1.val + w.1.2.val < triangle (w.1.1.val+1) := by
    have h₁ : w.1.2.val ≤ w.1.1.val := w.2
    rw [triangle_succ]; omega
  have hh : u.1.1.val = v.1.1.val := by
    rcases lt_trichotomy u.1.1.val v.1.1.val with hlt | heq | hgt
    · have := hm (show u.1.1.val + 1 ≤ v.1.1.val by omega)
      have := hbound u
      omega
    · exact heq
    · have := hm (show v.1.1.val + 1 ≤ u.1.1.val by omega)
      have := hbound v
      omega
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext hh
  · apply Fin.ext
    rw [hh] at he
    omega

private def prefixSpan (d : ℕ → K) (s : ℕ) : Submodule (ZMod 2) K :=
  Submodule.span (ZMod 2) (Set.range (fun i : Fin s => d i.val))

private theorem prefix_succ (d : ℕ → K) (s : ℕ) :
    prefixSpan d (s+1) = prefixSpan d s ⊔ Submodule.span (ZMod 2) {d s} := by
  unfold prefixSpan
  rw [← Submodule.span_union]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Or.inr rfl
    · exact Or.inl ⟨j, rfl⟩
  · rintro (⟨j, rfl⟩ | h)
    · exact ⟨j.castSucc, rfl⟩
    · exact ⟨Fin.last s, h.symm⟩

private theorem square_prefix {s : ℕ} (a : Fin s → K) :
    Submodule.span (ZMod 2) (Set.range a) * Submodule.span (ZMod 2) (Set.range a) =
    Submodule.span (ZMod 2) (Set.range fun ij : Fin s × Fin s => a ij.1 * a ij.2) := by
  rw [Submodule.span_mul_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact ⟨(i, j), rfl⟩
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact Set.mul_mem_mul (Set.mem_range_self _) (Set.mem_range_self _)

private theorem square_append (U : Submodule (ZMod 2) K) (x : K) :
    let V := U ⊔ Submodule.span (ZMod 2) {x}
    V * V = U * U ⊔ U.map (LinearMap.mulRight (ZMod 2) x) ⊔ Submodule.span (ZMod 2) {x^2} := by
  dsimp only
  have hmap : U * Submodule.span (ZMod 2) {x} = U.map (LinearMap.mulRight (ZMod 2) x) := by
    ext z
    exact Submodule.mem_mul_span_singleton
  have hsq : Submodule.span (ZMod 2) {x} * Submodule.span (ZMod 2) {x} =
      Submodule.span (ZMod 2) {x^2} := by
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton, pow_two]
  rw [Submodule.sup_mul, Submodule.mul_sup, Submodule.mul_sup,
    mul_comm (Submodule.span (ZMod 2) {x}) U, hmap, hsq]
  simp [sup_assoc]

private theorem finrank_append (U : Submodule (ZMod 2) K) (x : K) (hx : x ∉ U) :
    finrank (ZMod 2) (U ⊔ Submodule.span (ZMod 2) {x} : Submodule (ZMod 2) K) =
      finrank (ZMod 2) U + 1 := by
  have hx₀ : x ≠ 0 := fun h => hx (h ▸ U.zero_mem)
  have hd : Disjoint U (Submodule.span (ZMod 2) {x}) := by
    rw [disjoint_iff, Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy.2
    by_cases h : a = 0
    · simpa [h] using ha.symm
    · exact (hx ((Submodule.smul_mem_iff U h).mp (ha ▸ hy.1))).elim
  have he := Submodule.finrank_sup_add_finrank_inf_eq U (Submodule.span (ZMod 2) {x})
  rw [hd.eq_bot, finrank_bot, add_zero, finrank_span_singleton hx₀] at he
  exact he

set_option maxHeartbeats 2000000 in
private theorem chain_exists
    (growth : ∀ U : Submodule (ZMod 2) K, ∃ x : K,
      let V := U ⊔ Submodule.span (ZMod 2) {x}
      finrank (ZMod 2) (V*V) = min (finrank (ZMod 2) K)
        (finrank (ZMod 2) (U*U) + finrank (ZMod 2) U + 1))
    {r : ℕ} (seed : Fin r → K) (hs : LinearIndependent (ZMod 2) seed) :
    let baseRank := finrank (ZMod 2) (Submodule.span (ZMod 2)
      (Set.range (fun ij : Fin r × Fin r => seed ij.1 * seed ij.2)))
    ∃ d : ℕ → K, (∀ i : Fin r, d i.val = seed i) ∧ ∀ j : ℕ,
      let s := r+j
      finrank (ZMod 2) (Submodule.span (ZMod 2)
        (Set.range fun ij : Fin s × Fin s => d ij.1.val * d ij.2.val)) =
        min (finrank (ZMod 2) K) (baseRank+r*j+triangle j) := by
  classical
  let N := finrank (ZMod 2) K
  let U₀ := Submodule.span (ZMod 2) (Set.range seed)
  let f : Submodule (ZMod 2) K → K := fun U => Classical.choose (growth U)
  let U : ℕ → Submodule (ZMod 2) K := Nat.rec U₀ (fun _ U => U ⊔ Submodule.span (ZMod 2) {f U})
  let d : ℕ → K := fun i => if h : i < r then seed ⟨i,h⟩ else f (U (i-r))
  refine ⟨d, fun i => dif_pos i.isLt, ?_⟩
  have hp (j : ℕ) : prefixSpan d (r+j) = U j := by
    induction j with
    | zero =>
      change prefixSpan d r = U₀
      unfold prefixSpan U₀
      congr 1
      exact congrArg Set.range (funext fun i => dif_pos i.isLt)
    | succ j ih =>
      change prefixSpan d (r+j+1) = U j ⊔ Submodule.span (ZMod 2) {f (U j)}
      rw [prefix_succ, ih]
      have hh : d (r+j) = f (U j) := by simp [d]
      rw [hh]
  let dim : Submodule (ZMod 2) K → ℕ := fun V => finrank (ZMod 2) V
  have hstep (j : ℕ) : dim (U (j+1)*U (j+1)) = min N (dim (U j*U j) + dim (U j) + 1) := by
    change dim ((U j ⊔ Submodule.span (ZMod 2) {f (U j)}) *
      (U j ⊔ Submodule.span (ZMod 2) {f (U j)})) = _
    exact Classical.choose_spec (growth (U j))
  let a := dim (U₀*U₀)
  have W (j : ℕ) : dim (U j*U j) = min N (a+r*j+triangle j) ∧
      (dim (U j*U j) < N → dim (U j) = r+j) := by
    induction j with
    | zero =>
      have ha : a ≤ N := Submodule.finrank_le _
      refine ⟨?_, fun _ => ?_⟩
      · change a = min N a
        exact (min_eq_right ha).symm
      · simpa [dim, U, U₀] using finrank_span_eq_card hs
    | succ j ih =>
      rw [hstep, triangle_succ, Nat.mul_succ]
      let w := dim (U j*U j)
      let u := dim (U j)
      by_cases hw : w < N
      · have hu : u = r+j := ih.2 hw
        have hh : w = a+r*j+triangle j := by omega
        refine ⟨by omega, ?_⟩
        intro hn
        have hx : f (U j) ∉ U j := by
          intro hx
          have he : U (j+1) = U j :=
            sup_eq_left.mpr (Submodule.span_le.mpr (by simpa using hx))
          have hh' := hstep j
          rw [he] at hh'
          omega
        change dim (U j ⊔ Submodule.span (ZMod 2) {f (U j)}) = _
        have hs' := finrank_append (U j) (f (U j)) hx
        change dim (U j ⊔ Submodule.span (ZMod 2) {f (U j)}) = dim (U j) + 1 at hs'
        rw [hs']
        omega
      · have hh : w = N := by have := Submodule.finrank_le (U j*U j); omega
        exact ⟨by omega, by omega⟩
  intro j
  dsimp only
  rw [← square_prefix (fun i : Fin (r+j) => d i.val), ← square_prefix seed]
  change dim (prefixSpan d (r+j) * prefixSpan d (r+j)) = _
  rw [hp]
  exact (W j).1

end Chain
-- Uses the single-bank builders and AND append specification from
-- PEqualNP/Outside/L_meta_25830.lean at c041cec7a3792f85383b96bde660f88d6fbd8671.
-- The construction below retains each AND output as a separate tap.
private theorem b2z_and_tap (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

private theorem build_taps {n m : ℕ} (s : ℕ)
    (A : Fin s → Fin n → Bool) (B : Fin s → Fin m → Bool)
    (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (tap : Fin s → ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ gs'.countP nlGate = gs.countP nlGate + s ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 =
        (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (x : Fin n) (y : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach x y) gs').getD k false = (wiresOf (oneEach x y) gs).getD k false) ∧
      ∀ p : Fin s, tap p < n + m + gs'.length ∧
        (depthsOf (n + m) gs').getD (tap p) 0 ≤ 1 ∧
        Represents (fun x y => A p x && B p y) ⟨gs', tap p⟩ := by
  induction s generalizing gs with
  | zero =>
    exact ⟨gs, Fin.elim0, hv, le_rfl, by simp, fun _ _ => rfl, fun _ _ _ _ => rfl,
      fun p => Fin.elim0 p⟩
  | succ s ih =>
    obtain ⟨gsA, wa, hvA, hlA, hwa, hcA, hdA, hwA, ha0, ha⟩ :=
      build_row_fn (fun x => b2z (A 0 x)) gs hv
    obtain ⟨gsB, wb, hvB, hlB, hwb, hcB, hdB, hwB, hb0, hb⟩ :=
      build_col_fn (fun y => b2z (B 0 y)) gsA hvA
    have hwa' : wa < n + m + gsB.length := by omega
    obtain ⟨hvP, hlP, hcP, hdP, hwP, hpD, hpV⟩ := pushAnd_spec hvB hwa' hwb
    let gsP := pushAnd gsB wa wb
    let w0 := n + m + gsB.length
    have hw0 : w0 < n + m + gsP.length := by
      change gsP.length = gsB.length + 1 at hlP
      dsimp [w0]
      omega
    obtain ⟨gs', taps, hv', hl', hc', hd', hw', htaps⟩ :=
      ih (fun p => A p.succ) (fun p => B p.succ) gsP hvP
    change gsP.length = gsB.length + 1 at hlP
    change gsP.countP nlGate = gsB.countP nlGate + 1 at hcP
    refine ⟨gs', Fin.cases w0 taps, hv', by omega, by omega, ?_, ?_, ?_⟩
    · intro k hk
      rw [hd' k (by omega), hdP k (by omega), hdB k (by omega), hdA k hk]
    · intro x y k hk
      rw [hw' x y k (by omega), hwP x y k (by omega), hwB x y k (by omega), hwA x y k hk]
    · intro p
      refine Fin.cases ?_ (fun j => ?_) p
      · change w0 < n + m + gs'.length ∧ (depthsOf (n + m) gs').getD w0 0 ≤ 1 ∧
          Represents (fun x y => A 0 x && B 0 y) ⟨gs', w0⟩
        refine ⟨by omega, ?_, ?_⟩
        · rw [hd' w0 hw0, hpD, hdB wa hwa, ha0, hb0]
          simp
        · intro x y
          apply b2z_inj
          change b2z ((wiresOf (oneEach x y) gs').getD w0 false) = b2z (A 0 x && B 0 y)
          rw [hw' x y w0 hw0, hpV x y, hwB x y wa hwa, ha x y, hb x y, b2z_and_tap]
      · simpa only [Fin.cases_succ] using htaps j

private theorem fits_taps {n m : ℕ} (s : ℕ)
    (A : Fin s → Fin n → Bool) (B : Fin s → Fin m → Bool) :
    ∃ (C : Circuit) (tap : Fin s → ℕ), ReadsBack (n + m) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nlGate ≤ s ∧
      ∀ p : Fin s, (depthsOf (n + m) C.gates).getD (tap p) 0 ≤ 1 ∧
        Represents (fun x y => A p x && B p y) ⟨C.gates, tap p⟩ := by
  obtain ⟨gs, tap, hv, _, hc, _, _, htaps⟩ := build_taps s A B [] (valid_nil n m)
  exact ⟨⟨gs, 0⟩, tap, hv.2, hv.1, by simpa using hc.le,
    fun p => (htaps p).2⟩
section RankUpdate

open Module

variable {K : Type*} [Field K] [Algebra (ZMod 2) K] {k s : ℕ}

private noncomputable def updateMap (bit : K →ₗ[ZMod 2] ZMod 2) (z : K)
    (a d : Fin s → K) (S : Finset (Fin s)) : K →ₗ[ZMod 2] K :=
  LinearMap.mulLeft (ZMod 2) z -
    ∑ i ∈ S, (bit.comp (LinearMap.mulLeft (ZMod 2) (d i))).smulRight (a i)

private theorem updateMap_apply (bit : K →ₗ[ZMod 2] ZMod 2) (z : K)
    (a d : Fin s → K) (S : Finset (Fin s)) (y : K) :
    updateMap bit z a d S y = z * y - ∑ i ∈ S, bit (d i * y) • a i := by
  simp only [updateMap, LinearMap.sub_apply, LinearMap.mulLeft_apply,
    LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply]

private noncomputable def updateMatrix (b : Basis (Fin k) (ZMod 2) K)
    (bit : K →ₗ[ZMod 2] ZMod 2) (z : K) (a d : Fin s → K) (S : Finset (Fin s)) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 2) :=
  fun i j =>
    bit (z * Fin.cases 0 b i * Fin.cases 0 b j) -
      ∑ l ∈ S, bit (a l * Fin.cases 0 b i) * bit (d l * Fin.cases 0 b j)

private theorem rank_updateMatrix (b : Basis (Fin k) (ZMod 2) K)
    (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0) (z : K)
    (a d : Fin s → K) (S : Finset (Fin s)) :
    (updateMatrix b bit z a d S).rank = finrank (ZMod 2) (LinearMap.range (updateMap bit z a d S)) := by
  have he : pairAnchor (pairMatrix b bit (updateMap bit z a d S)) = updateMatrix b bit z a d S := by
    ext i j
    rw [pairAnchor_pairMatrix_apply]
    let x : K := Fin.cases 0 b i
    let y : K := Fin.cases 0 b j
    change bit (x * updateMap bit z a d S y) =
      bit (z * x * y) - ∑ l ∈ S, bit (a l * x) * bit (d l * y)
    simp only [updateMap_apply, mul_sub, map_sub, Finset.mul_sum, map_sum,
      Algebra.mul_smul_comm, map_smul, smul_eq_mul]
    rw [show x * (z * y) = z * x * y by ring]
    congr 1
    exact Finset.sum_congr rfl (fun l _ => by rw [mul_comm x (a l), mul_comm (bit (d l * y))])
  rw [← he, rank_pairAnchor_pairMatrix b bit hbit]

private theorem rank_update_eq (b : Basis (Fin k) (ZMod 2) K)
    (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0) (z : K) (hz : z ≠ 0)
    (a d : Fin s → K) (S : Finset (Fin s))
    (htri : ∀ i j, i ∈ S → j ∈ S → j ≤ i → bit (z⁻¹ * a i * d j) = 0) :
    (updateMatrix b bit z a d S).rank = k := by
  let _ : FiniteDimensional (ZMod 2) K := b.finiteDimensional_of_finite
  have hker : LinearMap.ker (updateMap bit z a d S) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hk : z * x = ∑ j ∈ S, bit (d j * x) • a j := by
      have hh := LinearMap.mem_ker.mp hx
      rw [updateMap_apply] at hh
      exact sub_eq_zero.mp hh
    have hxn : x = ∑ j ∈ S, bit (d j * x) • (z⁻¹ * a j) := by
      have h := congrArg (fun v : K => z⁻¹ * v) hk
      change z⁻¹ * (z * x) = z⁻¹ * (∑ j ∈ S, bit (d j * x) • a j) at h
      rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul, Finset.mul_sum] at h
      simpa only [Algebra.mul_smul_comm] using h
    -- In the equation for the coefficient at i, only coefficients at j < i can survive.
    have hc : ∀ n : ℕ, ∀ i : Fin s, i.val = n → i ∈ S → bit (d i * x) = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro i hi his
        calc
          bit (d i * x) = bit (d i * ∑ j ∈ S, bit (d j * x) • (z⁻¹ * a j)) :=
            congrArg (fun v : K => bit (d i * v)) hxn
          _ = ∑ j ∈ S, bit (d j * x) * bit (z⁻¹ * a j * d i) := by
            simp only [Finset.mul_sum, map_sum, Algebra.mul_smul_comm, map_smul, smul_eq_mul]
            exact Finset.sum_congr rfl (fun j _ => by rw [mul_comm (d i)])
          _ = 0 := Finset.sum_eq_zero fun j hjs => by
            by_cases hij : i ≤ j
            · rw [htri j i hjs his hij, mul_zero]
            · have hji : j.val < n := hi ▸ (show j.val < i.val from lt_of_not_ge hij)
              rw [ih j.val hji j rfl hjs, zero_mul]
    have hz0 : z * x = 0 := hk.trans (Finset.sum_eq_zero fun i hi => by
      rw [hc i.val i rfl hi, zero_smul])
    exact (mul_eq_zero.mp hz0).resolve_left hz
  rw [rank_updateMatrix b bit hbit]
  have hdim := LinearMap.finrank_range_add_finrank_ker (updateMap bit z a d S)
  rwa [hker, finrank_bot, add_zero, Module.finrank_eq_card_basis b, Fintype.card_fin] at hdim

private theorem rank_update_lt_of_ker (b : Basis (Fin k) (ZMod 2) K)
    (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0) (z : K)
    (a d : Fin s → K) (S : Finset (Fin s)) (y : K)
    (hy : y ≠ 0) (hker : updateMap bit z a d S y = 0) :
    (updateMatrix b bit z a d S).rank < k := by
  let _ : FiniteDimensional (ZMod 2) K := b.finiteDimensional_of_finite
  have hpos : 0 < finrank (ZMod 2) (LinearMap.ker (updateMap bit z a d S)) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨y, LinearMap.mem_ker.mpr hker⟩, fun h => hy (congrArg Subtype.val h)⟩
  have hdim := LinearMap.finrank_range_add_finrank_ker (updateMap bit z a d S)
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin] at hdim
  rw [rank_updateMatrix b bit hbit]
  omega

private theorem updateBit_one {v : ZMod 2} (hv : v ≠ 0) : v = 1 := by
  simpa [hv, b2z] using (zmod_of_bool_pred v).symm

private theorem rank_update_select (b : Basis (Fin k) (ZMod 2) K)
    (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0) (z : K) (hz : z ≠ 0)
    (d : Fin s → K) (hpair : ∃ i j, bit (z⁻¹ * d i * d j) ≠ 0) :
    ∃ S : Finset (Fin s), S.card ≤ 2 ∧ (updateMatrix b bit z d d S).rank < k := by
  classical
  -- A nonzero diagonal entry fixes one direction; otherwise a nonzero cross entry
  -- fixes the sum of its two directions.
  by_cases hdiag : ∃ i, bit (z⁻¹ * d i * d i) ≠ 0
  · obtain ⟨i, hi⟩ := hdiag
    let y := z⁻¹ * d i
    have hyi : bit (d i * y) = 1 := by
      rw [show d i * y = z⁻¹ * d i * d i by dsimp [y]; ring]
      exact updateBit_one hi
    have hy : y ≠ 0 := by
      intro h
      simp [h] at hyi
    refine ⟨{i}, by simp, rank_update_lt_of_ker b bit hbit z d d {i} y hy ?_⟩
    rw [updateMap_apply, Finset.sum_singleton, hyi, one_smul]
    simp [y, ← mul_assoc, mul_inv_cancel₀ hz]
  · obtain ⟨i, j, hij0⟩ := hpair
    have hd : ∀ i, bit (z⁻¹ * d i * d i) = 0 := fun i => by
      by_contra hi
      exact hdiag ⟨i, hi⟩
    have hij : i ≠ j := by
      rintro rfl
      exact hij0 (hd i)
    have hcross := updateBit_one hij0
    let y := z⁻¹ * (d i + d j)
    have hyi : bit (d i * y) = 1 := by
      change bit (d i * (z⁻¹ * (d i + d j))) = 1
      rw [mul_add, mul_add, map_add,
        show d i * (z⁻¹ * d i) = z⁻¹ * d i * d i by ring,
        show d i * (z⁻¹ * d j) = z⁻¹ * d i * d j by ring,
        hd i, hcross, zero_add]
    have hyj : bit (d j * y) = 1 := by
      change bit (d j * (z⁻¹ * (d i + d j))) = 1
      rw [mul_add, mul_add, map_add,
        show d j * (z⁻¹ * d i) = z⁻¹ * d i * d j by ring,
        show d j * (z⁻¹ * d j) = z⁻¹ * d j * d j by ring,
        hd j, hcross, add_zero]
    have hy : y ≠ 0 := by
      intro h
      simp [h] at hyi
    have hin : i ∉ ({j} : Finset (Fin s)) := by simpa using hij
    refine ⟨{i, j}, by simp [Finset.card_insert_of_notMem hin],
      rank_update_lt_of_ker b bit hbit z d d {i, j} y hy ?_⟩
    rw [updateMap_apply, Finset.sum_insert hin, Finset.sum_singleton, hyi, hyj, one_smul, one_smul]
    simp [y, ← mul_assoc, mul_inv_cancel₀ hz]

end RankUpdate
section Assembly

open Module
open scoped Pointwise
variable {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
variable {k : ℕ} (b : Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2)

private theorem cheap_update {s : ℕ} (A B : Fin s → Fin (k+1) → Bool) (a d : Fin s → K)
    (ha : ∀ i x, b2z (A i x) + b2z (A i 0) = bit (a i * Fin.cases 0 b x))
    (hd : ∀ i y, b2z (B i y) + b2z (B i 0) = bit (d i * Fin.cases 0 b y))
    (S : Finset (Fin s)) (z : K) (t : ℕ) :
    Cheap (residualTable b bit (fun i x y => A i x && B i y) S z) t ↔
      (updateMatrix b bit z a d S).rank ≤ 2*t := by
  rw [cheap_iff _ 0 0]
  have he : anchor 0 0 (fun i j =>
      b2z (residualTable b bit (fun l x y => A l x && B l y) S z i j)) =
      updateMatrix b bit z a d S := by
    ext x y
    rw [residual_anchor_formula]
    simp only [ha, hd, updateMatrix, sub_eq_add_neg]
    congr 1
    exact eq_neg_iff_add_eq_zero.mpr (zmod2_add_self _)
  rw [he]

private def Serve {s : ℕ} (T : Fin s → Fin (k+1) → Fin (k+1) → Bool) (h : ℕ) (z : K) : Prop :=
  z ≠ 0 ∧ ∃ S : Finset (Fin s), S.card ≤ h ∧ Cheap (residualTable b bit T S z) (k/2)

private theorem upper_bound (hb : bit ≠ 0) (hk : k % 2 = 1)
    (s : ℕ) (A B : Fin s → Fin (k+1) → Bool) (Z : Finset K)
    (hZ : ∀ z ∈ Z, Serve b bit (fun i x y => A i x && B i y) s z) :
    Z.card ≤ 2^k - 2^(k-triangle s) := by
  classical
  choose a ha using fun i => represent_factor b bit hb (A i)
  choose d hd using fun i => represent_factor b bit hb (B i)
  let f : Triangle s → K := fun ij => a ij.1.1 * d ij.1.2
  let W := Submodule.span (ZMod 2) (Set.range f)
  have hsub : Z ⊆ servedSet bit W := by
    intro z hz
    obtain ⟨h₀, S, _, hfit⟩ := hZ z hz
    have hr := (cheap_update b bit A B a d ha hd S z _).mp hfit
    by_contra h
    have hn := not_exists.mp (mt (detect_span bit f z).mpr h)
    have htri : ∀ i j, i ∈ S → j ∈ S → j ≤ i → bit (z⁻¹ * a i * d j) = 0 := by
      intro i j _ _ hij
      have hh := not_not.mp (hn ⟨(i,j), hij⟩)
      simpa [f, mul_assoc] using hh
    rw [rank_update_eq b bit hb z h₀ a d S htri] at hr
    omega
  have hdW : finrank (ZMod 2) W ≤ triangle s :=
    (finrank_range_le_card f).trans (card_triangle s)
  calc
    Z.card ≤ (servedSet bit W).card := Finset.card_le_card hsub
    _ = 2^k - 2^(k-finrank (ZMod 2) W) := card_servedSet b bit hb W
    _ ≤ 2^k - 2^(k-triangle s) :=
      Nat.sub_le_sub_left (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left hdW k)) _

private noncomputable def directionTable {s : ℕ} (d : Fin s → K) (i : Fin s) (x : Fin (k+1)) : Bool :=
  decide (bit (d i * Fin.cases 0 b x) ≠ 0)

private theorem lower_bound (hb : bit ≠ 0) (hk : k % 2 = 1)
    {s : ℕ} (d : Fin s → K) (a : ℕ)
    (hr : finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun ij : Fin s × Fin s => d ij.1 * d ij.2)) = min k a) :
    ∃ Z : Finset K, Z.card = 2^k - 2^(k-a) ∧ ∀ z ∈ Z,
      Serve b bit (fun i x y => directionTable b bit d i x && directionTable b bit d i y) 2 z := by
  classical
  let f := fun ij : Fin s × Fin s => d ij.1 * d ij.2
  let W := Submodule.span (ZMod 2) (Set.range f)
  refine ⟨servedSet bit W, ?_, ?_⟩
  · rw [card_servedSet b bit hb W, show finrank (ZMod 2) W = min k a from hr]
    congr 2
    omega
  intro z hz
  have hp : ∃ i j, bit (z⁻¹ * d i * d j) ≠ 0 := by
    obtain ⟨⟨i,j⟩, hi⟩ := (detect_span bit f z).mp hz
    exact ⟨i, j, by simpa [f, mul_assoc] using hi⟩
  have h₀ : z ≠ 0 := by
    intro h
    simp [h] at hp
  obtain ⟨S, hcard, hS⟩ := rank_update_select b bit hb z h₀ d hp
  let A := directionTable b bit d
  have hh (i : Fin s) (x : Fin (k+1)) :
      b2z (A i x) + b2z (A i 0) = bit (d i * Fin.cases 0 b x) := by
    simp only [A, directionTable, zmod_of_bool_pred, Fin.cases_zero, mul_zero, map_zero, add_zero]
  exact ⟨h₀, S, hcard, (cheap_update b bit A A d d hh hh S z _).mpr (by omega)⟩

end Assembly

end PEqualNP.Outside.L_meta_29714_aux

open PEqualNP.Outside.L_meta_29714_aux
open scoped Pointwise

theorem PEqualNP.Outside.L_meta_29714 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩

let F := ZMod 2
∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
    (k : ℕ) (basis : Module.Basis (Fin k) F K) (bit : K →ₗ[F] F), bit ≠ 0 →
  let n := k+1
  let point : Fin n → K := Fin.cases 0 basis
  let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
  let residual := fun {g : ℕ} (T : Fin g → Fin n → Fin n → Bool) (S : Finset (Fin g))
      (z : K) (x y : Fin n) => xor (mult z x y) (((S.filter (fun i => T i x y)).card % 2) == 1)


  k % 2 = 1 →
    let cap := fun s : ℕ => 2^k - 2^(k - (s*(s+1)/2))
    let serve := fun {s : ℕ} (T : Fin s → Fin n → Fin n → Bool) (h : ℕ) (z : K) =>
      z ≠ 0 ∧ ∃ S : Finset (Fin s), S.card ≤ h ∧ fits n n 1 (fun _ => residual T S z) (k/2)
    (∀ (s : ℕ) (A B : Fin s → Fin n → Bool) (Z : Finset K),
      (∀ z ∈ Z, serve (fun i x y => A i x && B i y) s z) → Z.card ≤ cap s) ∧
    ∀ (r : ℕ) (seed : Fin r → K), LinearIndependent F seed →
      let baseRank := Module.finrank F (Submodule.span F
        (Set.range (fun ij : Fin r × Fin r => seed ij.1 * seed ij.2)))
      ∃ d : ℕ → K, (∀ i : Fin r, d i.val = seed i) ∧ ∀ j : ℕ,
      let s := r+j
      let T := fun (i : Fin s) (x y : Fin n) =>
        decide (bit (d i.val * point x) ≠ 0) && decide (bit (d i.val * point y) ≠ 0)
      fits n n s T s ∧ ∃ Z : Finset K, Z.card = 2^k - 2^(k-(baseRank+r*j+j*(j+1)/2)) ∧ ∀ z ∈ Z, serve T 2 z
) := by
  dsimp only
  intro K _ _ _ k b bit hb hk
  have hd : Module.finrank (ZMod 2) K = k := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  refine ⟨upper_bound b bit hb hk, ?_⟩
  intro r seed hseed
  have hg (U : Submodule (ZMod 2) K) : ∃ x : K,
      let V := U ⊔ Submodule.span (ZMod 2) {x}
      Module.finrank (ZMod 2) (V*V) = min (Module.finrank (ZMod 2) K)
        (Module.finrank (ZMod 2) (U*U) + Module.finrank (ZMod 2) U + 1) := by
    obtain ⟨x, hx⟩ := growth_exists U (U*U) (by rw [hd]; exact hk) (fun a => by
      simpa only [pow_two] using Submodule.mul_mem_mul a.property a.property)
    exact ⟨x, (congrArg (fun W : Submodule (ZMod 2) K => Module.finrank (ZMod 2) W)
      (square_append U x)).trans hx⟩
  obtain ⟨d, hseed', hrank⟩ := chain_exists hg seed hseed
  refine ⟨d, hseed', ?_⟩
  intro j
  let s := r+j
  let ds : Fin s → K := fun i => d i.val
  let A := directionTable b bit ds
  refine ⟨fits_taps s A A, ?_⟩
  have hh := hrank j
  rw [hd] at hh
  exact lower_bound b bit hb hk ds _ hh
