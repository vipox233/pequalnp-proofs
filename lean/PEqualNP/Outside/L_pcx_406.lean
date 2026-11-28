import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_406

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

def unit (v : V) : V → ZMod 2 := fun u => if u = v then (1 : ZMod 2) else 0

def wt (x : V → ZMod 2) : ℕ := (univ.filter (fun v : V => x v ≠ 0)).card

noncomputable def len (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (s : Fin r → ZMod 2) : ℕ :=
  sInf {k : ℕ | ∃ x : V → ZMod 2, H x = s ∧ wt x = k}

lemma z2 (a : ZMod 2) (h : a ≠ 0) : a = 1 := by
  revert a h; decide

lemma add_self' {W : Type} (x : W → ZMod 2) : x + x = 0 := by
  funext v
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x v = a
  revert a; decide

omit [DecidableEq V] in
lemma len_le (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) {x : V → ZMod 2} {s : Fin r → ZMod 2}
    (hx : H x = s) : len H s ≤ wt x :=
  Nat.sInf_le ⟨x, hx, rfl⟩

omit [DecidableEq V] in
lemma len_spec (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (hH : Function.Surjective H)
    (s : Fin r → ZMod 2) : ∃ x, H x = s ∧ wt x = len H s := by
  obtain ⟨x, hx⟩ := hH s
  exact Nat.sInf_mem (s := {k : ℕ | ∃ x : V → ZMod 2, H x = s ∧ wt x = k}) ⟨_, x, hx, rfl⟩

lemma wt_add_unit (x : V → ZMod 2) (v : V) : wt (x + unit v) ≤ wt x + 1 := by
  unfold wt
  calc (univ.filter (fun u : V => (x + unit v) u ≠ 0)).card
      ≤ (insert v (univ.filter (fun u : V => x u ≠ 0))).card := by
        apply card_le_card
        intro u hu
        rw [mem_filter] at hu
        rw [mem_insert, mem_filter]
        by_cases h : u = v
        · exact Or.inl h
        · right; refine ⟨mem_univ _, ?_⟩
          have := hu.2
          simpa [unit, h] using this
    _ ≤ _ := card_insert_le _ _

lemma len_add_unit (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (hH : Function.Surjective H)
    (s : Fin r → ZMod 2) (v : V) : len H (s + H (unit v)) ≤ len H s + 1 := by
  obtain ⟨x, hx, hw⟩ := len_spec H hH s
  calc len H (s + H (unit v)) ≤ wt (x + unit v) := len_le H (by rw [map_add, hx])
    _ ≤ wt x + 1 := wt_add_unit x v
    _ = len H s + 1 := by rw [hw]

lemma eq_sum_unit (w : V → ZMod 2) : w = ∑ v ∈ univ.filter (fun v : V => w v ≠ 0), unit v := by
  funext u
  simp only [Finset.sum_apply, unit, Finset.sum_ite_eq, mem_filter, mem_univ, true_and]
  by_cases h : w u = 0
  · simp [h]
  · simp [z2 _ h]

omit [Fintype V] in
lemma chain (R : ℝ) (hR : 0 ≤ R) (μ : (V → ZMod 2) → ℝ) (_hμ0 : ∀ x, 0 ≤ μ x)
    (hμ : ∀ x v, μ x ≤ R * μ (x + unit v)) (S : Finset V) :
    ∀ z, μ z ≤ R ^ S.card * μ (z + ∑ v ∈ S, unit v) := by
  induction S using Finset.induction_on with
  | empty => intro z; simp
  | insert a S ha ih =>
    intro z
    rw [Finset.sum_insert ha, card_insert_of_notMem ha]
    calc μ z ≤ R ^ S.card * μ (z + ∑ v ∈ S, unit v) := ih z
      _ ≤ R ^ S.card * (R * μ (z + ∑ v ∈ S, unit v + unit a)) :=
          mul_le_mul_of_nonneg_left (hμ _ _) (pow_nonneg hR _)
      _ = R ^ (S.card + 1) * μ (z + (unit a + ∑ v ∈ S, unit v)) := by
          rw [pow_succ, mul_assoc, add_comm (unit a), ← add_assoc]

lemma chain' (R : ℝ) (hR : 0 ≤ R) (μ : (V → ZMod 2) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ : ∀ x v, μ x ≤ R * μ (x + unit v)) (w z : V → ZMod 2) :
    μ z ≤ R ^ wt w * μ (z + w) := by
  have := chain R hR μ hμ0 hμ (univ.filter (fun v : V => w v ≠ 0)) z
  rwa [← eq_sum_unit w] at this

lemma translate {M : Type} [AddCommMonoid M] (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (y s xs : _) (hxs : H xs = s) (f : (V → ZMod 2) → M) :
    ∑ x ∈ univ.filter (fun x => H x = y), f (x + xs) = ∑ x ∈ univ.filter (fun x => H x + y = s), f x := by
  apply Finset.sum_nbij' (fun x => x + xs) (fun x => x + xs)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [map_add, hx, hxs, add_right_comm, add_self', zero_add]
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    have : H x = s + y := by rw [← hx, add_assoc, add_self', add_zero]
    rw [map_add, this, hxs, add_right_comm, add_self', zero_add]
  · intro x _; simp only [add_assoc, add_self', add_zero]
  · intro x _; simp only [add_assoc, add_self', add_zero]
  · intro x _; rfl

lemma part3 (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (hH : Function.Surjective H)
    (R : ℕ) (y : Fin r → ZMod 2) (μ : (V → ZMod 2) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ : ∀ x v, μ x ≤ (R : ℝ) * μ (x + unit v)) :
    (∑ x, μ x) ≤ ((∑ s : Fin r → ZMod 2, R ^ (len H s) : ℕ) : ℝ) *
      ∑ x ∈ univ.filter (fun x => H x = y), μ x := by
  rw [← Finset.sum_fiberwise univ (fun x => H x + y) μ]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s _
  obtain ⟨xs, hxs, hw⟩ := len_spec H hH s
  rw [← translate H y s xs hxs μ, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have := chain' (R : ℝ) (Nat.cast_nonneg R) μ hμ0 hμ xs (x + xs)
  rwa [add_assoc, add_self', add_zero, hw] at this

lemma part4 (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (hH : Function.Surjective H)
    (R : ℕ) (hR : 1 ≤ R) (y : Fin r → ZMod 2) :
    let μ : (V → ZMod 2) → ℝ := fun x => (R : ℝ) ^ (len H (H x + y))
    ((∀ x, 0 ≤ μ x) ∧ 0 < ∑ x, μ x ∧ ∀ x v, μ x ≤ (R : ℝ) * μ (x + unit v)) ∧
    (∑ x, μ x) = ((∑ s : Fin r → ZMod 2, R ^ (len H s) : ℕ) : ℝ) *
      ∑ x ∈ univ.filter (fun x => H x = y), μ x := by
  intro μ
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have len0 : len H 0 = 0 := Nat.le_zero.mp (len_le H (x := 0) (map_zero H) |>.trans (by simp [wt]))
  refine ⟨⟨fun x => pow_nonneg (by linarith) _, ?_, ?_⟩, ?_⟩
  · exact Finset.sum_pos (fun x _ => pow_pos (by linarith) _) univ_nonempty
  · intro x v
    simp only [μ]
    have h1 : H x + y = (H (x + unit v) + y) + H (unit v) := by
      rw [map_add, add_right_comm, add_assoc (H x), add_self', add_zero]
    rw [h1]
    calc (R : ℝ) ^ len H (H (x + unit v) + y + H (unit v))
        ≤ (R : ℝ) ^ (len H (H (x + unit v) + y) + 1) :=
          pow_le_pow_right₀ hR' (len_add_unit H hH _ v)
      _ = _ := by rw [pow_succ, mul_comm]
  · have hf : ∑ x ∈ univ.filter (fun x => H x = y), μ x =
        ((univ.filter (fun x => H x = y)).card : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [mem_filter] at hx
      simp only [μ, hx.2, add_self', len0, pow_zero, Nat.cast_one]
    rw [hf, ← Finset.sum_fiberwise univ (fun x => H x + y) μ]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    obtain ⟨xs, hxs, _⟩ := len_spec H hH s
    have e1 : ∑ x ∈ univ.filter (fun x => H x + y = s), μ x =
        ∑ x ∈ univ.filter (fun x => H x + y = s), (R : ℝ) ^ len H s := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [mem_filter] at hx
      simp only [μ, hx.2]
    rw [e1, ← translate H y s xs hxs (fun _ => (R : ℝ) ^ len H s)]
    simp [mul_comm]

lemma sum_pow_wt (κ : Type) [Fintype κ] [DecidableEq κ] (R : ℕ) :
    ∑ T : κ → ZMod 2, R ^ (univ.filter (fun k => T k ≠ 0)).card = (R + 1) ^ Fintype.card κ := by
  have h1 : ∀ T : κ → ZMod 2, R ^ (univ.filter (fun k => T k ≠ 0)).card =
      ∏ k, (if T k ≠ 0 then R else 1) := by
    intro T
    rw [Finset.prod_ite, prod_const, prod_const_one, mul_one]
  simp_rw [h1]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ : κ => (univ : Finset (ZMod 2))) (fun _ t => if t ≠ 0 then R else 1)]
  have h2 : ∑ t : ZMod 2, (if t ≠ 0 then R else 1) = R + 1 := by
    show ∑ t : Fin 2, (if t ≠ 0 then R else 1) = R + 1
    rw [Fin.sum_univ_two]; simp [add_comm]
  simp only [h2, prod_const, card_univ]

lemma x_sum_unit (x : V → ZMod 2) : x = ∑ v, x v • unit v := by
  funext u
  simp [Finset.sum_apply, unit]

lemma span_top (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (hH : Function.Surjective H) :
    Submodule.span (ZMod 2) (Set.range (fun v => H (unit v))) = ⊤ := by
  rw [eq_top_iff]
  intro s _
  obtain ⟨x, rfl⟩ := hH s
  rw [x_sum_unit x, map_sum]
  exact Submodule.sum_mem _ fun v _ => by
    rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)

lemma basis_setup (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (hH : Function.Surjective H) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (a : κ → V) (b : Module.Basis κ (ZMod 2) (Fin r → ZMod 2)),
      Function.Injective a ∧ (∀ k, b k = H (unit (a k))) ∧ Fintype.card κ = r := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' (ZMod 2) (fun v => H (unit v))
  have : Finite κ := Finite.of_injective a ha
  let _ : Fintype κ := Fintype.ofFinite κ
  have htop : ⊤ ≤ Submodule.span (ZMod 2) (Set.range ((fun v => H (unit v)) ∘ a)) := by
    rw [hsp, span_top H hH]
  let b := Module.Basis.mk hli htop
  refine ⟨κ, inferInstance, inferInstance, a, b, ha, fun k => by simp [b], ?_⟩
  have := Module.finrank_eq_card_basis b
  simpa using this.symm

lemma len_basis_le (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) {κ : Type} [Fintype κ] [DecidableEq κ]
    (a : κ → V) (b : Module.Basis κ (ZMod 2) (Fin r → ZMod 2)) (_ha : Function.Injective a)
    (hb : ∀ k, b k = H (unit (a k))) (T : κ → ZMod 2) :
    len H (b.equivFun.symm T) ≤ (univ.filter (fun k => T k ≠ 0)).card := by
  let x : V → ZMod 2 := ∑ k, T k • unit (a k)
  have hx : H x = b.equivFun.symm T := by
    simp [x, map_sum, map_smul, Module.Basis.equivFun_symm_apply, hb]
  refine (len_le H hx).trans ?_
  unfold wt
  calc (univ.filter (fun v => x v ≠ 0)).card ≤ ((univ.filter (fun k => T k ≠ 0)).image a).card := by
        apply card_le_card
        intro v hv
        rw [mem_filter] at hv
        have hv2 := hv.2
        simp only [x, Finset.sum_apply, Pi.smul_apply, unit, smul_eq_mul, mul_ite, mul_one, mul_zero] at hv2
        obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv2
        rw [mem_image]
        refine ⟨k, ?_, ?_⟩
        · rw [mem_filter]; refine ⟨mem_univ _, ?_⟩
          intro h0; apply hk; simp [h0]
        · by_contra hne; apply hk; simp [Ne.symm hne]
    _ ≤ _ := card_image_le

lemma wt_unit (v : V) : wt (unit v) = 1 := by
  unfold wt
  rw [card_eq_one]
  refine ⟨v, ?_⟩
  ext u
  simp [unit]

lemma parts12 (H : (V → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) (hH : Function.Surjective H)
    (R : ℕ) (hR : 1 ≤ R) :
    (∑ s : Fin r → ZMod 2, R ^ (len H s)) ≤ (R + 1) ^ r ∧
    (1 < R → ((∑ s : Fin r → ZMod 2, R ^ (len H s)) = (R + 1) ^ r ↔
      ((univ.image (fun v : V => H (unit v))).erase 0).card = r)) := by
  classical
  obtain ⟨κ, _, _, a, b, ha, hb, hcard⟩ := basis_setup H hH
  have hZ : (∑ s : Fin r → ZMod 2, R ^ (len H s)) = ∑ T : κ → ZMod 2, R ^ len H (b.equivFun.symm T) :=
    (Equiv.sum_comp b.equivFun.symm.toEquiv (fun s => R ^ len H s)).symm
  have hW : (R + 1) ^ r = ∑ T : κ → ZMod 2, R ^ (univ.filter (fun k => T k ≠ 0)).card := by
    rw [sum_pow_wt, hcard]
  have hle : ∀ T : κ → ZMod 2, R ^ len H (b.equivFun.symm T) ≤ R ^ (univ.filter (fun k => T k ≠ 0)).card :=
    fun T => Nat.pow_le_pow_right hR (len_basis_le H a b ha hb T)
  refine ⟨by rw [hZ, hW]; exact Finset.sum_le_sum fun T _ => hle T, fun hR1 => ?_⟩
  set cols := (univ.image (fun v : V => H (unit v))).erase 0 with hcols
  set B := univ.image (fun k => b k) with hB
  have hBc : B ⊆ cols := by
    intro c hc
    rw [hB, mem_image] at hc
    obtain ⟨k, _, rfl⟩ := hc
    rw [hcols, mem_erase, mem_image]
    exact ⟨b.ne_zero k, a k, mem_univ _, (hb k).symm⟩
  have hBcard : B.card = r := by
    rw [hB, card_image_of_injective _ b.injective, card_univ, hcard]
  constructor
  · intro hZeq
    by_contra hne
    have hnot : ¬ cols ⊆ B := by
      intro hsub
      have h1 := card_le_card hsub
      have h2 := card_le_card hBc
      exact hne (by omega)
    obtain ⟨col, hcol, hcolB⟩ := Finset.not_subset.mp hnot
    rw [hcols, mem_erase, mem_image] at hcol
    obtain ⟨hc0, v0, _, rfl⟩ := hcol
    set T0 := b.equivFun (H (unit v0)) with hT0
    have hφ : b.equivFun.symm T0 = H (unit v0) := by simp [hT0]
    have hlen : len H (b.equivFun.symm T0) ≤ 1 := by
      rw [hφ]; exact (len_le H rfl).trans (wt_unit v0).le
    have hwt : 2 ≤ (univ.filter (fun k => T0 k ≠ 0)).card := by
      by_contra hlt
      push Not at hlt
      interval_cases hc : (univ.filter (fun k => T0 k ≠ 0)).card
      · rw [card_eq_zero, filter_eq_empty_iff] at hc
        apply hc0
        have : T0 = 0 := funext fun k => by simpa using hc (mem_univ k)
        rw [← hφ, this]; simp
      · obtain ⟨k, hk⟩ := card_eq_one.mp hc
        have hT : T0 = fun k' => if k' = k then 1 else 0 := by
          funext k'
          by_cases h : k' = k
          · subst h
            have : k' ∈ univ.filter (fun k => T0 k ≠ 0) := by rw [hk]; simp
            rw [mem_filter] at this
            simpa using z2 _ this.2
          · have : k' ∉ univ.filter (fun k => T0 k ≠ 0) := by rw [hk]; simpa using h
            simp only [mem_filter, mem_univ, true_and, not_not] at this
            simp [h, this]
        apply hcolB
        rw [hB, mem_image]
        refine ⟨k, mem_univ _, ?_⟩
        rw [← hφ, hT]
        simp [Module.Basis.equivFun_symm_apply, ite_smul]
    have hlt : (∑ s : Fin r → ZMod 2, R ^ (len H s)) < (R + 1) ^ r := by
      rw [hZ, hW]
      apply Finset.sum_lt_sum (fun T _ => hle T)
      exact ⟨T0, mem_univ _, Nat.pow_lt_pow_right hR1 (by omega)⟩
    omega
  · intro hc
    have hcB : cols = B := (Finset.eq_of_subset_of_card_le hBc (by rw [hc, hBcard])).symm
    rw [hZ, hW]
    refine Finset.sum_congr rfl fun T _ => ?_
    congr 1
    refine le_antisymm (len_basis_le H a b ha hb T) ?_
    obtain ⟨x, hx, hw⟩ := len_spec H (V := V) hH (b.equivFun.symm T)
    rw [← hw]
    have hcol : ∀ v, H (unit v) = 0 ∨ ∃ k, H (unit v) = b k := by
      intro v
      by_cases h0 : H (unit v) = 0
      · exact Or.inl h0
      · right
        have : H (unit v) ∈ cols := by
          rw [hcols, mem_erase, mem_image]; exact ⟨h0, v, mem_univ _, rfl⟩
        rw [hcB, hB, mem_image] at this
        obtain ⟨k, _, hk⟩ := this
        exact ⟨k, hk.symm⟩
    have hTk : ∀ k, T k = ∑ v, x v * b.repr (H (unit v)) k := by
      intro k
      have h1 : T = b.equivFun (H x) := by rw [hx, LinearEquiv.apply_symm_apply]
      have h2 : H x = ∑ v, x v • H (unit v) := by
        conv_lhs => rw [x_sum_unit x]
        rw [map_sum]; simp only [map_smul]
      rw [h1, Module.Basis.equivFun_apply, h2, map_sum]
      simp
    have hpick : ∀ k, T k ≠ 0 → ∃ v, x v ≠ 0 ∧ H (unit v) = b k := by
      intro k hk
      rw [hTk k] at hk
      obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
      refine ⟨v, fun h => hv (by simp [h]), ?_⟩
      rcases hcol v with h0 | ⟨k', hk'⟩
      · exfalso; apply hv; simp [h0]
      · rw [hk'] at hv ⊢
        by_cases hkk : k' = k
        · rw [hkk]
        · exfalso; apply hv
          simp [Module.Basis.repr_self, hkk]
    unfold wt
    by_cases hne : (univ.filter (fun k => T k ≠ 0)).Nonempty
    swap
    · rw [not_nonempty_iff_eq_empty.mp hne]; simp
    obtain ⟨k0, hk0⟩ := hne
    rw [mem_filter] at hk0
    obtain ⟨v0, _⟩ := hpick k0 hk0.2
    have : Nonempty V := ⟨v0⟩
    choose! g hg using hpick
    apply Finset.card_le_card_of_injOn g
    · intro k hk
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk ⊢
      exact (hg k hk).1
    · intro k hk k' hk' hkk
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk hk'
      have h1 := (hg k hk).2
      have h2 := (hg k' hk').2
      rw [hkk] at h1
      exact b.injective (h1.symm.trans h2)

end PEqualNP.Outside.L_pcx_406
theorem PEqualNP.Outside.L_pcx_406 : ∀ (V : Type) [Fintype V] [DecidableEq V] (r R : ℕ), 1 ≤ R →
  let K := ZMod 2
  let X := V → K
  let Y := Fin r → K
  ∀ (H : X →ₗ[K] Y), Function.Surjective H →
    let unit := fun v : V => fun u : V => if u = v then (1 : K) else 0
    let cols := (Finset.univ.image (fun v : V => H (unit v))).erase 0
    let length := fun s : Y => sInf {k : ℕ | ∃ x : X, H x = s ∧
      (Finset.univ.filter (fun v : V => x v ≠ 0)).card = k}
    let Z := ∑ s : Y, R^(length s)
    let smooth := fun μ : X → ℝ => (∀ x, 0 ≤ μ x) ∧ 0 < ∑ x, μ x ∧
      ∀ x v, μ x ≤ (R : ℝ) * μ (x + unit v)
    Z ≤ (R+1)^r ∧ (1 < R → (Z = (R+1)^r ↔ cols.card = r)) ∧
    ∀ y : Y,
      let fiber := Finset.univ.filter (fun x : X => H x = y)
      (∀ μ : X → ℝ, smooth μ → (∑ x, μ x) ≤ (Z : ℝ) * ∑ x ∈ fiber, μ x) ∧
      ∃ μ : X → ℝ, smooth μ ∧ (∑ x, μ x) = (Z : ℝ) * ∑ x ∈ fiber, μ x := by
  intro V _ _ r R hR K X Y H hH unit cols length Z smooth
  obtain ⟨h1, h2⟩ := L_pcx_406.parts12 H hH R hR
  refine ⟨h1, h2, fun y => ?_⟩
  intro fiber
  refine ⟨fun μ hμ => L_pcx_406.part3 H hH R y μ hμ.1 hμ.2.2, ?_⟩
  obtain ⟨hs, he⟩ := L_pcx_406.part4 H hH R hR y
  exact ⟨_, hs, he⟩
