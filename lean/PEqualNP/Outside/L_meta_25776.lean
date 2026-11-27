import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25776_aux

open scoped Classical

private lemma pad_inj {a c : Nat} (hac : a ≤ c) :
    Function.Injective
      (fun (x : Fin a → ZMod 2) (i : Fin c) =>
        if hi : i.val < a then x ⟨i.val, hi⟩ else 0) := by
  intro x y hxy
  funext j
  have h := congrFun hxy ⟨j.val, Nat.lt_of_lt_of_le j.isLt hac⟩
  simpa [j.isLt] using h

private def padLin {a c : Nat} (_hac : a ≤ c) :
    (Fin a → ZMod 2) →ₗ[ZMod 2] (Fin c → ZMod 2) where
  toFun x i := if hi : i.val < a then x ⟨i.val, hi⟩ else 0
  map_add' x y := by
    funext i
    by_cases hi : i.val < a <;> simp [hi]
  map_smul' r x := by
    funext i
    by_cases hi : i.val < a <;> simp [hi]

private lemma padLin_inj {a c : Nat} (hac : a ≤ c) : Function.Injective (padLin hac) :=
  pad_inj hac

private lemma attainment (m h b : Nat) (hh : 6 ≤ h) (_hb : 2 ≤ b) (hbh : b < h)
    (hm : m + h + b ≤ 2 ^ h * b) :
    let q := h + b
    let U := Fin h → ZMod 2
    let V := Fin m → ZMod 2
    let feasible := fun (label : U → V → Bool) =>
      ∃ (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((U × V) →ₗ[ZMod 2] ZMod 2))
        (answers : U → V → Fin q → ZMod 2) (leaf : (Fin q → ZMod 2) → Bool),
        (∀ (u : U) (x : V) (j : Fin q), answers u x j =
          ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u, x)) ∧
        ∀ (u : U) (x : V), label u x = leaf (answers u x)
    ∃ label : U → V → Bool, feasible label ∧
      (∀ witness, label witness 0 = false) ∧
      ∀ x : V, x ≠ 0 → ∀ live : Finset U, 2 ^ h ≤ live.card + 2 →
        ∃ address ∈ live, label address x = true := by
  intro q U V feasible
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 h
  have hh0 : h ≠ 0 := by omega
  have hF_rank : Module.finrank (ZMod 2) F = h := GaloisField.finrank 2 hh0
  have hU_rank : Module.finrank (ZMod 2) U = h := Module.finrank_fin_fun (ZMod 2)
  let eU : U ≃ₗ[ZMod 2] F := LinearEquiv.ofFinrankEq U F (hU_rank.trans hF_rank.symm)
  let iota : (Fin b → ZMod 2) →ₗ[ZMod 2] F := eU.toLinearMap.comp (padLin (Nat.le_of_lt hbh))
  have hiota_inj : Function.Injective iota :=
    eU.injective.comp (padLin_inj (Nat.le_of_lt hbh))
  let E := U → (Fin b → ZMod 2)
  let S0 : E →ₗ[ZMod 2] (Fin b → ZMod 2) :=
    { toFun := fun y => ∑ a : U, y a
      map_add' := fun y z => by
        change ∑ a : U, (y a + z a) = (∑ a : U, y a) + ∑ a : U, z a
        exact Finset.sum_add_distrib
      map_smul' := fun r y => by
        change ∑ a : U, r • y a = r • ∑ a : U, y a
        exact (Finset.smul_sum).symm }
  let S1 : E →ₗ[ZMod 2] F :=
    { toFun := fun y => ∑ a : U, eU a * iota (y a)
      map_add' := fun y z => by
        change ∑ a : U, eU a * iota (y a + z a) =
          (∑ a : U, eU a * iota (y a)) + ∑ a : U, eU a * iota (z a)
        simp only [map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r y => by
        change ∑ a : U, eU a * iota (r • y a) = r • ∑ a : U, eU a * iota (y a)
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_smul, Algebra.mul_smul_comm] }
  let S : E →ₗ[ZMod 2] ((Fin b → ZMod 2) × F) := S0.prod S1
  let W := LinearMap.ker S
  have hE_rank : Module.finrank (ZMod 2) E = 2 ^ h * b := by
    rw [Module.finrank_pi_fintype (ZMod 2)]
    simp [U, ZMod.card]
  have hcod_rank : Module.finrank (ZMod 2) ((Fin b → ZMod 2) × F) = b + h := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, hF_rank]
  have hrange_le : Module.finrank (ZMod 2) (LinearMap.range S) ≤ b + h := by
    calc Module.finrank (ZMod 2) (LinearMap.range S)
        ≤ Module.finrank (ZMod 2) ((Fin b → ZMod 2) × F) := Submodule.finrank_le _
      _ = b + h := hcod_rank
  have hrn : Module.finrank (ZMod 2) (LinearMap.range S) + Module.finrank (ZMod 2) W =
      2 ^ h * b := by
    rw [LinearMap.finrank_range_add_finrank_ker S, hE_rank]
  have hmW : m ≤ Module.finrank (ZMod 2) W := by omega
  let dW := Module.finrank (ZMod 2) W
  let eW : (Fin dW → ZMod 2) ≃ₗ[ZMod 2] W :=
    LinearEquiv.ofFinrankEq (Fin dW → ZMod 2) W (Module.finrank_fin_fun (ZMod 2))
  let emb : V →ₗ[ZMod 2] W := eW.toLinearMap.comp (padLin hmW)
  have hemb_inj : Function.Injective emb := eW.injective.comp (padLin_inj hmW)
  let label : U → V → Bool := fun u x => decide ((emb x).1 u ≠ 0)
  refine ⟨label, ?_, ?_, ?_⟩
  · let ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((U × V) →ₗ[ZMod 2] ZMod 2) :=
      fun j p =>
        if hj : j.val < h then
          (LinearMap.proj ⟨j.val, hj⟩).comp (LinearMap.fst (ZMod 2) U V)
        else
          let u : U := fun i => p ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_of_not_lt hj)⟩
          ((LinearMap.proj ⟨j.val - h, by omega⟩).comp
            ((LinearMap.proj u).comp ((Submodule.subtype W).comp emb))).comp
            (LinearMap.snd (ZMod 2) U V)
    let answers : U → V → Fin q → ZMod 2 := fun u x j =>
      if hj : j.val < h then u ⟨j.val, hj⟩
      else ((emb x).1 u) ⟨j.val - h, by omega⟩
    let leaf : (Fin q → ZMod 2) → Bool := fun a =>
      decide (∃ r : Fin b, a ⟨h + r.val, by omega⟩ ≠ 0)
    refine ⟨ask, answers, leaf, ?_, ?_⟩
    · intro u x j
      by_cases hj : j.val < h
      · simp [ask, answers, hj]
      · simp [ask, answers, hj]
    · intro u x
      simp only [label, leaf, decide_eq_decide]
      constructor
      · intro hne
        by_contra hall
        push Not at hall
        apply hne
        funext r
        have hr := hall r
        have hnh : ¬ (h + r.val < h) := by omega
        simpa [answers, hnh] using hr
      · rintro ⟨r, hr⟩ heq
        have hnh : ¬ (h + r.val < h) := by omega
        apply hr
        simp [answers, hnh, heq]
  · intro u
    simp [label]
    rfl
  · intro x hx live hlive
    by_contra hnone
    push Not at hnone
    have hy0 : ∀ a ∈ live, (emb x).1 a = 0 := by
      intro a ha
      have hfa := hnone a ha
      simpa [label] using hfa
    let y : E := (emb x).1
    have hy_ne : y ≠ 0 := by
      intro h0
      apply hx
      apply hemb_inj
      apply Subtype.ext
      simpa [y] using h0
    have hy_ker : S y = 0 := (emb x).2
    have hS0 : S0 y = 0 := congrArg Prod.fst hy_ker
    have hS1 : S1 y = 0 := congrArg Prod.snd hy_ker
    let supp : Finset U := Finset.univ.filter (fun a => y a ≠ 0)
    have hdisj : Disjoint supp live := by
      rw [Finset.disjoint_left]
      intro a has hal
      exact (Finset.mem_filter.mp has).2 (hy0 a hal)
    have hcard_le : supp.card + live.card ≤ 2 ^ h := by
      calc supp.card + live.card
          = (supp ∪ live).card := (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ Finset.univ.card := Finset.card_le_univ _
        _ = Fintype.card U := Finset.card_univ
        _ = 2 ^ h := by simp [U, ZMod.card]
    have hsupp_le : supp.card ≤ 2 := by omega
    have hsum0 : ∑ a ∈ supp, y a = 0 := by
      rw [← hS0]
      change ∑ a ∈ supp, y a = ∑ a : U, y a
      apply Finset.sum_subset (Finset.subset_univ supp)
      intro a _ has
      by_contra hne
      exact has (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hne⟩)
    have hsum1 : ∑ a ∈ supp, eU a * iota (y a) = 0 := by
      rw [← hS1]
      change ∑ a ∈ supp, eU a * iota (y a) = ∑ a : U, eU a * iota (y a)
      apply Finset.sum_subset (Finset.subset_univ supp)
      intro a _ has
      have hya : y a = 0 := by
        by_contra hne
        exact has (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hne⟩)
      simp [hya]
    interval_cases hsc : supp.card
    · rw [Finset.card_eq_zero] at hsc
      apply hy_ne
      funext a
      by_contra hne
      have ha : a ∈ supp := Finset.mem_filter.mpr ⟨Finset.mem_univ a, hne⟩
      rw [hsc] at ha
      exact Finset.notMem_empty a ha
    · obtain ⟨a1, ha1⟩ := Finset.card_eq_one.mp hsc
      have ha1_mem : a1 ∈ supp := by rw [ha1]; simp
      have hya1_ne : y a1 ≠ 0 := (Finset.mem_filter.mp ha1_mem).2
      rw [ha1, Finset.sum_singleton] at hsum0
      exact hya1_ne hsum0
    · obtain ⟨a1, a2, hne12, ha12⟩ := Finset.card_eq_two.mp hsc
      have ha1_mem : a1 ∈ supp := by rw [ha12]; simp
      have hya1_ne : y a1 ≠ 0 := (Finset.mem_filter.mp ha1_mem).2
      rw [ha12, Finset.sum_pair hne12] at hsum0 hsum1
      have hya2 : y a2 = - y a1 := eq_neg_of_add_eq_zero_right hsum0
      have hmul : (eU a1 - eU a2) * iota (y a1) = 0 := by
        calc (eU a1 - eU a2) * iota (y a1)
            = eU a1 * iota (y a1) - eU a2 * iota (y a1) := sub_mul _ _ _
          _ = eU a1 * iota (y a1) + eU a2 * (-(iota (y a1))) := by ring
          _ = eU a1 * iota (y a1) + eU a2 * iota (- y a1) := by rw [map_neg]
          _ = eU a1 * iota (y a1) + eU a2 * iota (y a2) := by rw [hya2]
          _ = 0 := hsum1
      have he_ne : eU a1 - eU a2 ≠ 0 := sub_ne_zero.mpr (fun heq => hne12 (eU.injective heq))
      have hi_ne : iota (y a1) ≠ 0 := by
        intro hi0
        apply hya1_ne
        exact hiota_inj (hi0.trans (map_zero iota).symm)
      exact mul_ne_zero he_ne hi_ne hmul

private lemma block_deficit_bound {b k : Nat} (hb : 2 ≤ b) (hk : 1 ≤ k) :
    b + k ≤ 2 ^ k * b ∧ 2 ^ k ≤ 2 * (2 ^ k * b - (b + k)) := by
  induction k, hk using Nat.le_induction with
  | base =>
    constructor <;> omega
  | succ k hk ih =>
    have hpow : 2 ^ k ≥ 2 := by
      have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
      simpa using this
    have hpow1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
    have hmul : 2 ^ (k + 1) * b = 2 * (2 ^ k * b) := by rw [hpow1]; ring
    have hb2 : 2 ^ k * 2 ≤ 2 ^ k * b := Nat.mul_le_mul_left _ hb
    omega

private lemma block_charge_le {b k : Nat} (hb : 2 ≤ b) : b + k ≤ 2 ^ k * b := by
  by_cases hk : k = 0
  · subst hk; simp
  · exact (block_deficit_bound hb (Nat.pos_of_ne_zero hk)).1

private lemma four_mul_le_pow_pred {h : Nat} (hh : 6 ≤ h) : 4 * h ≤ 2 ^ (h - 1) := by
  induction h, hh using Nat.le_induction with
  | base => decide
  | succ h hh ih =>
    have h1 : h + 1 - 1 = (h - 1) + 1 := by omega
    rw [h1, Nat.pow_succ]
    omega

private lemma pow_pred_le_pred_pow {b : Nat} (hb : 2 ≤ b) : 2 ^ (b - 1) ≤ 2 ^ b - 1 := by
  have h1 : 2 ^ b = 2 * 2 ^ (b - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ b), Nat.pow_succ]
    ring
  have hpos : 1 ≤ 2 ^ (b - 1) := Nat.one_le_pow _ _ (by omega)
  omega

private lemma converse (m h b : Nat) (hh : 6 ≤ h) (hb : 2 ≤ b) (hbh : b < h)
    (hspec :
      let q := h + b
      let U := Fin h → ZMod 2
      let V := Fin m → ZMod 2
      let feasible := fun (label : U → V → Bool) =>
        ∃ (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((U × V) →ₗ[ZMod 2] ZMod 2))
          (answers : U → V → Fin q → ZMod 2) (leaf : (Fin q → ZMod 2) → Bool),
          (∀ (u : U) (x : V) (j : Fin q), answers u x j =
            ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u, x)) ∧
          ∀ (u : U) (x : V), label u x = leaf (answers u x)
      ∃ label : U → V → Bool, feasible label ∧
        (∀ witness, label witness 0 = false) ∧
        ∀ x : V, x ≠ 0 → ∀ live : Finset U, 2 ^ h ≤ live.card + 2 →
          ∃ address ∈ live, label address x = true) :
    m + h + b ≤ 2 ^ h * b := by
  dsimp only at hspec
  set q := h + b
  let U := Fin h → ZMod 2
  let V := Fin m → ZMod 2
  rcases hspec with ⟨label, ⟨ask, answers, leaf, hans, hleaf⟩, hzero, hdet⟩
  let L : Finset (Fin q → ZMod 2) := Finset.univ.image (fun u : U => answers u 0)
  let G : (Fin q → ZMod 2) → (U →ₗ[ZMod 2] (Fin q → ZMod 2)) := fun ell =>
    LinearMap.pi fun j =>
      (ask j (fun i => ell ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩)).comp (LinearMap.inl (ZMod 2) U V)
  let Phi : (Fin q → ZMod 2) → (V →ₗ[ZMod 2] (Fin q → ZMod 2)) := fun ell =>
    LinearMap.pi fun j =>
      (ask j (fun i => ell ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩)).comp (LinearMap.inr (ZMod 2) U V)
  have hpath_iff : ∀ (ell : Fin q → ZMod 2) (u : U) (x : V),
      answers u x = ell ↔ G ell u + Phi ell x = ell := by
    intro ell u x
    constructor
    · intro hux
      funext j
      have h1 : answers u x j =
          ask j (fun i => ell ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u, x) := by
        rw [hans u x j, hux]
      have h2 : (u, x) = (u, (0 : V)) + ((0 : U), x) := by simp
      calc (G ell u + Phi ell x) j
          = ask j (fun i => ell ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u, 0) +
            ask j (fun i => ell ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (0, x) := rfl
        _ = ask j (fun i => ell ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) ((u, 0) + (0, x)) :=
            (map_add _ _ _).symm
        _ = ask j (fun i => ell ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u, x) := by rw [← h2]
        _ = answers u x j := h1.symm
        _ = ell j := congrFun hux j
    · intro hsum
      have hrec : ∀ (n : Nat) (hn : n < q), answers u x ⟨n, hn⟩ = ell ⟨n, hn⟩ := by
        intro n
        induction n using Nat.strong_induction_on with
        | ind n ih =>
          intro hn
          rw [hans u x ⟨n, hn⟩]
          have hpref : (fun i : Fin n => answers u x ⟨i.val, Nat.lt_trans i.isLt hn⟩) =
              (fun i : Fin n => ell ⟨i.val, Nat.lt_trans i.isLt hn⟩) := by
            funext i
            exact ih i.val i.isLt (Nat.lt_trans i.isLt hn)
          rw [hpref]
          have h2 : (u, x) = (u, (0 : V)) + ((0 : U), x) := by simp
          rw [h2, map_add]
          exact congrFun hsum ⟨n, hn⟩
      funext j
      exact hrec j.val j.isLt
  let B : (Fin q → ZMod 2) → Finset U := fun ell => Finset.univ.filter (fun u => answers u 0 = ell)
  have hB_sum : ∑ ell ∈ L, (B ell).card = 2 ^ h := by
    have hcardU : (Finset.univ : Finset U).card = 2 ^ h := by
      simp [U, ZMod.card]
    rw [← hcardU]
    symm
    exact Finset.card_eq_sum_card_fiberwise (f := fun u : U => answers u 0) (s := Finset.univ)
      (t := L) (fun u _ => Finset.mem_image_of_mem _ (Finset.mem_univ u))
  have hleaf_false : ∀ ell ∈ L, leaf ell = false := by
    intro ell hell
    rcases Finset.mem_image.mp hell with ⟨u0, _, rfl⟩
    rw [← hleaf u0 0, hzero u0]
  let kval : (Fin q → ZMod 2) → Nat := fun ell => Module.finrank (ZMod 2) (LinearMap.ker (G ell))
  have hB_card : ∀ ell ∈ L, (B ell).card = 2 ^ (kval ell) := by
    intro ell hell
    rcases Finset.mem_image.mp hell with ⟨u0, _, hu0⟩
    have hu0G : G ell u0 = ell := by
      have := (hpath_iff ell u0 0).mp hu0
      simpa using this
    let f : LinearMap.ker (G ell) ≃ { u : U // u ∈ B ell } :=
      { toFun := fun v => ⟨u0 + v.1, by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, (hpath_iff ell (u0 + v.1) 0).mpr ?_⟩
          simp [map_add, hu0G, LinearMap.mem_ker.mp v.2]⟩
        invFun := fun u => ⟨u.1 - u0, by
          rw [LinearMap.mem_ker, map_sub]
          have huG : G ell u.1 = ell := by
            have h1 := (Finset.mem_filter.mp u.2).2
            have h2 := (hpath_iff ell u.1 0).mp h1
            simpa using h2
          rw [huG, hu0G, sub_self]⟩
        left_inv := fun v => by ext; simp
        right_inv := fun u => by ext; simp }
    have hc1 : Fintype.card (LinearMap.ker (G ell)) = Fintype.card { u : U // u ∈ B ell } :=
      Fintype.card_congr f
    rw [Fintype.card_coe] at hc1
    rw [← hc1, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  let W : { ell // ell ∈ L } → Type := fun ell => (Fin q → ZMod 2) ⧸ LinearMap.range (G ell.1)
  let Qcomp : ∀ ell : { ell // ell ∈ L }, V →ₗ[ZMod 2] W ell := fun ell =>
    (LinearMap.range (G ell.1)).mkQ.comp (Phi ell.1)
  let E := ∀ ell : { ell // ell ∈ L }, W ell
  let Q : V →ₗ[ZMod 2] E := LinearMap.pi Qcomp
  have hW_rank : ∀ ell : { ell // ell ∈ L }, Module.finrank (ZMod 2) (W ell) = b + kval ell.1 := by
    intro ell
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range (G ell.1))
    have h2 := LinearMap.finrank_range_add_finrank_ker (G ell.1)
    have hq : Module.finrank (ZMod 2) (Fin q → ZMod 2) = h + b := Module.finrank_fin_fun (ZMod 2)
    have hU : Module.finrank (ZMod 2) U = h := Module.finrank_fin_fun (ZMod 2)
    change Module.finrank (ZMod 2) (W ell) + Module.finrank (ZMod 2) (LinearMap.range (G ell.1)) =
      Module.finrank (ZMod 2) (Fin q → ZMod 2) at h1
    rw [hq] at h1
    rw [hU] at h2
    change Module.finrank (ZMod 2) (LinearMap.range (G ell.1)) + kval ell.1 = h at h2
    omega
  have hvanish : ∀ (x : V) (K : Finset { ell // ell ∈ L }),
      (∀ ell ∈ K, Qcomp ell x = 0) →
      2 ^ h ≤ (∑ ell ∈ K, (B ell.1).card) + 2 →
      x = 0 := by
    intro x K hKQ hKsum
    by_contra hx
    let A : { ell // ell ∈ L } → Finset U := fun ell =>
      Finset.univ.filter (fun u' => answers u' x = ell.1)
    have hBA : ∀ ell ∈ K, (B ell.1).card ≤ (A ell).card := by
      intro ell hell
      have hq0 : Qcomp ell x = 0 := hKQ ell hell
      have hmem : Phi ell.1 x ∈ LinearMap.range (G ell.1) :=
        (Submodule.Quotient.mk_eq_zero _).mp hq0
      rcases hmem with ⟨du, hdu⟩
      have hinj : Set.InjOn (fun u : U => u - du) (B ell.1 : Set U) := by
        intro u1 _ u2 _ h12
        exact sub_left_inj.mp h12
      have hmaps : Set.MapsTo (fun u : U => u - du) (B ell.1 : Set U) (A ell : Set U) := by
        intro u hu
        rw [Finset.mem_coe, Finset.mem_filter] at hu ⊢
        refine ⟨Finset.mem_univ _, (hpath_iff ell.1 (u - du) x).mpr ?_⟩
        have huG : G ell.1 u = ell.1 := by
          have := (hpath_iff ell.1 u 0).mp hu.2
          simpa using this
        rw [map_sub, huG, hdu, sub_add_cancel]
      exact Finset.card_le_card_of_injOn (fun u => u - du) hmaps hinj
    let live : Finset U := K.biUnion A
    have hdisj : Set.PairwiseDisjoint (K : Set { ell // ell ∈ L }) A := by
      intro e1 _ e2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      have h1 := (Finset.mem_filter.mp hu1).2
      have h2 := (Finset.mem_filter.mp hu2).2
      apply hne
      apply Subtype.ext
      exact h1.symm.trans h2
    have hlive_card : 2 ^ h ≤ live.card + 2 := by
      have h1 : live.card = ∑ ell ∈ K, (A ell).card := Finset.card_biUnion hdisj
      have h2 : ∑ ell ∈ K, (B ell.1).card ≤ ∑ ell ∈ K, (A ell).card :=
        Finset.sum_le_sum hBA
      omega
    obtain ⟨u, hu_mem, hu_true⟩ := hdet x hx live hlive_card
    rcases Finset.mem_biUnion.mp hu_mem with ⟨ell, _, huA⟩
    have hu_ans : answers u x = ell.1 := (Finset.mem_filter.mp huA).2
    have hu_false : label u x = false := by
      rw [hleaf u x, hu_ans]
      exact hleaf_false ell.1 ell.2
    rw [hu_false] at hu_true
    exact Bool.false_ne_true hu_true
  have hQ_inj : Function.Injective Q := by
    rw [injective_iff_map_eq_zero]
    intro x hQx
    refine hvanish x Finset.univ (fun ell _ => congrFun hQx ell) ?_
    have hsum_univ : ∑ ell : { ell // ell ∈ L }, (B ell.1).card = 2 ^ h := by
      rw [← hB_sum]
      exact Finset.sum_coe_sort L (fun ell => (B ell).card)
    omega
  let C : Nat := Module.finrank (ZMod 2) E
  have hC_eq : C = ∑ ell ∈ L, (b + kval ell) := by
    change Module.finrank (ZMod 2) (∀ ell : { ell // ell ∈ L }, W ell) = _
    rw [Module.finrank_pi_fintype (ZMod 2)]
    simp_rw [hW_rank]
    exact Finset.sum_coe_sort L (fun ell => b + kval ell)
  have hC_le : C ≤ 2 ^ h * b := by
    rw [hC_eq]
    calc ∑ ell ∈ L, (b + kval ell)
        ≤ ∑ ell ∈ L, 2 ^ (kval ell) * b := Finset.sum_le_sum (fun ell _ => block_charge_le hb)
      _ = (∑ ell ∈ L, 2 ^ (kval ell)) * b := (Finset.sum_mul _ _ _).symm
      _ = (∑ ell ∈ L, (B ell).card) * b := by
          congr 1
          exact Finset.sum_congr rfl fun ell hell => (hB_card ell hell).symm
      _ = 2 ^ h * b := by rw [hB_sum]
  let D : Nat := 2 ^ h * b - C
  have hCD : C + D = 2 ^ h * b := Nat.add_sub_of_le hC_le
  let M : Submodule (ZMod 2) E := LinearMap.range Q
  let R : Nat := Module.finrank (ZMod 2) (E ⧸ M)
  have hM_rank : Module.finrank (ZMod 2) M = m := by
    rw [LinearMap.finrank_range_of_inj hQ_inj]
    exact Module.finrank_fin_fun (ZMod 2)
  have hRmC : R + m = C := by
    have h1 := Submodule.finrank_quotient_add_finrank M
    rw [hM_rank] at h1
    exact h1
  suffices hRD : h + b ≤ R + D by omega
  by_cases hDge : h + b ≤ D
  · omega
  · push Not at hDge
    let S : Finset { ell // ell ∈ L } := Finset.univ.filter (fun ell => kval ell.1 = 0)
    let Lns : Finset (Fin q → ZMod 2) := L.filter (fun ell => kval ell ≠ 0)
    let Ls : Finset (Fin q → ZMod 2) := L.filter (fun ell => kval ell = 0)
    have hS_card_eq : S.card = Ls.card := by
      have : S = Finset.univ.filter (fun ell : { ell // ell ∈ L } => ell.1 ∈ Ls) := by
        ext ell
        simp [S, Ls]
      rw [this]
      refine Finset.card_bij (fun ell _ => ell.1) ?_ ?_ ?_
      · intro ell hell
        exact (Finset.mem_filter.mp hell).2
      · intro e1 _ e2 _ h12
        exact Subtype.ext h12
      · intro ell hell
        exact ⟨⟨ell, (Finset.mem_filter.mp hell).1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hell⟩, rfl⟩
    have hD_sum : D = ∑ ell ∈ L, (2 ^ (kval ell) * b - (b + kval ell)) := by
      have htot : (∑ ell ∈ L, (2 ^ (kval ell) * b - (b + kval ell))) + ∑ ell ∈ L, (b + kval ell) =
          2 ^ h * b := by
        rw [← Finset.sum_add_distrib]
        calc ∑ ell ∈ L, (2 ^ (kval ell) * b - (b + kval ell) + (b + kval ell))
            = ∑ ell ∈ L, 2 ^ (kval ell) * b :=
              Finset.sum_congr rfl fun ell _ => Nat.sub_add_cancel (block_charge_le hb)
          _ = (∑ ell ∈ L, 2 ^ (kval ell)) * b := (Finset.sum_mul _ _ _).symm
          _ = (∑ ell ∈ L, (B ell).card) * b := by
              congr 1
              exact Finset.sum_congr rfl fun ell hell => (hB_card ell hell).symm
          _ = 2 ^ h * b := by rw [hB_sum]
      omega
    have hns_le : ∑ ell ∈ Lns, (B ell).card ≤ 2 * D := by
      calc ∑ ell ∈ Lns, (B ell).card
          = ∑ ell ∈ Lns, 2 ^ (kval ell) :=
            Finset.sum_congr rfl fun ell hell => hB_card ell (Finset.mem_filter.mp hell).1
        _ ≤ ∑ ell ∈ Lns, 2 * (2 ^ (kval ell) * b - (b + kval ell)) := by
            refine Finset.sum_le_sum fun ell hell => ?_
            have hk1 : 1 ≤ kval ell := Nat.pos_of_ne_zero (Finset.mem_filter.mp hell).2
            exact (block_deficit_bound hb hk1).2
        _ = 2 * ∑ ell ∈ Lns, (2 ^ (kval ell) * b - (b + kval ell)) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ 2 * ∑ ell ∈ L, (2 ^ (kval ell) * b - (b + kval ell)) := by
            apply Nat.mul_le_mul_left
            exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = 2 * D := by rw [← hD_sum]
    have hsplit : Ls.card + ∑ ell ∈ Lns, (B ell).card = 2 ^ h := by
      have h1 : (∑ ell ∈ Ls, (B ell).card) + ∑ ell ∈ Lns, (B ell).card = ∑ ell ∈ L, (B ell).card :=
        Finset.sum_filter_add_sum_filter_not L (fun ell => kval ell = 0) (fun ell => (B ell).card)
      have h2 : ∑ ell ∈ Ls, (B ell).card = Ls.card := by
        calc ∑ ell ∈ Ls, (B ell).card
            = ∑ ell ∈ Ls, 1 := by
              refine Finset.sum_congr rfl fun ell hell => ?_
              rw [hB_card ell (Finset.mem_filter.mp hell).1, (Finset.mem_filter.mp hell).2]
              simp
          _ = Ls.card := by simp
      rw [h2, hB_sum] at h1
      exact h1
    have hS_lb : 2 ^ h ≤ S.card + 2 * D := by omega
    let phi : (Σ ell : S, { v : W ell.1 // v ≠ 0 }) → { z : E ⧸ M // z ≠ 0 } :=
      fun ⟨ell, ⟨v, hv⟩⟩ =>
        ⟨M.mkQ (Pi.single ell.1 v), by
          intro h0
          have hmem : Pi.single ell.1 v ∈ M := (Submodule.Quotient.mk_eq_zero M).mp h0
          rcases hmem with ⟨x, hx⟩
          have hx0 : x = 0 := by
            refine hvanish x (Finset.univ.erase ell.1) ?_ ?_
            · intro ell' hell'
              have hne : ell' ≠ ell.1 := (Finset.mem_erase.mp hell').1
              have h1 : Qcomp ell' x = Pi.single ell.1 v ell' := congrFun hx ell'
              rw [Pi.single_eq_of_ne hne] at h1
              exact h1
            · have hsum_all : ∑ e : { e // e ∈ L }, (B e.1).card = 2 ^ h := by
                rw [← hB_sum]
                exact Finset.sum_coe_sort L (fun e => (B e).card)
              have hBe : (B ell.1.1).card = 1 := by
                rw [hB_card ell.1.1 ell.1.2, (Finset.mem_filter.mp ell.2).2]
                simp
              have hsum_er : (∑ e ∈ Finset.univ.erase ell.1, (B e.1).card) + (B ell.1.1).card =
                  ∑ e : { e // e ∈ L }, (B e.1).card :=
                Finset.sum_erase_add Finset.univ (fun e : { e // e ∈ L } => (B e.1).card) (Finset.mem_univ _)
              omega
          rw [hx0, map_zero] at hx
          have hv0 : v = 0 := by
            have h1 : (0 : W ell.1) = Pi.single ell.1 v ell.1 := congrFun hx ell.1
            rw [Pi.single_eq_same] at h1
            exact h1.symm
          exact hv hv0⟩
    have hphi_inj : Function.Injective phi := by
      rintro ⟨e1, ⟨v1, hv1⟩⟩ ⟨e2, ⟨v2, hv2⟩⟩ heq
      have hmk : M.mkQ (Pi.single e1.1 v1 - Pi.single e2.1 v2) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val heq
      have hmem : Pi.single e1.1 v1 - Pi.single e2.1 v2 ∈ M :=
        (Submodule.Quotient.mk_eq_zero M).mp hmk
      rcases hmem with ⟨x, hx⟩
      have hx0 : x = 0 := by
        refine hvanish x ((Finset.univ.erase e1.1).erase e2.1) ?_ ?_
        · intro ell' hell'
          have hne2 : ell' ≠ e2.1 := (Finset.mem_erase.mp hell').1
          have hne1 : ell' ≠ e1.1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hell').2).1
          have h1 : Qcomp ell' x = Pi.single e1.1 v1 ell' - Pi.single e2.1 v2 ell' := congrFun hx ell'
          simpa [Pi.single_eq_of_ne hne1, Pi.single_eq_of_ne hne2] using h1
        · have hsum_all : ∑ e : { e // e ∈ L }, (B e.1).card = 2 ^ h := by
            rw [← hB_sum]
            exact Finset.sum_coe_sort L (fun e => (B e).card)
          have hB1 : (B e1.1.1).card = 1 := by
            rw [hB_card e1.1.1 e1.1.2, (Finset.mem_filter.mp e1.2).2]; simp
          have hB2 : (B e2.1.1).card = 1 := by
            rw [hB_card e2.1.1 e2.1.2, (Finset.mem_filter.mp e2.2).2]; simp
          have h1 : (∑ e ∈ Finset.univ.erase e1.1, (B e.1).card) + (B e1.1.1).card = 2 ^ h := by
            rw [← hsum_all]
            exact Finset.sum_erase_add Finset.univ (fun e : { e // e ∈ L } => (B e.1).card) (Finset.mem_univ _)
          by_cases h12 : e2.1 ∈ Finset.univ.erase e1.1
          · have h2 : (∑ e ∈ (Finset.univ.erase e1.1).erase e2.1, (B e.1).card) + (B e2.1.1).card =
                ∑ e ∈ Finset.univ.erase e1.1, (B e.1).card :=
              Finset.sum_erase_add _ (fun e : { e // e ∈ L } => (B e.1).card) h12
            omega
          · rw [Finset.erase_eq_of_notMem h12]
            omega
      rw [hx0, map_zero] at hx
      have hdiff0 : Pi.single e1.1 v1 = Pi.single e2.1 v2 := (sub_eq_zero.mp hx.symm)
      by_cases h12 : e1.1 = e2.1
      · have he : e1 = e2 := Subtype.ext h12
        subst he
        have hv12 : v1 = v2 := by
          have := congrFun hdiff0 e1.1
          simpa using this
        subst hv12
        rfl
      · exfalso
        have := congrFun hdiff0 e1.1
        simp [Pi.single_eq_of_ne h12] at this
        exact hv1 this
    have hpack : S.card * (2 ^ b - 1) ≤ 2 ^ R - 1 := by
      have hle := Fintype.card_le_of_injective phi hphi_inj
      have hcard_dom : Fintype.card (Σ ell : S, { v : W ell.1 // v ≠ 0 }) = S.card * (2 ^ b - 1) := by
        rw [Fintype.card_sigma]
        calc ∑ ell : S, Fintype.card { v : W ell.1 // v ≠ 0 }
            = ∑ _ell : S, (2 ^ b - 1) := by
              refine Finset.sum_congr rfl fun ell _ => ?_
              rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
              rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hW_rank ell.1,
                (Finset.mem_filter.mp ell.2).2, add_zero]
          _ = S.card * (2 ^ b - 1) := by simp
      have hcard_cod : Fintype.card { z : E ⧸ M // z ≠ 0 } = 2 ^ R - 1 := by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
        rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
      rw [hcard_dom, hcard_cod] at hle
      exact hle
    have h2R_pos : 1 ≤ 2 ^ R := Nat.one_le_pow _ _ (by omega)
    have h2b_lb : 2 ^ (b - 1) ≤ 2 ^ b - 1 := pow_pred_le_pred_pow hb
    by_cases hD0 : D = 0
    · have hS_full : 2 ^ h ≤ S.card := by omega
      have hgt : 2 ^ (h + b - 1) < 2 ^ R := by
        have h1 : 2 ^ h * 2 ^ (b - 1) ≤ S.card * (2 ^ b - 1) := Nat.mul_le_mul hS_full h2b_lb
        have h2 : 2 ^ (h + b - 1) = 2 ^ h * 2 ^ (b - 1) := by
          rw [← Nat.pow_add]
          congr 1
          omega
        omega
      have hRge : h + b - 1 < R := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hgt
      omega
    · have h4h : 4 * h ≤ 2 ^ (h - 1) := four_mul_le_pow_pred hh
      have hpow_h : 2 ^ h = 2 * 2 ^ (h - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ h), Nat.pow_succ]
        ring
      have hS_half : 2 ^ (h - 1) ≤ S.card := by omega
      have hgt : 2 ^ (h + b - 2) < 2 ^ R := by
        have h1 : 2 ^ (h - 1) * 2 ^ (b - 1) ≤ S.card * (2 ^ b - 1) := Nat.mul_le_mul hS_half h2b_lb
        have h2 : 2 ^ (h + b - 2) = 2 ^ (h - 1) * 2 ^ (b - 1) := by
          rw [← Nat.pow_add]
          congr 1
          omega
        omega
      have hRge : h + b - 2 < R := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hgt
      omega

end PEqualNP.Outside.L_meta_25776_aux

theorem PEqualNP.Outside.L_meta_25776 :
    ∀ (m h b : Nat), 6 ≤ h → 2 ≤ b → b < h →
      let q := h+b
      let U := Fin h → ZMod 2
      let V := Fin m → ZMod 2
      let feasible := fun (label : U → V → Bool) =>
        ∃ (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((U × V) →ₗ[ZMod 2] ZMod 2))
          (answers : U → V → Fin q → ZMod 2) (leaf : (Fin q → ZMod 2) → Bool),
          (∀ (u : U) (x : V) (j : Fin q), answers u x j =
            ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u,x)) ∧
          ∀ (u : U) (x : V), label u x = leaf (answers u x)
      (∃ label : U → V → Bool, feasible label ∧
        (∀ witness, label witness 0 = false) ∧
        ∀ x : V, x ≠ 0 → ∀ live : Finset U, 2^h ≤ live.card+2 →
          ∃ address ∈ live, label address x = true) ↔ m+h+b ≤ 2^h*b := by
  intro m h b hh hb hbh
  constructor
  · exact PEqualNP.Outside.L_meta_25776_aux.converse m h b hh hb hbh
  · exact PEqualNP.Outside.L_meta_25776_aux.attainment m h b hh hb hbh
