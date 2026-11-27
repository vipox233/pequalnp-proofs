import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25775

open scoped Classical

lemma pad_inj {a c : Nat} (hac : a ≤ c) :
    Function.Injective
      (fun (x : Fin a → ZMod 2) (i : Fin c) =>
        if hi : i.val < a then x ⟨i.val, hi⟩ else 0) := by
  intro x y hxy
  funext j
  have h := congrFun hxy ⟨j.val, Nat.lt_of_lt_of_le j.isLt hac⟩
  simpa [j.isLt] using h

def padLin {a c : Nat} (_hac : a ≤ c) :
    (Fin a → ZMod 2) →ₗ[ZMod 2] (Fin c → ZMod 2) where
  toFun x i := if hi : i.val < a then x ⟨i.val, hi⟩ else 0
  map_add' x y := by
    funext i
    by_cases hi : i.val < a <;> simp [hi]
  map_smul' r x := by
    funext i
    by_cases hi : i.val < a <;> simp [hi]

lemma padLin_inj {a c : Nat} (hac : a ≤ c) : Function.Injective (padLin hac) :=
  pad_inj hac

lemma attain_small (m h b R : Nat) (hR : 0 < R) (hm : m ≤ h + b) :
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
      ∀ (x : V), x ≠ 0 → ∀ survivors : Finset U, R ≤ survivors.card →
        ∃ witness ∈ survivors, label witness x = true := by
  intro q U V feasible
  let E := padLin hm
  let label : U → V → Bool := fun _ x => decide (E x ≠ 0)
  refine ⟨label, ⟨fun j _ => (LinearMap.proj j).comp (E.comp (LinearMap.snd (ZMod 2) U V)),
    fun _ x => E x, fun a => decide (a ≠ 0), fun u x j => rfl, fun u x => rfl⟩, ?_, ?_⟩
  · intro w; simp [label]
  · intro x hx S hS
    obtain ⟨w, hw⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨w, hw, ?_⟩
    have : E x ≠ 0 := fun h0 => hx (padLin_inj hm (h0.trans (map_zero _).symm))
    simpa [label] using this

lemma attain_big (m h b R : Nat) (hb : 2 ≤ b) (hhb : h ≤ b) (hm : m ≤ R * b) :
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
      ∀ (x : V), x ≠ 0 → ∀ survivors : Finset U, R ≤ survivors.card →
        ∃ witness ∈ survivors, label witness x = true := by
  intro q U V feasible
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 b
  have hb0 : b ≠ 0 := by omega
  have hF_rank : Module.finrank (ZMod 2) F = b := GaloisField.finrank 2 hb0
  let eF : (Fin b → ZMod 2) ≃ₗ[ZMod 2] F :=
    LinearEquiv.ofFinrankEq _ F ((Module.finrank_fin_fun (ZMod 2)).trans hF_rank.symm)
  let eU : U →ₗ[ZMod 2] F := eF.toLinearMap.comp (padLin hhb)
  have heU : Function.Injective eU := eF.injective.comp (padLin_inj hhb)
  have hT_rank : Module.finrank (ZMod 2) (Fin R → F) = R * b := by
    rw [Module.finrank_pi_fintype (ZMod 2)]; simp [hF_rank]
  let eT : (Fin (R * b) → ZMod 2) ≃ₗ[ZMod 2] (Fin R → F) :=
    LinearEquiv.ofFinrankEq _ _ ((Module.finrank_fin_fun (ZMod 2)).trans hT_rank.symm)
  let emb : V →ₗ[ZMod 2] (Fin R → F) := eT.toLinearMap.comp (padLin hm)
  have hemb : Function.Injective emb := eT.injective.comp (padLin_inj hm)
  let ev : U → (V →ₗ[ZMod 2] F) := fun u =>
    { toFun := fun x => ∑ i : Fin R, emb x i * eU u ^ (i : ℕ)
      map_add' := fun x y => by
        simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_mul_assoc] }
  let label : U → V → Bool := fun u x => decide (ev u x ≠ 0)
  refine ⟨label, ?_, ?_, ?_⟩
  · let ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((U × V) →ₗ[ZMod 2] ZMod 2) :=
      fun j p =>
        if hj : j.val < h then
          (LinearMap.proj ⟨j.val, hj⟩).comp (LinearMap.fst (ZMod 2) U V)
        else
          let u : U := fun i => p ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_of_not_lt hj)⟩
          ((LinearMap.proj ⟨j.val - h, by omega⟩).comp
            (eF.symm.toLinearMap.comp (ev u))).comp
            (LinearMap.snd (ZMod 2) U V)
    let answers : U → V → Fin q → ZMod 2 := fun u x j =>
      if hj : j.val < h then u ⟨j.val, hj⟩
      else (eF.symm (ev u x)) ⟨j.val - h, by omega⟩
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
        apply eF.symm.injective
        rw [map_zero]
        funext r
        have hr := hall r
        have hnh : ¬ (h + r.val < h) := by omega
        simpa [answers, hnh] using hr
      · rintro ⟨r, hr⟩ heq
        have hnh : ¬ (h + r.val < h) := by omega
        apply hr
        simp [answers, hnh, heq]
  · intro u
    simp [label, ev]
  · intro x hx S hS
    by_contra hnone
    push Not at hnone
    have h0 : ∀ u ∈ S, ev u x = 0 := by
      intro u hu
      have := hnone u hu
      simpa [label] using this
    let p : Polynomial F := ∑ i : Fin R, Polynomial.C (emb x i) * Polynomial.X ^ (i : ℕ)
    have hp : p = 0 := by
      apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (S.image eU)
      · rw [Finset.card_image_of_injective _ heU]
        exact lt_of_lt_of_le (Polynomial.degree_sum_fin_lt _) (by exact_mod_cast hS)
      · intro y hy
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
        have := h0 u hu
        simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X]
        exact this
    apply hx
    apply hemb
    rw [map_zero]
    funext i
    have := congrArg (fun (f : Polynomial F) => f.coeff i) hp
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single i] at this
    · simpa using this
    · intro j _ hji
      have : (i : ℕ) ≠ j := fun h => hji (Fin.ext h).symm
      simp [this]
    · simp

lemma charge_le {b k : Nat} (hb : 2 ≤ b) : b + k ≤ 2 ^ k * b := by
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  nlinarith

lemma charge2_le {b k : Nat} (hb : 2 ≤ b) : b + 2 * k ≤ 2 ^ k * b := by
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  nlinarith

lemma pick {α : Type*} [DecidableEq α] (b : Nat) (hb : 2 ≤ b) (k : α → Nat) (Z : Finset α) :
    ∀ R : Nat, 1 ≤ R → R ≤ ∑ e ∈ Z, 2 ^ k e →
      ∃ K ⊆ Z, R ≤ ∑ e ∈ K, 2 ^ k e ∧
        (∑ e ∈ K, (b + k e) ≤ b * R ∨ ∃ e ∈ Z, K = {e}) := by
  induction Z using Finset.induction_on with
  | empty => intro R h1 h2; simp at h2; omega
  | insert e Z heZ ih =>
    intro R h1 h2
    rw [Finset.sum_insert heZ] at h2
    by_cases hRZ : R ≤ ∑ e ∈ Z, 2 ^ k e
    · obtain ⟨K, hK, hR, hc⟩ := ih R h1 hRZ
      refine ⟨K, hK.trans (Finset.subset_insert _ _), hR, ?_⟩
      rcases hc with hc | ⟨e', he', rfl⟩
      · exact Or.inl hc
      · exact Or.inr ⟨e', Finset.mem_insert_of_mem he', rfl⟩
    by_cases hRe : R ≤ 2 ^ k e
    · exact ⟨{e}, by simp, by simpa using hRe, Or.inr ⟨e, by simp, rfl⟩⟩
    obtain ⟨K, hK, hR, hc⟩ := ih (R - 2 ^ k e) (by omega) (by omega)
    have heK : e ∉ K := fun h => heZ (hK h)
    rcases hc with hc | ⟨e', he', rfl⟩
    · refine ⟨insert e K, Finset.insert_subset_insert _ hK, ?_, Or.inl ?_⟩
      · rw [Finset.sum_insert heK]; omega
      · rw [Finset.sum_insert heK]
        have := charge_le (k := k e) hb
        have h3 : b * (R - 2 ^ k e) + 2 ^ k e * b = b * R := by
          rw [mul_comm (2 ^ k e) b, ← Nat.mul_add]; congr 1; omega
        omega
    · simp only [Finset.sum_singleton] at hR
      by_cases hR' : R ≤ 2 ^ k e'
      · exact ⟨{e'}, by simp [he'], by simpa using hR', Or.inr ⟨e', Finset.mem_insert_of_mem he', rfl⟩⟩
      have hne : e ≠ e' := fun h => heZ (h ▸ he')
      refine ⟨{e, e'}, ?_, ?_, Or.inl ?_⟩
      · intro x hx; simp at hx; rcases hx with rfl | rfl
        · simp
        · exact Finset.mem_insert_of_mem he'
      · rw [Finset.sum_pair hne]; omega
      · rw [Finset.sum_pair hne]
        rcases le_total (k e) (k e') with hk | hk
        · have := charge2_le (k := k e') hb
          have h4 : 2 ^ k e' * b + b ≤ b * R := by
            have : 2 ^ k e' + 1 ≤ R := by omega
            nlinarith
          omega
        · have := charge2_le (k := k e) hb
          have h4 : 2 ^ k e * b + b ≤ b * R := by
            have : 2 ^ k e + 1 ≤ R := by omega
            nlinarith
          omega

lemma upper (m h b R : Nat) (hb : 2 ≤ b) (hR : 0 < R) (hRh : R ≤ 2 ^ h)
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
        ∀ (x : V), x ≠ 0 → ∀ survivors : Finset U, R ≤ survivors.card →
          ∃ witness ∈ survivors, label witness x = true) :
    m ≤ max (h + b) (R * b) := by
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
      R ≤ (∑ ell ∈ K, (B ell.1).card) →
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
    have hlive_card : R ≤ live.card := by
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
  have hsum_univ : ∑ ell : { ell // ell ∈ L }, 2 ^ kval ell.1 = 2 ^ h := by
    rw [← hB_sum, ← Finset.sum_coe_sort L (fun ell => (B ell).card)]
    exact Finset.sum_congr rfl fun ell _ => (hB_card ell.1 ell.2).symm
  obtain ⟨K, -, hKR, hKc⟩ := pick b hb (fun ell : { ell // ell ∈ L } => kval ell.1)
    Finset.univ R hR (by rw [hsum_univ]; exact hRh)
  have hcost : ∑ ell ∈ K, (b + kval ell.1) ≤ max (h + b) (R * b) := by
    rcases hKc with hc | ⟨e, -, rfl⟩
    · rw [mul_comm] at hc; exact le_max_of_le_right hc
    · rw [Finset.sum_singleton]
      apply le_max_of_le_left
      have h1 : 2 ^ kval e.1 ≤ 2 ^ h := by
        rw [← hB_card e.1 e.2]
        calc (B e.1).card ≤ (Finset.univ : Finset U).card := Finset.card_le_univ _
          _ = 2 ^ h := by simp [U, ZMod.card]
      have h2 : kval e.1 ≤ h := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
      omega
  by_contra hm
  push Not at hm
  let QK : V →ₗ[ZMod 2] ((ell : K) → W ell.1) := LinearMap.pi fun ell => Qcomp ell.1
  have hQK_rank : Module.finrank (ZMod 2) ((ell : K) → W ell.1) = ∑ ell ∈ K, (b + kval ell.1) := by
    rw [Module.finrank_pi_fintype (ZMod 2)]
    simp_rw [hW_rank]
    exact Finset.sum_coe_sort K (fun ell => b + kval ell.1)
  have hnotinj : ¬ Function.Injective QK := by
    intro hinj
    have := LinearMap.finrank_le_finrank_of_injective hinj
    rw [hQK_rank, Module.finrank_fin_fun] at this
    omega
  rw [injective_iff_map_eq_zero] at hnotinj
  push Not at hnotinj
  obtain ⟨x, hx0, hx⟩ := hnotinj
  apply hx
  refine hvanish x K (fun ell hell => congrFun hx0 ⟨ell, hell⟩) ?_
  calc R ≤ ∑ e ∈ K, 2 ^ kval e.1 := hKR
    _ = ∑ e ∈ K, (B e.1).card := Finset.sum_congr rfl fun e _ => (hB_card e.1 e.2).symm

end PEqualNP.Outside.L_meta_25775

theorem PEqualNP.Outside.L_meta_25775 : (∀ (m h b : Nat), 2 ≤ b →
  let q := h+b
  let U := Fin h → ZMod 2
  let V := Fin m → ZMod 2
  let feasible := fun (label : U → V → Bool) =>
    ∃ (ask : (j : Fin q) → (Fin j.val → ZMod 2) → ((U × V) →ₗ[ZMod 2] ZMod 2))
      (answers : U → V → Fin q → ZMod 2) (leaf : (Fin q → ZMod 2) → Bool),
      (∀ (u : U) (x : V) (j : Fin q), answers u x j =
        ask j (fun i => answers u x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) (u,x)) ∧
      ∀ (u : U) (x : V), label u x = leaf (answers u x)
  ∀ remaining : Nat, 0 < remaining → remaining ≤ 2^h →
    let robust := ∃ label : U → V → Bool, feasible label ∧
      (∀ witness, label witness 0 = false) ∧
      ∀ (x : V), x ≠ 0 → ∀ survivors : Finset U, remaining ≤ survivors.card →
        ∃ witness ∈ survivors, label witness x = true
    (robust → m ≤ max q (remaining*b)) ∧
      (h ≤ b → m ≤ max q (remaining*b) → robust)) := by
  intro m h b hb q U V feasible remaining hpos hle robust
  refine ⟨fun hr => PEqualNP.Outside.L_meta_25775.upper m h b remaining hb hpos hle hr,
    fun hhb hm => ?_⟩
  rcases le_max_iff.mp hm with h1 | h1
  · exact PEqualNP.Outside.L_meta_25775.attain_small m h b remaining hpos h1
  · exact PEqualNP.Outside.L_meta_25775.attain_big m h b remaining hb hhb h1
