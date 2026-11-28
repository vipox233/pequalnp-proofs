import PEqualNP.Defs
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.LinearCombination
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.BigOperators.Fin

-- The affine promised circuit is adapted from ceyirelehe47, pull request 50344.
-- That construction also adapts the checked witness from pull request 45056.
namespace PEqualNP.Outside.L_meta_2009

namespace Refute2003.HashCounting

open scoped BigOperators
open Function

abbrev BadChoice {Key Hash : Type*} (bad : Key → Hash → Bool) (x : Key) :=
  { h : Hash // bad x h = true }

theorem exists_family_of_sum_card_lt {Key Hash : Type*} [Fintype Key] [Fintype Hash]
    (bad : Key → Hash → Bool) (R : ℕ)
    (hdensity : (∑ x : Key, (Fintype.card (BadChoice bad x)) ^ R) <
      (Fintype.card Hash) ^ R) :
    ∃ fam : Fin R → Hash, ∀ x : Key, ∃ i : Fin R, bad x (fam i) = false := by
  classical
  by_contra h
  have hn : ∀ fam : Fin R → Hash, ∃ x : Key, ∀ i : Fin R, bad x (fam i) = true := by
    intro fam
    by_contra hx
    apply h
    refine ⟨fam, ?_⟩
    intro x
    by_contra hxi
    exact hx ⟨x, by
      intro i
      cases hev : bad x (fam i) with
      | false => exact False.elim (hxi ⟨i, hev⟩)
      | true => rfl⟩
  choose x hx using hn
  let enc : (Fin R → Hash) → (Σ y : Key, Fin R → BadChoice bad y) :=
    fun f => ⟨x f, fun i => ⟨f i, hx f i⟩⟩
  have hi : Injective enc := by
    intro f g he
    funext i
    exact congrArg (fun z : Σ y : Key, Fin R → BadChoice bad y => (z.2 i).1) he
  have hle := Fintype.card_le_of_injective enc hi
  have asPow : Fintype.card (Fin R → Hash) = (Fintype.card Hash)^R := by
    simp [Fintype.card_fun]
  have asSum : Fintype.card (Σ y : Key, Fin R → BadChoice bad y) =
      ∑ y : Key, (Fintype.card (BadChoice bad y))^R := by
    simp [Fintype.card_sigma, Fintype.card_fun]
  rw [asPow, asSum] at hle
  exact (Nat.not_le_of_gt hdensity) hle

theorem exists_family_of_constant_density {Key Hash : Type*}
    [Fintype Key] [Fintype Hash] [Nonempty Hash] (bad : Key → Hash → Bool)
    (R w : ℕ)
    (hbad : ∀ x : Key, 2 ^ w * Fintype.card (BadChoice bad x) ≤ Fintype.card Hash)
    (hkey : Fintype.card Key < (2 ^ w)^R) :
    ∃ fam : Fin R → Hash, ∀ x : Key, ∃ i : Fin R, bad x (fam i) = false := by
  classical
  apply exists_family_of_sum_card_lt bad R
  let H := Fintype.card Hash
  let B := (2 ^ w)^R
  let s := ∑ x : Key, (Fintype.card (BadChoice bad x))^R
  have hp : 0 < H ^ R := pow_pos Fintype.card_pos R
  have hle : B * s ≤ Fintype.card Key * H ^ R := by
    dsimp [s]
    rw [Finset.mul_sum]
    calc
      (∑ x : Key, B * (Fintype.card (BadChoice bad x))^R) ≤ ∑ _x : Key, H^R := by
        apply Finset.sum_le_sum
        intro x hx
        dsimp [B, H]
        rw [← mul_pow]
        exact Nat.pow_le_pow_left (hbad x) _
      _ = Fintype.card Key * H ^ R := by simp
  by_contra hs
  have hl : H^R ≤ s := by simpa [H, s] using (Nat.le_of_not_gt hs)
  have hlt : Fintype.card Key * H^R < B * H^R := Nat.mul_lt_mul_of_pos_right hkey hp
  exact (Nat.not_lt_of_ge ((Nat.mul_le_mul_left B hl).trans hle)) hlt

end Refute2003.HashCounting

namespace Refute2003.HashCounting

open scoped BigOperators

theorem exists_family_weighted {J Hash : Type*}
    [Fintype J] [Fintype Hash] [Nonempty Hash]
    (K : J → Type*) [∀ i, Fintype (K i)]
    (bad : (i : J) → K i → Hash → Bool) (w : J → ℕ)
    (L B : ℕ) (hw : ∀ i, 1 ≤ w i)
    (hK : ∀ i, Fintype.card (K i) ≤ (2 ^ L) ^ (w i))
    (hbad : ∀ i x, 2 ^ (w i) * Fintype.card (BadChoice (bad i) x) ≤ Fintype.card Hash)
    (hJ : Fintype.card J < 2 ^ B) :
    ∃ fam : Fin (L+B) → Hash, ∀ i x, ∃ j, bad i x (fam j) = false := by
  classical
  let H := Fintype.card Hash
  let R := L+B
  let sub (i : J) := ∑ x : K i, (Fintype.card (BadChoice (bad i) x))^R
  have hH : 0 < H^R := by exact pow_pos Fintype.card_pos _
  have hOne : ∀ i : J, 2^B * sub i ≤ H^R := by
    intro i
    have pre : (2^(w i))^R * sub i ≤ Fintype.card (K i) * H^R := by
      dsimp only [sub]
      rw [Finset.mul_sum]
      calc
        _ ≤ ∑ _x : K i, H^R := by
          apply Finset.sum_le_sum
          intro x hx
          rw [← mul_pow]
          exact Nat.pow_le_pow_left (hbad i x) _
        _ = _ := by simp
    have hsplit : (2^(w i))^R = (2^L)^(w i) * (2^B)^(w i) := by
      simp only [R, ← pow_mul, ← pow_add]
      congr 1
      ring
    rw [hsplit, Nat.mul_assoc] at pre
    have hh : (2^B)^(w i) * sub i ≤ H^R := by
      apply Nat.le_of_mul_le_mul_left _ (show 0 < (2^L)^(w i) by positivity)
      exact pre.trans (Nat.mul_le_mul_right _ (hK i))
    have hpow : 2^B ≤ (2^B)^(w i) := by
      simpa only [pow_one] using
         (Nat.pow_le_pow_right (show 0 < 2^B by positivity) (hw i))
    exact (Nat.mul_le_mul_right _ hpow).trans hh
  have hSum : (∑ i : J, sub i) < H^R := by
    have hss : 2^B*(∑ i : J, sub i) ≤ Fintype.card J*H^R := by
      rw [Finset.mul_sum]
      calc
        _ ≤ ∑ _i : J, H^R := Finset.sum_le_sum (fun i _ => hOne i)
        _ = _ := by simp
    have hh : Fintype.card J*H^R < 2^B*H^R := Nat.mul_lt_mul_of_pos_right hJ hH
    by_contra hn
    exact (Nat.not_lt_of_ge ((Nat.mul_le_mul_left _ (Nat.le_of_not_gt hn)).trans hss)) hh
  let Bad : Sigma K → Hash → Bool := fun x ↦ bad x.1 x.2
  obtain ⟨fam,hfam⟩ := exists_family_of_sum_card_lt Bad R (by
    rw [Fintype.sum_sigma]
    simpa only [Bad, sub, H] using hSum)
  exact ⟨fam, fun i x => hfam ⟨i,x⟩⟩

end Refute2003.HashCounting

namespace Refute2003.Collisions
open scoped BigOperators
open Function
noncomputable section

def iso {n M : ℕ} (f : Fin n → Fin M) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∀ j, f j = f i → j = i)

def prev {n M : ℕ} (f : Fin n → Fin M) (i : Fin n) : Prop :=
  ∃ j, j < i ∧ f j = f i

def many {n M : ℕ} (f : Fin n → Fin M) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (prev f)

def bad {n M : ℕ} (f : Fin n → Fin M) : Bool :=
  decide (2*(iso f).card < n)

theorem not_iso_of_prev {n M : ℕ} (f : Fin n → Fin M) {i : Fin n}
    (hi : i ∈ many f) : i ∉ iso f := by
  classical
  intro hI
  obtain ⟨j,hji,hf⟩ := (Finset.mem_filter.mp hi).2
  have he := (Finset.mem_filter.mp hI).2 j hf
  exact (ne_of_lt hji) he

theorem many_of_few_iso {n M : ℕ} (f : Fin n → Fin M)
    (hb : bad f = true) : (n+3)/4 ≤ (many f).card := by
  classical
  let U := (Finset.univ : Finset (Fin n)) \ iso f
  let H := U \ many f
  have hU : U.card+(iso f).card = n := by
    simpa [U] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (iso f))
  have hM : many f ⊆ U := fun i hi =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, not_iso_of_prev f hi⟩
  have hH : H.card+(many f).card = U.card := Finset.card_sdiff_add_card_eq_card hM
  have hB : 2*(iso f).card < n := by simpa [bad] using hb
  have chooseLater : ∀ a : ↥H, ∃ j : ↥(many f), f a = f j := by
    intro a
    have hu := (Finset.mem_sdiff.mp a.property).1
    have hn := (Finset.mem_sdiff.mp a.property).2
    have hi := (Finset.mem_sdiff.mp hu).2
    have hep : ∃ j, f j = f a ∧ j ≠ a.val := by
      by_contra! he
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
    obtain ⟨j,hj,hej⟩ := hep
    have hlt : a.val < j := by
      rcases lt_or_gt_of_ne hej with h | h
      · exact False.elim (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,h,hj⟩))
      · exact h
    exact ⟨⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.val,hlt,hj.symm⟩⟩,
      hj.symm⟩
  choose later hlater using chooseLater
  have hinj : Injective later := by
    intro a b hab
    apply Subtype.ext
    by_contra ne
    have hsame : f a = f b := by rw [hlater a, hlater b, hab]
    rcases lt_or_gt_of_ne ne with h | h
    · exact (Finset.mem_sdiff.mp b.property).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.val,h,hsame⟩)
    · exact (Finset.mem_sdiff.mp a.property).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.val,h,hsame.symm⟩)
  have hle : H.card ≤ (many f).card := by
    simpa using Fintype.card_le_of_injective later hinj
  omega

abbrev Code (n r M : ℕ) :=
  Σ A : ↥((Finset.univ : Finset (Fin n)).powersetCard r),
    (↥A.val → Fin n) × ({i : Fin n // i ∉ A.val} → Fin M)

def Fits {n r M : ℕ} (c : Code n r M) (f : Fin n → Fin M) : Prop :=
  (∀ i : ↥c.1.val, c.2.1 i < i.val ∧ f (c.2.1 i) = f i) ∧
    ∀ i : {j : Fin n // j ∉ c.1.val}, c.2.2 i = f i

theorem fits_unique {n r M : ℕ} {c : Code n r M} {f g : Fin n → Fin M}
    (hf : Fits c f) (hg : Fits c g) : f = g := by
  classical
  funext i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    by_cases hi : i ∈ c.1.val
    · let j := c.2.1 ⟨i,hi⟩
      have hj : j < i := (hf.1 ⟨i,hi⟩).1
      exact (hf.1 ⟨i,hi⟩).2.symm.trans ((ih j hj).trans (hg.1 ⟨i,hi⟩).2)
    · exact (hf.2 ⟨i,hi⟩).symm.trans (hg.2 ⟨i,hi⟩)

theorem fits_of_bad {n M : ℕ} {f : Fin n → Fin M} (hb : bad f = true) :
    ∃ c : Code n ((n+3)/4) M, Fits c f := by
  classical
  obtain ⟨A,hA,hAc⟩ := Finset.exists_subset_card_eq (many_of_few_iso f hb)
  have hp : ∀ i : ↥A, ∃ j, j < i.val ∧ f j = f i := fun i =>
    (Finset.mem_filter.mp (hA i.property)).2
  choose prevIndex hpIndex using hp
  let A' : ↥((Finset.univ : Finset (Fin n)).powersetCard ((n+3)/4)) :=
    ⟨A, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hAc⟩⟩
  exact ⟨⟨A',prevIndex,fun i => f i⟩, hpIndex, fun _ => rfl⟩

theorem code_card_le (n r M : ℕ) :
    Fintype.card (Code n r M) ≤ 2^n*(n^r * M^(n-r)) := by
  classical
  let U : Finset (Fin n) := Finset.univ
  have heq : Fintype.card (Code n r M) = (U.powersetCard r).card*(n^r*M^(n-r)) := by
    rw [Fintype.card_sigma]
    calc
      _ = ∑ _A : ↥(U.powersetCard r), n^r*M^(n-r) := by
        apply Finset.sum_congr rfl
        intro A hA
        have hAr : A.val.card = r := (Finset.mem_powersetCard.mp A.property).2
        have hs : Fintype.card {i : Fin n // i ∉ A.val} = n-r := by
          rw [Fintype.card_subtype_compl, Fintype.card_coe, hAr, Fintype.card_fin]
        simp [Fintype.card_prod, Fintype.card_fun, hAr, hs]
      _ = _ := by simp
  have hsub : U.powersetCard r ⊆ U.powerset := by
    intro A hA
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hA).1
  rw [heq]
  exact Nat.mul_le_mul_right _ (by
    simpa [U] using Finset.card_le_card hsub)

theorem bad_vec_card (n M : ℕ) :
    Fintype.card {f : Fin n → Fin M // bad f = true} ≤
      2^n*(n^((n+3)/4)*M^(n-(n+3)/4)) := by
  classical
  have hx : ∀ f : {f : Fin n → Fin M // bad f = true}, ∃ c : Code n ((n+3)/4) M,
      Fits c f.val := fun f => fits_of_bad f.property
  choose code hcode using hx
  have hinj : Injective code := by
    intro a b he
    apply Subtype.ext
    have hb := hcode b
    rw [← he] at hb
    exact fits_unique (hcode a) hb
  exact (Fintype.card_le_of_injective code hinj).trans (code_card_le n ((n+3)/4) M)

theorem bad_vec_scaled (n d : ℕ) (hnd : n ≤ d) :
    2^n*Fintype.card {f : Fin n → Fin (512*d) // bad f = true} ≤ (512*d)^n := by
  let r := (n+3)/4
  have hR : r ≤ n := by dsimp [r]; omega
  have hExp : n+n ≤ 9*r := by dsimp [r]; omega
  have h2 : 2^n*2^n ≤ 512^r := by
    rw [← pow_add]
    change 2^(n+n) ≤ (2^9)^r
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) hExp
  calc
    _ ≤ 2^n*(2^n*(n^r*(512*d)^(n-r))) := Nat.mul_le_mul_left _ (bad_vec_card n (512*d))
    _ = (2^n*2^n)*n^r*(512*d)^(n-r) := by ring
    _ ≤ 512^r*d^r*(512*d)^(n-r) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul h2 (Nat.pow_le_pow_left hnd _))
    _ = _ := by rw [← mul_pow, ← pow_add, Nat.add_sub_of_le hR]

end

end Refute2003.Collisions
open scoped BigOperators
open Polynomial
namespace Refute2003.PolyHash

noncomputable section
variable {K : Type*} [Field K]

def poly {d : ℕ} (c : Fin d → K) : Polynomial K :=
  ∑ j : Fin d, Polynomial.monomial j.val (c j)

theorem coeff_lt {d j : ℕ} (c : Fin d → K) (hj : j < d) :
    (poly c).coeff j = c ⟨j,hj⟩ := by
  classical
  rw [poly, Polynomial.finsetSum_coeff]
  calc
    _ = (Polynomial.monomial j (c ⟨j,hj⟩)).coeff j := by
      apply Finset.sum_eq_single (⟨j,hj⟩ : Fin d)
      · intro i hi hin
        have hval : i.val ≠ j := fun h => hin (Fin.ext h)
        simp [Polynomial.coeff_monomial, Ne.symm hval]
      · simp
    _ = _ := by simp

theorem coeff_ge {d j : ℕ} (c : Fin d → K) (hj : d ≤ j) :
    (poly c).coeff j = 0 := by
  classical
  rw [poly, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  have hval : i.val ≠ j := ne_of_lt (i.isLt.trans_le hj)
  simp [Polynomial.coeff_monomial, Ne.symm hval]

theorem poly_eval {d : ℕ} (c : Fin d → K) (x : K) :
    (poly c).eval x = ∑ j : Fin d, c j*x^j.val := by
  classical
  simp [poly, Polynomial.eval_finsetSum]

theorem coeff_eq_from_evals_tail {d : ℕ} (S : Finset K)
    (c c' : Fin d → K)
    (hEval : ∀ x ∈ S, (poly c).eval x = (poly c').eval x)
    (hTail : ∀ j : Fin d, S.card ≤ j.val → c j = c' j) :
    c = c' := by
  have hdegree : (poly c - poly c').degree < ↑S.card := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro j hj
    rw [Polynomial.coeff_sub]
    by_cases h : j < d
    · rw [coeff_lt c h, coeff_lt c' h, hTail ⟨j,h⟩ hj, sub_self]
    · rw [coeff_ge c (Nat.le_of_not_gt h), coeff_ge c' (Nat.le_of_not_gt h), sub_self]
  have hz : poly c - poly c' = 0 := by
    classical
    by_contra hzero
    have hsub : S ⊆ (poly c - poly c').roots.toFinset := by
      intro x hx
      apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots hzero).mpr
      change (poly c - poly c').eval x = 0
      simp only [Polynomial.eval_sub, hEval x hx, sub_self]
    have hcard : S.card ≤ (poly c - poly c').roots.card :=
      (Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)
    have hcast : (S.card : WithBot ℕ) ≤ ((poly c - poly c').roots.card : WithBot ℕ) :=
      WithBot.coe_le_coe.mpr hcard
    exact (not_lt_of_ge (hcast.trans (Polynomial.card_roots hzero))) hdegree
  have hp : poly c = poly c' := sub_eq_zero.mp hz
  funext j
  have hco := congrArg (fun f : Polynomial K => f.coeff j.val) hp
  simpa [coeff_lt c j.isLt, coeff_lt c' j.isLt] using hco

theorem horner_reverse {d : ℕ} (c : Fin d → K) (x : K) :
    (((List.finRange d).reverse.map c).foldl (fun a b => a*x+b) 0) = (poly c).eval x := by
  rw [poly_eval]
  induction d with
  | zero => simp
  | succ d ih =>
    rw [List.finRange_succ, List.reverse_cons, List.map_append, List.map_singleton,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [← List.map_reverse, List.map_map]
    rw [ih (c ∘ Fin.succ), Fin.sum_univ_succ]
    simp [Function.comp_def, pow_succ, Finset.sum_mul, mul_assoc, add_comm]

def tailEquiv (k d : ℕ) (hkd : k ≤ d) :
    { j : Fin d // k ≤ j.val } ≃ Fin (d-k) where
  toFun j := ⟨j.val.val-k,by have := j.val.isLt; have := j.property; omega⟩
  invFun i := ⟨⟨k+i.val,by have := i.isLt; omega⟩,by change k ≤ k+i.val; omega⟩
  left_inv := by intro j; apply Subtype.ext; apply Fin.ext; have := j.property; dsimp; omega
  right_inv := by intro i; apply Fin.ext; dsimp; omega

variable [Fintype K]

def bucketVec {d M : ℕ} {Rem : Type*} (ρ : K ≃ Fin M × Rem) (S : Finset K)
    (c : Fin d → K) : Fin S.card → Fin M :=
  fun i => (ρ ((poly c).eval ((S.equivFin).symm i).val)).1

theorem bad_seed_scaled {d : ℕ} {Rem : Type*} [Fintype Rem]
    (ρ : K ≃ Fin (512*d) × Rem) (S : Finset K) (hs : S.card ≤ d) :
    2^S.card * Fintype.card
        {c : Fin d → K // Refute2003.Collisions.bad (bucketVec ρ S c) = true} ≤
      (Fintype.card K)^d := by
  classical
  let V := {f : Fin S.card → Fin (512*d) // Refute2003.Collisions.bad f = true}
  let Tail := { j : Fin d // S.card ≤ j.val }
  let Cod := V × (Fin S.card → Rem) × (Tail → K)
  let Dom := {c : Fin d → K // Refute2003.Collisions.bad (bucketVec ρ S c) = true}
  let enc : Dom → Cod := fun c =>
    (⟨bucketVec ρ S c.val, c.property⟩,
       fun i => (ρ ((poly c.val).eval ((S.equivFin).symm i).val)).2,
       fun j => c.val j.val)
  have hinj : Function.Injective enc := by
    intro c c' hEq
    apply Subtype.ext
    apply coeff_eq_from_evals_tail S
    · intro a ha
      let i := S.equivFin ⟨a,ha⟩
      apply ρ.injective
      apply Prod.ext
      · have ht := congrArg (fun z : Cod => z.1.val i) hEq
        simpa [enc, bucketVec, i] using ht
      · have ht := congrArg (fun z : Cod => z.2.1 i) hEq
        simpa [enc, i] using ht
    · intro j hj
      exact congrArg (fun z : Cod => z.2.2 ⟨j,hj⟩) hEq
  have ht : Fintype.card Tail = d-S.card := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (tailEquiv S.card d hs)
  have hsize : Fintype.card Dom ≤ Fintype.card V *
       (Fintype.card Rem)^S.card * (Fintype.card K)^(d-S.card) := by
    simpa [Cod, Fintype.card_prod, Fintype.card_fun, ht, Nat.mul_assoc]
      using Fintype.card_le_of_injective enc hinj
  have hk : Fintype.card K = (512*d)*(Fintype.card Rem) := by
    simpa [Fintype.card_prod] using Fintype.card_congr ρ
  calc
    _ ≤ 2^S.card*(Fintype.card V*(Fintype.card Rem)^S.card*(Fintype.card K)^(d-S.card)) :=
      Nat.mul_le_mul_left _ hsize
    _ = (2^S.card*Fintype.card V)*(Fintype.card Rem)^S.card*(Fintype.card K)^(d-S.card) := by ring
    _ ≤ (512*d)^S.card*(Fintype.card Rem)^S.card*(Fintype.card K)^(d-S.card) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Refute2003.Collisions.bad_vec_scaled S.card d hs))
    _ = _ := by rw [← mul_pow, ← hk, ← pow_add, Nat.add_sub_of_le hs]

def splitWordEquiv (w m : ℕ) (hm : m ≤ w) :
    (Fin w → Bool) ≃ (Fin m → Bool) × (Fin (w-m) → Bool) where
  toFun f := (fun i => f (i.castLE hm), fun j => f ⟨m+j.val,by have := j.isLt; omega⟩)
  invFun z := fun i =>
    if hi : i.val < m then z.1 ⟨i.val,hi⟩ else z.2 ⟨i.val-m,by have := i.isLt; omega⟩
  left_inv := by
    intro f
    funext i
    dsimp
    split
    · congr
    · congr 1
      apply Fin.ext
      dsimp
      omega
  right_inv := by
    intro z
    apply Prod.ext
    · funext i
      dsimp
      rw [dif_pos i.isLt]
    · funext j
      dsimp
      rw [dif_neg (show ¬ m+j.val < m by omega)]
      apply congrArg z.2
      apply Fin.ext
      dsimp
      omega

def bitsFin (m : ℕ) : (Fin m → Bool) ≃ Fin (2^m) :=
  Fintype.equivFinOfCardEq (by simp [Fintype.card_fun])

def bucketEquiv {w e : ℕ} (h : e+9 ≤ w) (β : K ≃ (Fin w → Bool)) :
    K ≃ Fin (512*2^e) × (Fin (w-(e+9)) → Bool) :=
  β.trans ((splitWordEquiv w (e+9) h).trans
    (Equiv.prodCongr ((bitsFin (e+9)).trans (finCongr (by rw [pow_add]; norm_num [Nat.mul_comm])))
      (Equiv.refl _)))

def isolated {M : ℕ} (S : Finset K) (f : K → Fin M) : Finset K := by
  classical
  exact S.filter (fun a => ∀ b ∈ S, f b = f a → b = a)

theorem isoVec_eq {d M : ℕ} {Rem : Type*} (ρ : K ≃ Fin M × Rem)
    (S : Finset K) (c : Fin d → K) :
    (Refute2003.Collisions.iso (bucketVec ρ S c)).card =
      (isolated S (fun a => (ρ ((poly c).eval a)).1)).card := by
  classical
  let E : Fin S.card ↪ K := ⟨fun i => ((S.equivFin).symm i).val,
    fun _ _ h => (S.equivFin).symm.injective (Subtype.ext h)⟩
  have hm : (Refute2003.Collisions.iso (bucketVec ρ S c)).map E =
      isolated S (fun a => (ρ ((poly c).eval a)).1) := by
    ext a
    constructor
    · intro hh
      obtain ⟨i,hi,hea⟩ := Finset.mem_map.mp hh
      have ha : a ∈ S := hea ▸ ((S.equivFin).symm i).property
      apply Finset.mem_filter.mpr
      refine ⟨ha, ?_⟩
      intro b hb heB
      let j := (S.equivFin) ⟨b,hb⟩
      have hea' : ((S.equivFin).symm i).val = a := hea
      have hij := (Finset.mem_filter.mp hi).2 j (by simpa [bucketVec, j, hea'] using heB)
      have heb : E j = b := by
        change ((S.equivFin).symm j).val = b
        simp [j]
      calc
        b = E j := heb.symm
        _ = E i := congrArg E hij
        _ = a := hea
    · intro hh
      have ha := (Finset.mem_filter.mp hh).1
      let i := S.equivFin ⟨a,ha⟩
      have heA : E i = a := by
        change ((S.equivFin).symm i).val = a
        simp [i]
      refine Finset.mem_map.mpr ⟨i, ?_, heA⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro j hj
      have he : E j = a :=
        (Finset.mem_filter.mp hh).2 (E j) ((S.equivFin).symm j).property (by
          change (ρ ((poly c).eval ((S.equivFin).symm j).val)).1 = _
          simpa [bucketVec,i] using hj)
      exact E.injective (he.trans heA.symm)
  exact (Finset.card_map E).symm.trans (congrArg Finset.card hm)

theorem exists_polynomial_family {d : ℕ} {Rem : Type*} [Fintype Rem]
    (ρ : K ≃ Fin (512*d) × Rem) (L B : ℕ)
    (hK : Fintype.card K ≤ 2^L) (hd : d < 2^B) :
    ∃ fam : Fin (L+B) → (Fin d → K),
      ∀ S : Finset K, S.Nonempty → S.card ≤ d →
        ∃ i, S.card ≤ 2*(isolated S (fun a => (ρ ((poly (fam i)).eval a)).1)).card := by
  classical
  let Key : Fin d → Type _ := fun j => ↥((Finset.univ : Finset K).powersetCard (j.val+1))
  let w : Fin d → ℕ := fun j => j.val+1
  let Bad : (j : Fin d) → Key j → (Fin d → K) → Bool :=
    fun _ S c => Refute2003.Collisions.bad (bucketVec ρ S.val c)
  have hW : ∀ j, 1 ≤ w j := by intro j; simp [w]
  have hKey : ∀ j, Fintype.card (Key j) ≤ (2^L)^(w j) := by
    intro j
    simp only [Key, w, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ]
    exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hK _)
  have hs : ∀ j S, 2^(w j) *
      Fintype.card (Refute2003.HashCounting.BadChoice (Bad j) S) ≤
        Fintype.card (Fin d → K) := by
    intro j S
    have hcard : S.val.card = w j := (Finset.mem_powersetCard.mp S.property).2
    have hcap : S.val.card ≤ d := by
      rw [hcard]
      exact Nat.succ_le_of_lt j.isLt
    simpa [Bad, Refute2003.HashCounting.BadChoice, hcard, Fintype.card_fun]
      using bad_seed_scaled ρ S.val hcap
  obtain ⟨fam, hfam⟩ := Refute2003.HashCounting.exists_family_weighted Key Bad w L B hW hKey hs
    (by simpa using hd)
  refine ⟨fam, ?_⟩
  intro S hSn hSd
  have hp : 0 < S.card := Finset.card_pos.mpr hSn
  let j : Fin d := ⟨S.card-1, by omega⟩
  have hj : w j = S.card := by dsimp [w,j]; omega
  let S' : Key j := ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hj.symm⟩⟩
  obtain ⟨i,hi⟩ := hfam j S'
  refine ⟨i, ?_⟩
  have hneg : ¬ (2*(Refute2003.Collisions.iso (bucketVec ρ S (fam i))).card < S.card) := by
    simpa [Bad,S',Refute2003.Collisions.bad] using hi
  rw [isoVec_eq] at hneg
  exact Nat.le_of_not_gt hneg

end

end Refute2003.PolyHash

namespace Refute2003.BundleBuild

structure Ops (M : Type → Type) (W : Type) [Monad M] where
  constant : Bool → W
  andGate : W → W → M W
  orGate : W → W → M W

abbrev Ops.const {M : Type → Type} {W : Type} [Monad M] [Inhabited (Ops M W)] : Bool → W :=
  (default : Ops M W).constant

abbrev Ops.land {M : Type → Type} {W : Type} [Monad M] [Inhabited (Ops M W)] : W → W → M W :=
  (default : Ops M W).andGate

abbrev Ops.lor {M : Type → Type} {W : Type} [Monad M] [Inhabited (Ops M W)] : W → W → M W :=
  (default : Ops M W).orGate

abbrev Dual (W : Type) := W × W
abbrev Word (W : Type) (w : Nat) := Fin w → Dual W

def selected {W : Type} (d : Dual W) (v : Bool) : W :=
  if v then d.1 else d.2

structure Cell (W : Type) (w : Nat) where
  present : W
  code : Word W w

abbrev Sketch (W : Type) (r b w : Nat) := Fin r → Fin b → Cell W w

def tabM {M : Type → Type} [Monad M] {A : Type} :
    (n : Nat) → (Fin n → M A) → M (Fin n → A)
  | 0, _ => pure Fin.elim0
  | n+1, f => do
    let hd ← f 0
    let tl ← tabM n (fun i => f i.succ)
    pure (Fin.cases hd tl)

def mapMList {M : Type → Type} [Monad M] {A B : Type}
    (f : A → M B) : List A → M (List B)
  | [] => pure []
  | a :: as => do
    let b ← f a
    let bs ← mapMList f as
    pure (b :: bs)

section Emit
variable {M : Type → Type} {W : Type} [Monad M] [Inhabited (Ops M W)]

def allList (xs : List W) : M W :=
  xs.foldlM Ops.land (Ops.const (M := M) (W := W) true)

def anyList (xs : List W) : M W :=
  xs.foldlM Ops.lor (Ops.const (M := M) (W := W) false)

def reduceF {A : Type} (ops : W → W → M W) (z : W)
    (xs : List A) (f : A → M W) : M W :=
  xs.foldlM (fun s a => do
    let x ← f a
    ops s x) z

def allFin (n : Nat) (f : Fin n → M W) : M W :=
  reduceF Ops.land (Ops.const (M := M) (W := W) true) (List.finRange n) f

def anyFin (n : Nat) (f : Fin n → M W) : M W :=
  reduceF Ops.lor (Ops.const (M := M) (W := W) false) (List.finRange n) f

def dualAnd (a b : Dual W) : M (Dual W) := do
  let p ← Ops.land a.1 b.1
  let n ← Ops.lor a.2 b.2
  pure (p,n)

def dualOr (a b : Dual W) : M (Dual W) := do
  let p ← Ops.lor a.1 b.1
  let n ← Ops.land a.2 b.2
  pure (p,n)

def dualXor (a b : Dual W) : M (Dual W) := do
  let p₁ ← Ops.land a.1 b.2
  let p₂ ← Ops.land a.2 b.1
  let n₁ ← Ops.land a.1 b.1
  let n₂ ← Ops.land a.2 b.2
  let p ← Ops.lor p₁ p₂
  let n ← Ops.lor n₁ n₂
  pure (p,n)

def dualConst (b : Bool) : Dual W :=
  (Ops.const (M := M) (W := W) b, Ops.const (M := M) (W := W) (!b))

def parity (xs : List (Dual W)) : M (Dual W) :=
  xs.foldlM dualXor (dualConst (M := M) (W := W) false)

def sameWord {w : Nat} (a : Word W w) (v : Fin w → Bool) : M W :=
  allFin w (fun j => pure (selected (a j) (v j)))

def addBits {w : Nat} (a b : Word W w) : M (Word W w) :=
  tabM w (fun i => dualXor (a i) (b i))

def mulBits {w : Nat} (constants : Fin w → Fin w → Fin w → Bool)
    (a b : Word W w) : M (Word W w) :=
  tabM w (fun i => do
    let pairs := (List.finRange w).flatMap (fun j => (List.finRange w).map (fun k => (j,k)))
    let chosen := pairs.filter (fun jk => constants i jk.1 jk.2)
    chosen.foldlM (fun acc jk => do
      let prod ← dualAnd (a jk.1) (b jk.2)
      dualXor acc prod) (dualConst (M := M) (W := W) false))

def affineBits {w o : Nat} (matrix : Fin o → Fin w → Bool) (offset : Fin o → Bool)
    (a : Word W w) : M (Word W o) :=
  tabM o (fun j =>
    ((List.finRange w).filter (matrix j)).foldlM
      (fun acc k => dualXor acc (a k)) (dualConst (M := M) (W := W) (offset j)))

def hornerBits {w : Nat} (constants : Fin w → Fin w → Fin w → Bool)
    (coeffs : List (Fin w → Bool)) (a : Word W w) : M (Word W w) :=
  coeffs.foldlM (fun acc c => do
    let p ← mulBits constants acc a
    addBits p (fun j => dualConst (M := M) (W := W) (c j)))
    (fun _ => dualConst (M := M) (W := W) false)

def lift {r b w : Nat} (src : Sketch W r b w) (f : Word W w → M W) : M W :=
  allFin r (fun h =>
    anyFin b (fun c => do
      let cand ← f (src h c).code
      Ops.land (src h c).present cand))

def mkSketch {r b w : Nat}
    (actPred : Fin r → Fin b → M W)
    (bitPred : Fin r → Fin b → Fin w → Bool → M W) : M (Sketch W r b w) :=
  tabM r (fun h => tabM b (fun c => do
    let present ← actPred h c
    let code ← tabM w (fun j => do
      let p ← bitPred h c j true
      let n ← bitPred h c j false
      pure (p,n))
    pure ⟨present, code⟩))

def project {r b w r' b' w' : Nat} (src : Sketch W r b w)
    (map : Word W w → M (Word W w')) (keep : Word W w → M W)
    (matchDest : Fin r' → Fin b' → Word W w' → M W) : M (Sketch W r' b' w') :=
  mkSketch
    (fun h c => lift src (fun x => do
      let k ← keep x
      let y ← map x
      let m ← matchDest h c y
      Ops.land k m))
    (fun h c j v => lift src (fun x => do
      let k ← keep x
      let y ← map x
      let m ← matchDest h c y
      let yes ← Ops.land k m
      Ops.land yes (selected (y j) v)))

structure Layout (M : Type → Type) (W : Type) (q w : Nat) where
  hashes : Nat
  buckets : Nat
  checkCell : Fin hashes → Fin buckets → Word W w → M W
  entries : Fin hashes → Fin buckets → List (Fin q)

def aggregate {q r b w : Nat} (src : Sketch W r b w)
    (layout : Layout M W q w) : M (Sketch W layout.hashes layout.buckets w) :=
  mkSketch
    (fun h c => lift src (layout.checkCell h c))
    (fun h c j v => lift src (fun x => do
      let m ← layout.checkCell h c x
      Ops.land m (selected (x j) v)))

def table {q w : Nat} (layout : Layout M W q w)
    (aggregateWords : Sketch W layout.hashes layout.buckets w)
    (word : Fin q → Fin w → Bool) (X : Fin q → W) :
    M (Fin layout.hashes → Fin layout.buckets → W) :=
  tabM layout.hashes (fun h => tabM layout.buckets (fun c => do
    let yes ← reduceF Ops.lor (Ops.const (M := M) (W := W) false) (layout.entries h c)
      (fun v => do
        let eq ← sameWord (aggregateWords h c).code (word v)
        Ops.land (X v) eq)
    Ops.land (aggregateWords h c).present yes))

def filterWord {q w : Nat} (layout : Layout M W q w)
    (V : Fin layout.hashes → Fin layout.buckets → W) (a : Word W w) : M W :=
  allFin layout.hashes (fun h =>
    anyFin layout.buckets (fun c => do
      let m ← layout.checkCell h c a
      Ops.land m (V h c)))

def step {q r b w : Nat} (src : Sketch W r b w)
    (word : Fin q → Fin w → Bool) (X : Fin q → W) (layout : Layout M W q w)
    (matchOwn : Fin r → Fin b → Word W w → M W) : M (Sketch W r b w) := do
  let agg ← aggregate src layout
  let V ← table layout agg word X
  project src (fun a => pure a) (filterWord layout V) matchOwn

def lookup {q r b w : Nat} (start : Sketch W r b w)
    (word : Fin q → Fin w → Bool) (X : Fin q → W) (layouts : List (Layout M W q w))
    (matchOwn : Fin r → Fin b → Word W w → M W) (h : Fin r) : M W := do
  let result ← layouts.foldlM (fun src layout => step src word X layout matchOwn) start
  anyFin b (fun c => pure (result h c).present)

end Emit
end Refute2003.BundleBuild

namespace Refute2003.BundleBuild

structure Sem (S W : Type) [Inhabited (Ops (StateM S) W)] where
  ext : S → S → Prop
  refl : ∀ s, ext s s
  trans : ∀ {s t u}, ext s t → ext t u → ext s u
  rep : S → W → Prop → Prop
  stabilize : ∀ {s t a p}, ext s t → rep s a p → rep t a p
  congr : ∀ {s a p q}, (p ↔ q) → rep s a p → rep s a q
  konst : ∀ s b, rep s (Ops.const (M := StateM S) (W := W) b) (b = true)
  land : ∀ {s a b p q}, rep s a p → rep s b q →
    let R := ((Ops.land a b : StateM S W).run s)
    ext s R.2 ∧ rep R.2 R.1 (p ∧ q)
  lor : ∀ {s a b p q}, rep s a p → rep s b q →
    let R := ((Ops.lor a b : StateM S W).run s)
    ext s R.2 ∧ rep R.2 R.1 (p ∨ q)

section
variable {S W : Type} [Inhabited (Ops (StateM S) W)] (v : Sem S W)

def Good {A : Type} (s : S) (p : StateM S A) (P : S → A → Prop) : Prop :=
  let R := p.run s
  v.ext s R.2 ∧ P R.2 R.1

theorem Good.ret {A : Type} (s : S) (a : A) (P : S → A → Prop) (h : P s a) :
    Good v s (pure a) P :=
  ⟨v.refl s, h⟩

theorem Good.bind {A B : Type} {s : S} {p : StateM S A} {f : A → StateM S B}
    {P : S → A → Prop} {Q : S → B → Prop} (h : Good v s p P)
    (hf : ∀ t a, v.ext s t → P t a → Good v t (f a) Q) :
    Good v s (p >>= f) Q := by
  have ht := hf (p.run s).2 (p.run s).1 h.1 h.2
  exact ⟨v.trans h.1 ht.1, ht.2⟩

theorem Good.post {A : Type} {s : S} {p : StateM S A} {P Q : S → A → Prop}
    (h : Good v s p P) (imp : ∀ t a, P t a → Q t a) : Good v s p Q :=
  ⟨h.1, imp _ _ h.2⟩

theorem Good.postExt {A : Type} {s : S} {p : StateM S A} {P Q : S → A → Prop}
    (h : Good v s p P) (imp : ∀ t a, v.ext s t → P t a → Q t a) : Good v s p Q :=
  ⟨h.1, imp _ _ h.1 h.2⟩

theorem const_true (s : S) : v.rep s (Ops.const (M := StateM S) (W := W) true) True :=
  v.congr (by simp) (v.konst s true)

theorem const_false (s : S) : v.rep s (Ops.const (M := StateM S) (W := W) false) False :=
  v.congr (by simp) (v.konst s false)

theorem land_good {s : S} {a b : W} {p q : Prop} (ha : v.rep s a p) (hb : v.rep s b q) :
    Good v s ((Ops.land a b) : StateM S W) (fun t c => v.rep t c (p ∧ q)) :=
  v.land ha hb

theorem lor_good {s : S} {a b : W} {p q : Prop} (ha : v.rep s a p) (hb : v.rep s b q) :
    Good v s ((Ops.lor a b) : StateM S W) (fun t c => v.rep t c (p ∨ q)) :=
  v.lor ha hb

theorem tab_correct {A : Type} (n : Nat) {s : S} (f : Fin n → StateM S A)
    (P : Fin n → S → A → Prop)
    (hstable : ∀ i t u a, v.ext t u → P i t a → P i u a)
    (hf : ∀ i t, v.ext s t → Good v t (f i) (P i)) :
    Good v s (tabM n f) (fun t out => ∀ i, P i t (out i)) := by
  induction n generalizing s with
  | zero => exact Good.ret v s _ _ (fun i => Fin.elim0 i)
  | succ n ih =>
    change Good v s (f 0 >>= fun hd => tabM n (fun i => f i.succ) >>= fun tl =>
      (pure (Fin.cases (motive := fun _ => A) hd tl) : StateM S (Fin (n+1) → A))) _
    apply Good.bind v (hf 0 s (v.refl s))
    intro t hd hst hhd
    have ht := ih (s := t) (fun i => f i.succ) (fun i => P i.succ)
      (fun i => hstable i.succ) (fun i u htu => hf i.succ u (v.trans hst htu))
    apply Good.bind v ht
    intro u tl htu htl
    apply Good.ret
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hstable 0 t u hd htu hhd
    · simpa using htl j

theorem reduce_correct {A : Type} {s : S} (xs : List A)
    (f : A → StateM S W) (p : A → Prop)
    (op : W → W → StateM S W) (combine : Prop → Prop → Prop)
    (ok : ∀ {t a b I J}, v.rep t a I → v.rep t b J →
      Good v t (op a b) (fun u c => v.rep u c (combine I J)))
    (hh : ∀ a ∈ xs, ∀ t, v.ext s t → Good v t (f a) (fun u w => v.rep u w (p a)))
    (z : W) (e : Prop) (hz : v.rep s z e) :
    Good v s (reduceF op z xs f) (fun t out =>
      v.rep t out (xs.foldl (fun acc a => combine acc (p a)) e)) := by
  induction xs generalizing s z e with
  | nil => exact Good.ret v s z _ hz
  | cons a as ih =>
    change Good v s (f a >>= fun g => op z g >>= fun first => reduceF op first as f) _
    apply Good.bind v (hh a (by simp) s (v.refl s))
    intro t g hst hg
    apply Good.bind v (ok (v.stabilize hst hz) hg)
    intro u first htu hu
    apply ih
    · intro i hi tt hh'
      exact hh i (by simp [hi]) tt (v.trans (v.trans hst htu) hh')
    · exact hu

theorem fold_and_iff {A : Type} (xs : List A) (p : A → Prop) (e : Prop) :
    xs.foldl (fun acc a => acc ∧ p a) e ↔ e ∧ ∀ a ∈ xs, p a := by
  induction xs generalizing e with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, ih]
    constructor
    · rintro ⟨⟨he, hp⟩, hs⟩
      exact ⟨he, fun u hu => (List.mem_cons.mp hu).elim (fun hu => hu.symm ▸ hp) (hs u)⟩
    · rintro ⟨he, hp⟩
      exact ⟨⟨he, hp a (by simp)⟩, fun u hu => hp u (by simp [hu])⟩

theorem fold_or_iff {A : Type} (xs : List A) (p : A → Prop) (e : Prop) :
    xs.foldl (fun acc a => acc ∨ p a) e ↔ e ∨ ∃ a ∈ xs, p a := by
  induction xs generalizing e with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, ih]
    constructor
    · intro h
      rcases h with h | ⟨u, hu, hp⟩
      · exact h.elim Or.inl (fun hp => Or.inr ⟨a, by simp, hp⟩)
      · exact Or.inr ⟨u, by simp [hu], hp⟩
    · intro h
      rcases h with he | ⟨u, hu, hp⟩
      · exact Or.inl (Or.inl he)
      · rcases List.mem_cons.mp hu with he | hh
        · exact Or.inl (Or.inr (he ▸ hp))
        · exact Or.inr ⟨u, hh, hp⟩

theorem all_correct {s : S} (n : Nat) (f : Fin n → StateM S W) (p : Fin n → Prop)
    (h : ∀ a t, v.ext s t → Good v t (f a) (fun u w => v.rep u w (p a))) :
    Good v s (allFin n f) (fun t out => v.rep t out (∀ a, p a)) := by
  apply Good.post v
    (reduce_correct v (List.finRange n) f p Ops.land And
      (fun a b => land_good v a b) (fun a _ t ht => h a t ht) _ True (const_true v s))
  intro t out rr
  apply v.congr _ rr
  simpa using fold_and_iff (List.finRange n) p True

theorem any_correct {s : S} (n : Nat) (f : Fin n → StateM S W) (p : Fin n → Prop)
    (h : ∀ a t, v.ext s t → Good v t (f a) (fun u w => v.rep u w (p a))) :
    Good v s (anyFin n f) (fun t out => v.rep t out (∃ a, p a)) := by
  apply Good.post v
    (reduce_correct v (List.finRange n) f p Ops.lor Or
      (fun a b => lor_good v a b) (fun a _ t ht => h a t ht) _ False (const_false v s))
  intro t out rr
  apply v.congr _ rr
  simpa using fold_or_iff (List.finRange n) p False

def WordRep {w : Nat} (s : S) (word : Word W w) (r : Fin w → Bool → Prop) :=
  ∀ j z, v.rep s (selected (word j) z) (r j z)

theorem WordRep.extend {w : Nat} {s t : S} {word : Word W w} {r}
    (h : WordRep v s word r) (st : v.ext s t) : WordRep v t word r :=
  fun i b => v.stabilize st (h i b)

def SketchRep {r b w : Nat} (s : S) (sk : Sketch W r b w)
    (p : Fin r → Fin b → Prop) (R : Fin r → Fin b → Fin w → Bool → Prop) :=
  ∀ h c, v.rep s (sk h c).present (p h c) ∧ WordRep v s (sk h c).code (R h c)

theorem SketchRep.extend {r b w : Nat} {s t : S} {sk : Sketch W r b w} {p R}
    (h : SketchRep v s sk p R) (st : v.ext s t) : SketchRep v t sk p R :=
  fun i j => ⟨v.stabilize st (h i j).1, WordRep.extend v (h i j).2 st⟩

theorem lift_correct {r b w : Nat} {s : S} (sk : Sketch W r b w)
    (act : Fin r → Fin b → Prop) (R : Fin r → Fin b → Fin w → Bool → Prop)
    (f : Word W w → StateM S W) (pred : (Fin w → Bool → Prop) → Prop)
    (hsk : SketchRep v s sk act R)
    (hf : ∀ t (code : Word W w) rs, v.ext s t → WordRep v t code rs →
      Good v t (f code) (fun u a => v.rep u a (pred rs))) :
    Good v s (lift sk f) (fun t o => v.rep t o (∀ h, ∃ c, act h c ∧ pred (R h c))) := by
  apply all_correct v
  intro h t hst
  apply any_correct v
  intro c u htu
  have hsu := v.trans hst htu
  have hr := SketchRep.extend v hsk hsu h c
  apply Good.bind v (hf u _ _ hsu hr.2)
  intro a val hua hv
  exact land_good v (v.stabilize hua hr.1) hv

theorem mkSketch_correct {r b w : Nat} {s : S}
    (a : Fin r → Fin b → StateM S W)
    (bits : Fin r → Fin b → Fin w → Bool → StateM S W)
    (act : Fin r → Fin b → Prop) (R : Fin r → Fin b → Fin w → Bool → Prop)
    (ha : ∀ h c t, v.ext s t → Good v t (a h c) (fun u x => v.rep u x (act h c)))
    (hb : ∀ h c j vbit t, v.ext s t →
      Good v t (bits h c j vbit) (fun u x => v.rep u x (R h c j vbit))) :
    Good v s (mkSketch a bits) (fun t sk => SketchRep v t sk act R) := by
  unfold mkSketch
  unfold SketchRep
  refine tab_correct v r _ (fun h t (block : Fin b → Cell W w) => ∀ c,
    v.rep t (block c).present (act h c) ∧ WordRep v t (block c).code (R h c)) ?_ ?_
  · intro i t u block htu hb'
    intro j
    exact ⟨v.stabilize htu (hb' j).1, WordRep.extend v (hb' j).2 htu⟩
  · intro h s' hss'
    refine tab_correct v b _ (fun c t (cell : Cell W w) =>
      v.rep t cell.present (act h c) ∧ WordRep v t cell.code (R h c)) ?_ ?_
    · intro j t u cell htu hj
      exact ⟨v.stabilize htu hj.1, WordRep.extend v hj.2 htu⟩
    · intro c t hs't
      have hst := v.trans hss' hs't
      apply Good.bind v (ha h c t hst)
      intro u present htu hPresent
      have hsu := v.trans hst htu
      have hc : Good v u (tabM w (fun j => do
          let positive ← bits h c j true
          let negative ← bits h c j false
          pure (positive, negative))) (fun t' out => WordRep v t' out (R h c)) := by
        refine tab_correct v w _ (fun j m (d : Dual W) => ∀ z, v.rep m (selected d z) (R h c j z)) ?_ ?_
        · intro j m n d hmn hd z
          exact v.stabilize hmn (hd z)
        · intro j m hum
          have hsm := v.trans hsu hum
          apply Good.bind v (hb h c j true m hsm)
          intro m' positive hmm' hPos
          have hsm' := v.trans hsm hmm'
          apply Good.bind v (hb h c j false m' hsm')
          intro m'' negative hm'm'' hNeg
          apply Good.ret
          intro z
          cases z with
          | false => exact hNeg
          | true => exact v.stabilize hm'm'' hPos
      apply Good.bind v hc
      intro t' word hut' hWord
      exact Good.ret v t' (Cell.mk present word) (fun tt cell =>
        v.rep tt cell.present (act h c) ∧ WordRep v tt cell.code (R h c))
          (And.intro (v.stabilize hut' hPresent) hWord)

end
end Refute2003.BundleBuild

namespace Refute2003.Bundle

abbrev Rails (width : Nat) := Fin width → Bool → Prop

def RailsLE {w : Nat} (a b : Rails w) : Prop :=
  ∀ j z, a j z → b j z

def singletonRails {α : Type*} {w : Nat} (word : α → Fin w → Bool) (a : α) : Rails w :=
  fun j z => word a j = z

def active {α β γ : Type*} (hash : γ → α → β) (A : Finset α) (h : γ) (b : β) : Prop :=
  ∃ a ∈ A, hash h a = b

def rails {α β γ : Type*} {w : Nat} (word : α → Fin w → Bool)
    (hash : γ → α → β) (A : Finset α) (h : γ) (b : β) : Rails w :=
  fun j z => ∃ a ∈ A, hash h a = b ∧ word a j = z

def sketchLift {α β γ : Type*} {w : Nat} (word : α → Fin w → Bool)
    (hash : γ → α → β) (A : Finset α) (ev : Rails w → Prop) : Prop :=
  ∀ h, ∃ b, active hash A h b ∧ ev (rails word hash A h b)

theorem singleton_le_rails {α β γ : Type*} {w : Nat} (word : α → Fin w → Bool)
    (hash : γ → α → β) {A : Finset α} {a : α} (ha : a ∈ A) (h : γ) :
    RailsLE (singletonRails word a) (rails word hash A h (hash h a)) := by
  intro j z hz
  exact ⟨a, ha, rfl, hz⟩

theorem rails_of_unique {α β γ : Type*} {w : Nat} (word : α → Fin w → Bool)
    (hash : γ → α → β) {A : Finset α} {a : α} (ha : a ∈ A) (h : γ) (b : β)
    (hab : hash h a = b) (hu : ∀ a' ∈ A, hash h a' = b → a' = a) :
    rails word hash A h b = singletonRails word a := by
  funext j z
  apply propext
  constructor
  · rintro ⟨a', ha', ha'b, hz⟩
    have he := hu a' ha' ha'b
    cases he
    exact hz
  · intro hz
    exact ⟨a, ha, hab, hz⟩

theorem sketchLift_iff {α β γ : Type*} {w : Nat} (word : α → Fin w → Bool)
    (hash : γ → α → β) (A : Finset α) (ev : Rails w → Prop) (pred : α → Prop)
    (mono : ∀ {r s}, RailsLE r s → ev r → ev s)
    (coherent : ∀ a, ev (singletonRails word a) ↔ pred a)
    (perfect : ∃ h, ∀ a ∈ A, ∀ a' ∈ A, hash h a' = hash h a → a' = a) :
    sketchLift word hash A ev ↔ ∃ a ∈ A, pred a := by
  constructor
  · intro L
    rcases perfect with ⟨h, hh⟩
    rcases L h with ⟨b, ⟨a, ha, hab⟩, hb⟩
    have he : rails word hash A h b = singletonRails word a :=
      rails_of_unique word hash ha h b hab (fun a' ha' he => hh a ha a' ha' (he.trans hab.symm))
    rw [he] at hb
    exact ⟨a, ha, (coherent a).mp hb⟩
  · rintro ⟨a, ha, hp⟩ h
    refine ⟨hash h a, ⟨a, ha, rfl⟩, ?_⟩
    exact mono (singleton_le_rails word hash ha h) ((coherent a).mpr hp)

noncomputable def transfer {α δ : Type*} [DecidableEq δ]
    (A : Finset α) (pred : α → Prop) (g : α → δ) : Finset δ := by
  classical
  exact (A.filter pred).image g

theorem mem_transfer {α δ : Type*} [DecidableEq δ] (A : Finset α)
    (pred : α → Prop) (g : α → δ) (b : δ) :
    b ∈ transfer A pred g ↔ ∃ a ∈ A, pred a ∧ g a = b := by
  classical
  simp [transfer, Finset.mem_image, Finset.mem_filter, and_assoc]

theorem transfer_active {α δ β γ : Type*} [DecidableEq δ]
    (A : Finset α) (pred : α → Prop) (g : α → δ)
    (hash : γ → δ → β) (h : γ) (b : β) :
    active hash (transfer A pred g) h b ↔
      ∃ a ∈ A, pred a ∧ hash h (g a) = b := by
  constructor
  · rintro ⟨u, hu, huc⟩
    rcases (mem_transfer A pred g u).mp hu with ⟨a, ha, hP, rfl⟩
    exact ⟨a, ha, hP, huc⟩
  · rintro ⟨a, ha, hP, hab⟩
    exact ⟨g a, (mem_transfer A pred g (g a)).mpr ⟨a, ha, hP, rfl⟩, hab⟩

theorem transfer_rails {α δ β γ : Type*} [DecidableEq δ] {w : Nat}
    (A : Finset α) (pred : α → Prop) (g : α → δ)
    (word : δ → Fin w → Bool) (hash : γ → δ → β) (h : γ) (b : β) (j : Fin w) (z : Bool) :
    rails word hash (transfer A pred g) h b j z ↔
      ∃ a ∈ A, pred a ∧ hash h (g a) = b ∧ word (g a) j = z := by
  constructor
  · rintro ⟨u, hu, huc, huz⟩
    rcases (mem_transfer A pred g u).mp hu with ⟨a, ha, hP, rfl⟩
    exact ⟨a, ha, hP, huc, huz⟩
  · rintro ⟨a, ha, hP, hab, haz⟩
    exact ⟨g a, (mem_transfer A pred g (g a)).mpr ⟨a, ha, hP, rfl⟩, hab, haz⟩

theorem transfer_card {α δ : Type*} [DecidableEq δ] (A : Finset α)
    (pred : α → Prop) (g : α → δ) : (transfer A pred g).card ≤ A.card := by
  classical
  unfold transfer
  exact (Finset.card_image_le).trans (Finset.card_filter_le _ _)

section Table

variable {α β γ : Type*} {w : Nat}
variable (word : α → Fin w → Bool) (hash : γ → α → β) (X : α → Prop)

def bucketHit (A : Finset α) (h : γ) (b : β) : Prop :=
  active hash A h b ∧
    ∃ v, hash h v = b ∧ X v ∧ ∀ j, rails word hash A h b j (word v j)

def isolated (A : Finset α) (h : γ) (a : α) : Prop :=
  ∀ a' ∈ A, hash h a' = hash h a → a' = a

noncomputable def advance (A : Finset α) : Finset α := by
  classical
  exact A.filter (fun a => ∀ h, bucketHit word hash X A h (hash h a))

theorem mem_advance (A : Finset α) (a : α) :
    a ∈ advance word hash X A ↔ a ∈ A ∧ ∀ h, bucketHit word hash X A h (hash h a) := by
  classical
  simp [advance]

theorem advance_subset (A : Finset α) : advance word hash X A ⊆ A := by
  intro a ha
  exact ((mem_advance word hash X A a).mp ha).1

theorem keeps_hit {A : Finset α} {a : α} (ha : a ∈ A) (hX : X a) :
    a ∈ advance word hash X A := by
  apply (mem_advance word hash X A a).mpr
  exact ⟨ha, fun h => ⟨⟨a, ha, rfl⟩, a, rfl, hX, fun j => ⟨a, ha, rfl, rfl⟩⟩⟩

theorem isolated_bucket_hit_iff {A : Finset α} {a : α} (ha : a ∈ A) {h : γ}
    (inj : Function.Injective word) (hi : isolated hash A h a) :
    bucketHit word hash X A h (hash h a) ↔ X a := by
  constructor
  · rintro ⟨_, v, _, hXv, hbits⟩
    have hword : word a = word v := by
      funext j
      rcases hbits j with ⟨u, hu, huh, hj⟩
      have hu' := hi u hu huh
      cases hu'
      exact hj
    have he := inj hword
    exact he.symm ▸ hXv
  · intro hX
    exact ⟨⟨a, ha, rfl⟩, a, rfl, hX, fun j => ⟨a, ha, rfl, rfl⟩⟩

theorem advance_removes {A I : Finset α} (inj : Function.Injective word)
    (hI : I ⊆ A) (hiso : ∀ a ∈ I, ∃ h, isolated hash A h a)
    (noHit : ∀ a ∈ A, ¬ X a) :
    ∀ a ∈ advance word hash X A, a ∉ I := by
  intro a ha hi
  have aA := hI hi
  obtain ⟨h, hh⟩ := hiso a hi
  have hit := ((mem_advance word hash X A a).mp ha).2 h
  exact noHit a aA ((isolated_bucket_hit_iff word hash X aA inj hh).mp hit)

theorem advance_card_le {A : Finset α} {m : Nat}
    (inj : Function.Injective word) (noHit : ∀ a ∈ A, ¬ X a)
    (hc : A.card ≤ 2*m+1)
    (hiso : m < A.card → ∃ I : Finset α, I ⊆ A ∧ A.card ≤ 2*I.card ∧
      ∀ a ∈ I, ∃ h, isolated hash A h a) :
    (advance word hash X A).card ≤ m := by
  classical
  by_cases small : A.card ≤ m
  · exact (Finset.card_le_card (advance_subset word hash X A)).trans small
  · obtain ⟨I, hI, hhalf, hIiso⟩ := hiso (Nat.lt_of_not_ge small)
    have hs : advance word hash X A ⊆ A \ I := by
      intro a ha
      exact Finset.mem_sdiff.mpr ⟨advance_subset word hash X A ha,
        advance_removes word hash X inj hI hIiso noHit a ha⟩
    have hh := Finset.card_le_card hs
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hI] at hh
    have hIc := Finset.card_le_card hI
    omega

end Table

section Steps
variable {α : Type*} {w : Nat}
variable (word : α → Fin w → Bool) (X : α → Prop)
variable {β γ : Nat → Type*} (maps : (j : Nat) → γ j → α → β j)

def halfThreshold : Nat → Nat
  | 0 => 0
  | n+1 => 2^n

noncomputable def lookupSteps (word : α → Fin w → Bool) (X : α → Prop)
    (maps : (j : Nat) → γ j → α → β j) : Nat → Finset α → Finset α
  | 0, A => advance word (maps 0) X A
  | n+1, A => lookupSteps word X maps n (advance word (maps (n+1)) X A)

theorem keeps_lookup (n : Nat) {A : Finset α} {a : α}
    (ha : a ∈ A) (hX : X a) : a ∈ lookupSteps word X maps n A := by
  induction n generalizing A with
  | zero => exact keeps_hit word (maps 0) X ha hX
  | succ n ih =>
    exact ih (keeps_hit word (maps (n+1)) X ha hX)

theorem lookup_noHit (inj : Function.Injective word)
    (family : ∀ n (A : Finset α), halfThreshold n < A.card → A.card ≤ 2^n →
      ∃ I : Finset α, I ⊆ A ∧ A.card ≤ 2*I.card ∧ ∀ a ∈ I, ∃ h, isolated (maps n) A h a)
    (n : Nat) (A : Finset α) (hc : A.card ≤ 2^n) (noHit : ∀ a ∈ A, ¬ X a) :
    lookupSteps word X maps n A = ∅ := by
  induction n generalizing A with
  | zero =>
    have hh : (advance word (maps 0) X A).card ≤ 0 :=
      advance_card_le word (maps 0) X inj noHit (by simpa using hc) (fun h => family 0 A h hc)
    exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hh)
  | succ n ih =>
    have hc' : A.card ≤ 2*(2^n)+1 := by
      rw [pow_succ] at hc
      omega
    have ha : (advance word (maps (n+1)) X A).card ≤ 2^n :=
      advance_card_le word (maps (n+1)) X inj noHit hc' (fun h => family (n+1) A h hc)
    exact ih _ ha (fun a ha' => noHit a (advance_subset word (maps (n+1)) X A ha'))

theorem lookup_exact (inj : Function.Injective word)
    (family : ∀ n (A : Finset α), halfThreshold n < A.card → A.card ≤ 2^n →
      ∃ I : Finset α, I ⊆ A ∧ A.card ≤ 2*I.card ∧ ∀ a ∈ I, ∃ h, isolated (maps n) A h a)
    (n : Nat) (A : Finset α) (hc : A.card ≤ 2^n) :
    (∃ a, a ∈ lookupSteps word X maps n A) ↔ ∃ a ∈ A, X a := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    by_contra h
    have noHit : ∀ t ∈ A, ¬ X t := fun t ht hX => h ⟨t, ht, hX⟩
    rw [lookup_noHit word X maps inj family n A hc noHit] at ha
    simp at ha
  · rintro ⟨a, ha, hX⟩
    exact ⟨a, keeps_lookup word X maps n ha hX⟩

end Steps
end Refute2003.Bundle

namespace Refute2003.BundleBuild
open Refute2003.Bundle

def ExactSketch {S W α : Type} [Inhabited (Ops (StateM S) W)] (v : Sem S W)
    {r b w : Nat} (s : S) (sk : Sketch W r b w)
    (word : α → Fin w → Bool) (hash : Fin r → α → Fin b) (A : Finset α) : Prop :=
  SketchRep v s sk (active hash A) (rails word hash A)

def Perfect {α : Type} {r b : Nat} (hash : Fin r → α → Fin b) (A : Finset α) : Prop :=
  ∃ h, ∀ a ∈ A, ∀ a' ∈ A, hash h a' = hash h a → a' = a

def RailsMono {w : Nat} (f : Rails w → Prop) : Prop :=
  ∀ {R R'}, RailsLE R R' → f R → f R'

structure HashCheck {S W α : Type} [Inhabited (Ops (StateM S) W)] (v : Sem S W)
    {r b w : Nat} (word : α → Fin w → Bool) (hash : Fin r → α → Fin b)
    (run : Fin r → Fin b → Word W w → StateM S W) where
  spec : Fin r → Fin b → Rails w → Prop
  mono : ∀ h c, RailsMono (spec h c)
  singleton : ∀ h c a, spec h c (singletonRails word a) ↔ hash h a = c
  good : ∀ h c t a R, WordRep v t a R →
    Good v t (run h c a) (fun u out => v.rep u out (spec h c R))

structure MapCheck {S W α β : Type} [Inhabited (Ops (StateM S) W)] (v : Sem S W)
    {w w' : Nat} (word : α → Fin w → Bool) (word' : β → Fin w' → Bool)
    (map : α → β) (run : Word W w → StateM S (Word W w')) where
  spec : Rails w → Rails w'
  mono : ∀ {R R'}, RailsLE R R' → RailsLE (spec R) (spec R')
  singleton : ∀ a, spec (singletonRails word a) = singletonRails word' (map a)
  good : ∀ t a R, WordRep v t a R →
    Good v t (run a) (fun u out => WordRep v u out (spec R))

def identityMap {S W α : Type} [Inhabited (Ops (StateM S) W)] (v : Sem S W)
    {w : Nat} (word : α → Fin w → Bool) :
    MapCheck v word word id (fun code => pure code) where
  spec := id
  mono := fun h => h
  singleton := fun _ => rfl
  good := fun t a _ ha => Good.ret v t a _ ha

section Implementation
variable {S W : Type} [Inhabited (Ops (StateM S) W)] (v : Sem S W)

theorem ExactSketch.extend {α : Type} {r b w : Nat} {s t : S}
    {sk : Sketch W r b w} {word : α → Fin w → Bool}
    {hash : Fin r → α → Fin b} {A : Finset α}
    (hsk : ExactSketch v s sk word hash A) (ext : v.ext s t) :
    ExactSketch v t sk word hash A :=
  SketchRep.extend v hsk ext

theorem lift_exact {α : Type} {r b w : Nat} {s : S} {sk : Sketch W r b w}
    {word : α → Fin w → Bool} {hash : Fin r → α → Fin b} {A : Finset α}
    (hsk : ExactSketch v s sk word hash A) (hperf : Perfect hash A)
    (f : Word W w → StateM S W) (P : α → Prop) (eval : Rails w → Prop)
    (mono : RailsMono eval) (single : ∀ a, eval (singletonRails word a) ↔ P a)
    (h : ∀ t code R, v.ext s t → WordRep v t code R →
      Good v t (f code) (fun u out => v.rep u out (eval R))) :
    Good v s (lift sk f) (fun t out => v.rep t out (∃ a ∈ A, P a)) := by
  apply Good.post v (lift_correct v sk (active hash A) (rails word hash A) f eval hsk h)
  intro t out hh
  exact v.congr (sketchLift_iff word hash A eval P mono single hperf) hh

theorem project_correct {α β : Type} [DecidableEq β] {r b w r' b' w' : Nat}
    {s : S} {sk : Sketch W r b w} {word : α → Fin w → Bool}
    {word' : β → Fin w' → Bool} {hash : Fin r → α → Fin b}
    {hash' : Fin r' → β → Fin b'} {A : Finset α}
    (hsk : ExactSketch v s sk word hash A) (hperf : Perfect hash A)
    (map : α → β) (pred : α → Prop)
    (runMap : Word W w → StateM S (Word W w')) (runKeep : Word W w → StateM S W)
    (runDest : Fin r' → Fin b' → Word W w' → StateM S W)
    (mapOK : MapCheck v word word' map runMap) (destOK : HashCheck v word' hash' runDest)
    (keepEval : Rails w → Prop) (monoKeep : RailsMono keepEval)
    (singleKeep : ∀ a, keepEval (singletonRails word a) ↔ pred a)
    (keepOK : ∀ t code R, v.ext s t → WordRep v t code R →
      Good v t (runKeep code) (fun u out => v.rep u out (keepEval R))) :
    Good v s (project sk runMap runKeep runDest)
      (fun t out => ExactSketch v t out word' hash' (transfer A pred map)) := by
  unfold project ExactSketch
  apply mkSketch_correct v
  · intro h c t hst
    apply Good.post v (P := fun t' out => v.rep t' out
      (∃ a ∈ A, pred a ∧ hash' h (map a) = c)) ?_
    · intro t' out h
      exact v.congr (transfer_active A pred map hash' _ _).symm h
    apply lift_exact v (ExactSketch.extend v hsk hst) hperf _
      (fun a => pred a ∧ hash' h (map a) = c)
      (fun R => keepEval R ∧ destOK.spec h c (mapOK.spec R))
    · intro R R' hR h
      exact ⟨monoKeep hR h.1, destOK.mono _ _ (mapOK.mono hR) h.2⟩
    · intro a
      rw [mapOK.singleton]
      exact and_congr (singleKeep a) (destOK.singleton h c (map a))
    · intro u code R htu hword
      apply Good.bind v (keepOK u code R (v.trans hst htu) hword)
      intro u' keep huu' hKeep
      apply Good.bind v (mapOK.good u' code R (WordRep.extend v hword huu'))
      intro u'' dest hu'u'' hDest
      apply Good.bind v (destOK.good h c u'' dest (mapOK.spec R) hDest)
      intro p matched hv hm
      exact land_good v (v.stabilize (v.trans hu'u'' hv) hKeep) hm
  · intro h c j z t hst
    apply Good.post v (P := fun t' out => v.rep t' out
      (∃ a ∈ A, pred a ∧ hash' h (map a) = c ∧ word' (map a) j = z)) ?_
    · intro t' out h
      exact v.congr (transfer_rails A pred map word' hash' _ _ j z).symm h
    apply lift_exact v (ExactSketch.extend v hsk hst) hperf _
      (fun a => pred a ∧ hash' h (map a) = c ∧ word' (map a) j = z)
      (fun R => (keepEval R ∧ destOK.spec h c (mapOK.spec R)) ∧ mapOK.spec R j z)
    · intro R R' hR h
      have mm := mapOK.mono hR
      exact ⟨⟨monoKeep hR h.1.1, destOK.mono _ _ mm h.1.2⟩, mm _ _ h.2⟩
    · intro a
      rw [mapOK.singleton, and_assoc]
      exact and_congr (singleKeep a) (and_congr (destOK.singleton h c (map a)) Iff.rfl)
    · intro u code R htu hword
      apply Good.bind v (keepOK u code R (v.trans hst htu) hword)
      intro u' keep huu' hKeep
      apply Good.bind v (mapOK.good u' code R (WordRep.extend v hword huu'))
      intro u'' dest hu'u'' hDest
      apply Good.bind v (destOK.good h c u'' dest (mapOK.spec R) hDest)
      intro p matched hv hm
      apply Good.bind v (land_good v (v.stabilize (v.trans hu'u'' hv) hKeep) hm)
      intro p' yes hp hYes
      exact land_good v hYes (v.stabilize (v.trans hv hp) (hDest j z))

def staticLayout {q r b w : Nat} (hash : Fin r → Fin q → Fin b)
    (check : Fin r → Fin b → Word W w → StateM S W) : Layout (StateM S) W q w where
  hashes := r
  buckets := b
  checkCell := check
  entries := fun h c => (List.finRange q).filter (fun a => hash h a == c)

@[simp] theorem staticLayout_mem {q r b w : Nat} (hash : Fin r → Fin q → Fin b)
    (check : Fin r → Fin b → Word W w → StateM S W) (h : Fin r) (c : Fin b) (a : Fin q) :
    a ∈ (staticLayout hash check).entries h c ↔ hash h a = c := by
  simp [staticLayout]

theorem aggregate_correct {q r b w : Nat} {s : S} {sk : Sketch W r b w}
    {word : Fin q → Fin w → Bool} {hash : Fin r → Fin q → Fin b} {A : Finset (Fin q)}
    (hsk : ExactSketch v s sk word hash A) (hperf : Perfect hash A)
    (layout : Layout (StateM S) W q w) (hash' : Fin layout.hashes → Fin q → Fin layout.buckets)
    (hcheck : HashCheck v word hash' layout.checkCell) :
    Good v s (aggregate sk layout) (fun t out => ExactSketch v t out word hash' A) := by
  unfold aggregate ExactSketch
  apply mkSketch_correct v
  · intro h c t ht
    exact lift_exact v (ExactSketch.extend v hsk ht) hperf _ _ _
      (hcheck.mono h c) (hcheck.singleton h c)
      (fun u code R _ hu => hcheck.good h c u code R hu)
  · intro h c j z t ht
    apply lift_exact v (ExactSketch.extend v hsk ht) hperf _
      (fun a => hash' h a = c ∧ word a j = z) (fun R => hcheck.spec h c R ∧ R j z)
    · intro R R' hR hp
      exact ⟨hcheck.mono h c hR hp.1, hR _ _ hp.2⟩
    · intro a
      exact and_congr (hcheck.singleton h c a) Iff.rfl
    · intro u code R _ hR
      apply Good.bind v (hcheck.good h c u code R hR)
      intro t' out ext hout
      exact land_good v hout (v.stabilize ext (hR j z))

theorem sameWord_correct {w : Nat} {s : S} {a : Word W w}
    {R : Rails w} (val : Fin w → Bool) (hR : WordRep v s a R) :
    Good v s (sameWord a val) (fun t out => v.rep t out (∀ j, R j (val j))) := by
  apply all_correct v
  intro j t hst
  exact Good.ret v t _ _ (v.stabilize hst (hR j (val j)))

theorem table_correct {q w : Nat} {s : S} (layout : Layout (StateM S) W q w)
    (word : Fin q → Fin w → Bool) (hash : Fin layout.hashes → Fin q → Fin layout.buckets)
    (A : Finset (Fin q)) (X : Fin q → W) (XP : Fin q → Prop)
    (sk : Sketch W layout.hashes layout.buckets w)
    (hsk : ExactSketch v s sk word hash A) (hx : ∀ a, v.rep s (X a) (XP a))
    (hmem : ∀ h c a, a ∈ layout.entries h c ↔ hash h a = c) :
    Good v s (table layout sk word X) (fun t out =>
      ∀ h c, v.rep t (out h c) (bucketHit word hash XP A h c)) := by
  unfold table
  refine tab_correct v layout.hashes _ (fun h t (row : Fin layout.buckets → W) =>
    ∀ c, v.rep t (row c) (bucketHit word hash XP A h c)) ?_ ?_
  · intro h t u row ext he c
    exact v.stabilize ext (he c)
  · intro h u hsu
    refine tab_correct v layout.buckets _ (fun c t x =>
      v.rep t x (bucketHit word hash XP A h c)) ?_ ?_
    · intro c t t' x ext he
      exact v.stabilize ext he
    · intro c t hut
      have hst := v.trans hsu hut
      let R := rails word hash A h c
      let p : Fin q → Prop := fun a => XP a ∧ ∀ j, R j (word a j)
      have hf : ∀ a ∈ layout.entries h c, ∀ k, v.ext t k →
          Good v k (do let eq ← sameWord (sk h c).code (word a); Ops.land (X a) eq)
            (fun k' out => v.rep k' out (p a)) := by
        intro a _ k htk
        have hsk' := ExactSketch.extend v hsk (v.trans hst htk) h c
        apply Good.bind v (sameWord_correct v (word a) hsk'.2)
        intro k' eq hkk' heq
        exact land_good v (v.stabilize (v.trans (v.trans hst htk) hkk') (hx a)) heq
      apply Good.bind v (reduce_correct v (layout.entries h c) _ p Ops.lor Or
        (fun a b => lor_good v a b) hf _ False (const_false v t))
      intro k yes htk hyes
      have hy : v.rep k yes (∃ a, hash h a = c ∧ XP a ∧ ∀ j, R j (word a j)) := by
        apply v.congr _ hyes
        rw [fold_or_iff]
        simp [hmem,p]
      exact land_good v (ExactSketch.extend v hsk (v.trans hst htk) h c).1 hy

def filterEval {q w : Nat} (layout : Layout (StateM S) W q w)
    (word : Fin q → Fin w → Bool) (hash : Fin layout.hashes → Fin q → Fin layout.buckets)
    (ok : HashCheck v word hash layout.checkCell)
    (P : Fin layout.hashes → Fin layout.buckets → Prop) (R : Rails w) : Prop :=
  ∀ h, ∃ c, ok.spec h c R ∧ P h c

theorem filter_mono {q w : Nat} (layout : Layout (StateM S) W q w)
    (word : Fin q → Fin w → Bool) (hash : Fin layout.hashes → Fin q → Fin layout.buckets)
    (ok : HashCheck v word hash layout.checkCell)
    (P : Fin layout.hashes → Fin layout.buckets → Prop) :
    RailsMono (filterEval v layout word hash ok P) := by
  intro R R' hRs hR h
  obtain ⟨c, hc, hP⟩ := hR h
  exact ⟨c, ok.mono h c hRs hc, hP⟩

theorem filter_single {q w : Nat} (layout : Layout (StateM S) W q w)
    (word : Fin q → Fin w → Bool) (hash : Fin layout.hashes → Fin q → Fin layout.buckets)
    (ok : HashCheck v word hash layout.checkCell)
    (P : Fin layout.hashes → Fin layout.buckets → Prop) (a : Fin q) :
    filterEval v layout word hash ok P (singletonRails word a) ↔ ∀ h, P h (hash h a) := by
  constructor
  · intro he h
    obtain ⟨c, hc, hP⟩ := he h
    rw [ok.singleton] at hc
    exact hc.symm ▸ hP
  · intro h h'
    exact ⟨hash h' a,(ok.singleton h' (hash h' a) a).mpr rfl,h h'⟩

theorem filter_correct {q w : Nat} {s : S} (layout : Layout (StateM S) W q w)
    (word : Fin q → Fin w → Bool) (hash : Fin layout.hashes → Fin q → Fin layout.buckets)
    (ok : HashCheck v word hash layout.checkCell)
    (P : Fin layout.hashes → Fin layout.buckets → Prop) (V : Fin layout.hashes → Fin layout.buckets → W)
    (hV : ∀ h c, v.rep s (V h c) (P h c)) (a : Word W w) (R : Rails w)
    (hR : WordRep v s a R) :
    Good v s (filterWord layout V a) (fun t out =>
      v.rep t out (filterEval v layout word hash ok P R)) := by
  apply all_correct v
  intro h t hst
  apply any_correct v
  intro c u htu
  have hsu := v.trans hst htu
  apply Good.bind v (ok.good h c u a R (WordRep.extend v hR hsu))
  intro u' m huu' hm
  exact land_good v hm (v.stabilize (v.trans hsu huu') (hV h c))

end Implementation
end Refute2003.BundleBuild

namespace Refute2003.BundleBuild

structure Budget (M : Type → Type) [Monad M] where
  withinCost : {A : Type} → M A → Nat → Prop
  weakenCost {A : Type} {p : M A} {k l : Nat} : withinCost p k → k ≤ l → withinCost p l
  returnCost {A : Type} (a : A) : withinCost (pure a) 0
  bindCost {A B : Type} {p : M A} {f : A → M B} {k l : Nat} :
    withinCost p k → (∀ a, withinCost (f a) l) → withinCost (p >>= f) (k+l)

abbrev Budget.within {M : Type → Type} [Monad M] [Inhabited (Budget M)]
    {A : Type} (p : M A) (k : Nat) : Prop :=
  (default : Budget M).withinCost p k

theorem Budget.weaken {M : Type → Type} [Monad M] [Inhabited (Budget M)]
    {A : Type} {p : M A} {k l : Nat} : Budget.within p k → k ≤ l → Budget.within p l :=
  (default : Budget M).weakenCost

theorem Budget.ret {M : Type → Type} [Monad M] [Inhabited (Budget M)] {A : Type} (a : A) :
    Budget.within (pure a : M A) 0 :=
  (default : Budget M).returnCost a

theorem Budget.seq {M : Type → Type} [Monad M] [Inhabited (Budget M)]
    {A B : Type} {p : M A} {f : A → M B} {k l : Nat} :
    Budget.within p k → (∀ a, Budget.within (f a) l) → Budget.within (p >>= f) (k+l) :=
  (default : Budget M).bindCost

structure UnitGateBudget (M : Type → Type) (W : Type) [Monad M]
    [Inhabited (Ops M W)] [Inhabited (Budget M)] : Prop where
  andCost (a b : W) : Budget.within (Ops.land a b : M W) 1
  orCost (a b : W) : Budget.within (Ops.lor a b : M W) 1

theorem UnitGateBudget.land {M : Type → Type} {W : Type} [Monad M]
    [Inhabited (Ops M W)] [Inhabited (Budget M)] [Fact (UnitGateBudget M W)] (a b : W) :
    Budget.within (Ops.land a b : M W) 1 :=
  (Fact.out : UnitGateBudget M W).andCost a b

theorem UnitGateBudget.lor {M : Type → Type} {W : Type} [Monad M]
    [Inhabited (Ops M W)] [Inhabited (Budget M)] [Fact (UnitGateBudget M W)] (a b : W) :
    Budget.within (Ops.lor a b : M W) 1 :=
  (Fact.out : UnitGateBudget M W).orCost a b

def sumFin : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n+1, f => f 0 + sumFin n (fun i => f i.succ)

def sumList {A : Type} (f : A → Nat) : List A → Nat
  | [] => 0
  | a::as => f a + sumList f as

theorem sumFin_const (n k : Nat) : sumFin n (fun _ => k) = n*k := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih => simp [sumFin, ih, Nat.succ_mul, Nat.add_comm]

theorem sumFin_add (n : Nat) (f g : Fin n → Nat) :
    sumFin n (fun a => f a + g a) = sumFin n f + sumFin n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin, ih]
    omega

theorem sumFin_mul (n c : Nat) (f : Fin n → Nat) :
    sumFin n (fun a => f a * c) = sumFin n f * c := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih => simp [sumFin, ih, Nat.add_mul]

theorem sumList_const {A : Type} (xs : List A) (c : Nat) :
    sumList (fun _ => c) xs = xs.length*c := by
  induction xs with
  | nil => simp [sumList]
  | cons a as ih => simp [sumList, ih, Nat.succ_mul, Nat.add_comm]

section BudgetLemmas
variable {M : Type → Type} [Monad M] [Inhabited (Budget M)]

theorem then_ret {A B : Type} {p : M A} {k : Nat} (f : A → B)
    (h : Budget.within p k) : Budget.within (p >>= fun a => pure (f a)) k := by
  simpa using Budget.seq h (fun a => Budget.ret (M := M) (f a))

theorem tab_cost {A : Type} (n : Nat) (f : Fin n → M A) (c : Fin n → Nat)
    (h : ∀ i, Budget.within (f i) (c i)) : Budget.within (tabM n f) (sumFin n c) := by
  induction n with
  | zero => exact Budget.ret Fin.elim0
  | succ n ih =>
    change Budget.within (f 0 >>= fun hd => tabM n (fun i => f i.succ) >>=
      fun (tl : Fin n → A) => (pure (fun i : Fin (n+1) => Fin.cases hd tl i) : M (Fin (n+1) → A))) (c 0 + sumFin n (fun i => c i.succ))
    exact Budget.seq (h 0) (fun hd => then_ret (fun (tl : Fin n → A) => Fin.cases (motive := fun _ => A) hd tl) (ih _ _ (fun i => h i.succ)))

theorem tab_uniform {A : Type} (n : Nat) (f : Fin n → M A) (c : Nat)
    (h : ∀ i, Budget.within (f i) c) : Budget.within (tabM n f) (n*c) := by
  rw [←sumFin_const n c]
  exact tab_cost n f (fun _ => c) h

theorem fold_cost {A S : Type} (xs : List A) (f : S → A → M S)
    (c : A → Nat) (h : ∀ (s : S) (a : A), Budget.within (f s a) (c a)) (s : S) :
    Budget.within (xs.foldlM f s) (sumList c xs) := by
  induction xs generalizing s with
  | nil => exact Budget.ret s
  | cons a as ih =>
    change Budget.within (f s a >>= fun t => as.foldlM f t) (c a + sumList c as)
    exact Budget.seq (h s a) ih

theorem fold_uniform {A S : Type} (xs : List A) (f : S → A → M S)
    (c : Nat) (h : ∀ (s : S) (a : A), Budget.within (f s a) c) (s : S) :
    Budget.within (xs.foldlM f s) (xs.length*c) := by
  rw [←sumList_const xs c]
  exact fold_cost xs f (fun _ => c) h s

end BudgetLemmas

section Gates
variable {M : Type → Type} {W : Type} [Monad M] [Inhabited (Ops M W)] [Inhabited (Budget M)] [Fact (UnitGateBudget M W)]

theorem land_cost (a b : W) : Budget.within (Ops.land a b : M W) 1 :=
  UnitGateBudget.land a b

theorem lor_cost (a b : W) : Budget.within (Ops.lor a b : M W) 1 :=
  UnitGateBudget.lor a b

theorem reduce_cost {A : Type} (xs : List A) (f : A → M W)
    (op : W → W → M W) (z : W) (c g : Nat)
    (hf : ∀ a, Budget.within (f a) c)
    (ho : ∀ u v, Budget.within (op u v) g) :
    Budget.within (reduceF op z xs f) (xs.length*(c+g)) :=
  fold_uniform xs _ _ (fun u x => Budget.seq (hf x) (ho u)) z

theorem allFin_cost (n c : Nat) (f : Fin n → M W)
    (h : ∀ i, Budget.within (f i) c) :
    Budget.within (allFin n f) (n*(c+1)) := by
  simpa [allFin] using reduce_cost (List.finRange n) f Ops.land
    (Ops.const (M := M) (W := W) true) c 1 h land_cost

theorem anyFin_cost (n c : Nat) (f : Fin n → M W)
    (h : ∀ i, Budget.within (f i) c) :
    Budget.within (anyFin n f) (n*(c+1)) := by
  simpa [anyFin] using reduce_cost (List.finRange n) f Ops.lor
    (Ops.const (M := M) (W := W) false) c 1 h lor_cost

theorem dualAnd_cost (a b : Dual W) : Budget.within (dualAnd (M := M) a b) 2 := by
  exact Budget.seq (land_cost a.1 b.1)
    (fun p => then_ret (fun n => (p,n)) (lor_cost a.2 b.2))

theorem dualXor_cost (a b : Dual W) : Budget.within (dualXor (M := M) a b) 6 := by
  exact Budget.seq (land_cost a.1 b.2) fun p₁ =>
    Budget.seq (land_cost a.2 b.1) fun p₂ =>
    Budget.seq (land_cost a.1 b.1) fun n₁ =>
    Budget.seq (land_cost a.2 b.2) fun n₂ =>
    Budget.seq (lor_cost p₁ p₂) fun p =>
      then_ret (fun n => (p,n)) (lor_cost n₁ n₂)

theorem sameWord_cost {w : Nat} (a : Word W w) (v : Fin w → Bool) :
    Budget.within (sameWord (M := M) a v) w := by
  simpa [sameWord] using allFin_cost w 0
    (fun j => pure (selected (a j) (v j))) (fun j => Budget.ret (selected (a j) (v j)))

theorem addBits_cost {w : Nat} (a b : Word W w) :
    Budget.within (addBits (M := M) a b) (w*6) :=
  tab_uniform w _ _ (fun j => dualXor_cost (a j) (b j))

theorem sum_pairs_len {w : Nat} (xs : List (Fin w)) :
    (xs.flatMap (fun j => (List.finRange w).map (fun k => (j,k)))).length =
      xs.length*w := by
  induction xs with
  | nil => simp
  | cons a as ih => simp [ih, Nat.succ_mul, Nat.add_comm]

theorem mulBits_cost {w : Nat} (constants : Fin w → Fin w → Fin w → Bool)
    (a b : Word W w) : Budget.within (mulBits (M := M) constants a b) (w*(w*w*8)) := by
  apply tab_uniform
  intro i
  let pairs := (List.finRange w).flatMap (fun j => (List.finRange w).map (fun k => (j,k)))
  let chosen := pairs.filter (fun jk => constants i jk.1 jk.2)
  have hs : chosen.length ≤ w*w := by
    calc
      chosen.length ≤ pairs.length := List.length_filter_le ..
      _ = w*w := by simpa [pairs] using (sum_pairs_len (List.finRange w))
  have hb := fold_uniform (M := M) chosen
    (fun acc jk => dualAnd (M := M) (a jk.1) (b jk.2) >>= fun prod => dualXor (M := M) acc prod)
    8 (fun acc jk => Budget.seq (dualAnd_cost (a jk.1) (b jk.2)) (dualXor_cost acc))
    (dualConst (M := M) (W := W) false)
  exact Budget.weaken hb (Nat.mul_le_mul_right 8 hs)

theorem hornerBits_cost {w : Nat} (constants : Fin w → Fin w → Fin w → Bool)
    (coeffs : List (Fin w → Bool)) (a : Word W w) :
    Budget.within (hornerBits (M := M) constants coeffs a)
      (coeffs.length*(w*(w*w*8)+w*6)) := by
  apply fold_uniform
  intro s c
  exact Budget.seq (mulBits_cost constants s a) (fun p =>
    addBits_cost p (fun i => dualConst (M := M) (W := W) (c i)))

theorem affineBits_cost {w o : Nat} (matrix : Fin o → Fin w → Bool)
    (offset : Fin o → Bool) (a : Word W w) :
    Budget.within (affineBits (M := M) matrix offset a) (o*(w*6)) := by
  apply tab_uniform
  intro i
  have hb := fold_uniform (M := M) ((List.finRange w).filter (matrix i))
    (fun acc j => dualXor (M := M) acc (a j)) 6 (fun acc j => dualXor_cost acc (a j))
    (dualConst (M := M) (W := W) (offset i))
  exact Budget.weaken hb (Nat.mul_le_mul_right 6
    (by simpa using (List.length_filter_le (matrix i) (List.finRange w))))

theorem lift_cost {r b w : Nat} (src : Sketch W r b w) (f : Word W w → M W) (c : Nat)
    (h : ∀ x, Budget.within (f x) c) :
    Budget.within (lift src f) (r*(b*(c+2)+1)) := by
  apply allFin_cost
  intro i
  apply anyFin_cost
  intro j
  have hb : Budget.within (f (src i j).code >>= fun y => Ops.land (src i j).present y) (c+1) :=
    Budget.seq (h _) (land_cost (src i j).present)
  simpa [Nat.add_assoc] using hb

theorem sketch_cost {r b w : Nat}
    (actPred : Fin r → Fin b → M W) (bitPred : Fin r → Fin b → Fin w → Bool → M W)
    (ca cb : Nat) (ha : ∀ h c, Budget.within (actPred h c) ca)
    (hb : ∀ h c j z, Budget.within (bitPred h c j z) cb) :
    Budget.within (mkSketch actPred bitPred) (r*(b*(ca+w*(cb+cb)))) := by
  apply tab_uniform
  intro h
  apply tab_uniform
  intro c
  apply Budget.seq (ha h c)
  intro present
  apply then_ret (fun word => Cell.mk present word)
  apply tab_uniform
  intro j
  exact Budget.seq (hb h c j true) (fun p =>
    then_ret (fun n => (p,n)) (hb h c j false))

theorem project_cost {r b w r' b' w' : Nat} (src : Sketch W r b w)
    (map : Word W w → M (Word W w')) (keep : Word W w → M W)
    (matchDest : Fin r' → Fin b' → Word W w' → M W)
    (cm ck ch : Nat) (hm : ∀ x, Budget.within (map x) cm)
    (hk : ∀ x, Budget.within (keep x) ck)
    (hh : ∀ h c x, Budget.within (matchDest h c x) ch) :
    Budget.within (project src map keep matchDest)
      (r'*(b'*(r*(b*((ck+cm+ch+1)+2)+1)+w'*(r*(b*((ck+cm+ch+2)+2)+1)+r*(b*((ck+cm+ch+2)+2)+1))))) := by
  apply sketch_cost
  · intro h c
    apply lift_cost
    intro x
    have z := Budget.seq (hk x) (fun k => Budget.seq (hm x) (fun y =>
      Budget.seq (hh h c y) (land_cost k)))
    simpa [Nat.add_assoc] using z
  · intro h c j v
    apply lift_cost
    intro x
    have z := Budget.seq (hk x) (fun k => Budget.seq (hm x) (fun y =>
      Budget.seq (hh h c y) (fun m =>
      Budget.seq (land_cost k m) (fun ok => land_cost ok (selected (y j) v)))))
    simpa [Nat.add_assoc] using z

theorem aggregation_cost {q r b w : Nat} (src : Sketch W r b w) (lay : Layout M W q w)
    (c : Nat) (h : ∀ h g a, Budget.within (lay.checkCell h g a) c) :
    Budget.within (aggregate src lay)
      (lay.hashes*(lay.buckets*(r*(b*(c+2)+1)+w*(r*(b*((c+1)+2)+1)+r*(b*((c+1)+2)+1))))) := by
  apply sketch_cost
  · intro hh gg
    exact lift_cost src _ c (h hh gg)
  · intro hh gg j z
    exact lift_cost src _ (c+1) (fun x => Budget.seq (h hh gg x) (fun m =>
      land_cost m (selected (x j) z)))

theorem table_cost {q w : Nat} (lay : Layout M W q w)
    (agg : Sketch W lay.hashes lay.buckets w) (word : Fin q → Fin w → Bool) (X : Fin q → W)
    (part : ∀ h, sumFin lay.buckets (fun c => (lay.entries h c).length) ≤ q) :
    Budget.within (table lay agg word X) (lay.hashes*(q*((w+1)+1)+lay.buckets)) := by
  apply tab_uniform
  intro h
  let entry (c : Fin lay.buckets) (v : Fin q) : M W :=
    sameWord (agg h c).code (word v) >>= Ops.land (X v)
  let f (c : Fin lay.buckets) : M W := do
    let yes ← reduceF Ops.lor (Ops.const (M := M) (W := W) false) (lay.entries h c) (entry c)
    Ops.land (agg h c).present yes
  have hm : ∀ c, Budget.within (f c) ((lay.entries h c).length*((w+1)+1)+1) := by
    intro c
    unfold f
    exact Budget.seq
      (reduce_cost (lay.entries h c) (entry c) Ops.lor
        (Ops.const (M := M) (W := W) false) (w+1) 1
        (fun v => Budget.seq (sameWord_cost (agg h c).code (word v)) (land_cost (X v)))
        lor_cost)
      (land_cost (agg h c).present)
  have raw := tab_cost lay.buckets f _ hm
  apply Budget.weaken raw
  simp only [sumFin_add, sumFin_mul, sumFin_const, Nat.mul_one]
  have hu := Nat.mul_le_mul_right ((w+1)+1) (part h)
  omega

theorem filterWord_cost {q w : Nat} (lay : Layout M W q w)
    (V : Fin lay.hashes → Fin lay.buckets → W) (a : Word W w)
    (c : Nat) (h : ∀ h g, Budget.within (lay.checkCell h g a) c) :
    Budget.within (filterWord lay V a) (lay.hashes*(lay.buckets*((c+1)+1)+1)) := by
  apply allFin_cost
  intro i
  apply anyFin_cost
  intro j
  exact Budget.seq (h i j) (fun m => land_cost m (V i j))

def projCharge (r b r' b' w' cm ck ch : Nat) : Nat :=
  r'*(b'*(r*(b*((ck+cm+ch+1)+2)+1)+w'*(r*(b*((ck+cm+ch+2)+2)+1)+r*(b*((ck+cm+ch+2)+2)+1))))

def aggCharge (r b w H B c : Nat) : Nat :=
  H*(B*(r*(b*(c+2)+1)+w*(r*(b*((c+1)+2)+1)+r*(b*((c+1)+2)+1))))

def tableCharge (q w H B : Nat) : Nat :=
  H*(q*((w+1)+1)+B)

def filterCharge (H B c : Nat) : Nat :=
  H*(B*((c+1)+1)+1)

def stepCharge (q r b w H B c own : Nat) : Nat :=
  aggCharge r b w H B c +
    (tableCharge q w H B + projCharge r b r b w 0 (filterCharge H B c) own)

theorem oneStep_cost {q r b w : Nat} (src : Sketch W r b w)
    (word : Fin q → Fin w → Bool) (X : Fin q → W) (lay : Layout M W q w)
    (matchOwn : Fin r → Fin b → Word W w → M W) (c own : Nat)
    (h : ∀ u j a, Budget.within (lay.checkCell u j a) c)
    (oh : ∀ u j a, Budget.within (matchOwn u j a) own)
    (part : ∀ u, sumFin lay.buckets (fun j => (lay.entries u j).length) ≤ q) :
    Budget.within (step src word X lay matchOwn) (stepCharge q r b w lay.hashes lay.buckets c own) := by
  exact Budget.seq (aggregation_cost src lay c h) (fun agg =>
    Budget.seq (table_cost lay agg word X part) (fun V =>
      project_cost src pure (filterWord lay V) matchOwn 0
        (filterCharge lay.hashes lay.buckets c) own Budget.ret
        (fun a => filterWord_cost lay V a c (fun u j => h u j a)) oh))

theorem lookup_cost {q r b w : Nat} (src : Sketch W r b w)
    (word : Fin q → Fin w → Bool) (X : Fin q → W) (lays : List (Layout M W q w))
    (matchOwn : Fin r → Fin b → Word W w → M W) (h₀ : Fin r)
    (c : Layout M W q w → Nat) (own : Nat)
    (hh : ∀ lay u j a, Budget.within (lay.checkCell u j a) (c lay))
    (oh : ∀ u j a, Budget.within (matchOwn u j a) own)
    (part : ∀ (lay : Layout M W q w) u, sumFin lay.buckets (fun j => (lay.entries u j).length) ≤ q) :
    Budget.within (lookup src word X lays matchOwn h₀)
      (sumList (fun lay => stepCharge q r b w lay.hashes lay.buckets (c lay) own) lays + b) := by
  apply Budget.seq
  · exact fold_cost lays (fun s lay => step s word X lay matchOwn)
      (fun lay => stepCharge q r b w lay.hashes lay.buckets (c lay) own)
      (fun s lay => oneStep_cost s word X lay matchOwn (c lay) own (hh lay) oh (part lay)) src
  · intro out
    simpa using anyFin_cost b 0
      (fun j => pure (out h₀ j).present) (fun j => Budget.ret (out h₀ j).present)

end Gates
end Refute2003.BundleBuild

namespace Refute2003.BundleBuild
open Refute2003.Bundle
open scoped BigOperators

structure StageModel {S W : Type} [Inhabited (Ops (StateM S) W)] (v : Sem S W) {q w : Nat}
    (word : Fin q → Fin w → Bool) (layout : Layout (StateM S) W q w) where
  hash : Fin layout.hashes → Fin q → Fin layout.buckets
  check : HashCheck v word hash layout.checkCell
  mem : ∀ h c a, a ∈ layout.entries h c ↔ hash h a = c

def StageModel.ofStatic {S W : Type} [Inhabited (Ops (StateM S) W)] (v : Sem S W) {q w h b : Nat}
    (word : Fin q → Fin w → Bool) (hash : Fin h → Fin q → Fin b)
    (check : Fin h → Fin b → Word W w → StateM S W)
    (ok : HashCheck v word hash check) : StageModel v word (staticLayout hash check) where
  hash := hash
  check := ok
  mem := staticLayout_mem hash check

def stages {L : Type} (layouts : Nat → L) : Nat → List L
  | 0 => [layouts 0]
  | e+1 => layouts (e+1) :: stages layouts e

section Step
variable {S W : Type} [Inhabited (Ops (StateM S) W)] (v : Sem S W)

theorem step_correct {q r b w : Nat} {s : S} {sk : Sketch W r b w}
    {word : Fin q → Fin w → Bool} {hash : Fin r → Fin q → Fin b} {A : Finset (Fin q)}
    (hsk : ExactSketch v s sk word hash A) (hperf : Perfect hash A)
    (layout : Layout (StateM S) W q w) (mdl : StageModel v word layout)
    (checks : Fin r → Fin b → Word W w → StateM S W)
    (own : HashCheck v word hash checks)
    (X : Fin q → W) (XP : Fin q → Prop) (hx : ∀ a, v.rep s (X a) (XP a)) :
    Good v s (step sk word X layout checks)
      (fun t out => ExactSketch v t out word hash (advance word mdl.hash XP A)) := by
  unfold step
  apply Good.bind v (aggregate_correct v hsk hperf layout mdl.hash mdl.check)
  intro t agg hst hagg
  apply Good.bind v (table_correct v layout word mdl.hash A X XP agg hagg
    (fun a => v.stabilize hst (hx a)) mdl.mem)
  intro u V htu hV
  let p := bucketHit word mdl.hash XP A
  let E := filterEval v layout word mdl.hash mdl.check p
  let pred : Fin q → Prop := fun a => ∀ h, p h (mdl.hash h a)
  have hP := project_correct v (ExactSketch.extend v hsk (v.trans hst htu)) hperf
    id pred _ (filterWord layout V) checks (identityMap v word) own
    E (filter_mono v layout word mdl.hash mdl.check p) (filter_single v layout word mdl.hash mdl.check p)
    (fun t' code R hut' hR =>
      filter_correct v layout word mdl.hash mdl.check p V
        (fun h c => v.stabilize hut' (hV h c)) code R hR)
  have eq : transfer A pred id = advance word mdl.hash XP A := by
    ext a
    rw [mem_transfer,mem_advance]
    constructor
    · rintro ⟨a',ha',hp,hea⟩
      change a' = a at hea
      subst a'
      exact ⟨ha',hp⟩
    · rintro ⟨ha,hp⟩
      exact ⟨a,ha,hp,rfl⟩
  simpa only [eq] using hP

theorem compiled_steps {q r b w : Nat} {s : S} {sk : Sketch W r b w}
    {word : Fin q → Fin w → Bool} {hash : Fin r → Fin q → Fin b} {A : Finset (Fin q)}
    (X : Fin q → W) (XP : Fin q → Prop)
    (layouts : Nat → Layout (StateM S) W q w) (mdls : ∀ e, StageModel v word (layouts e))
    (checks : Fin r → Fin b → Word W w → StateM S W)
    (own : HashCheck v word hash checks) (cap : Nat)
    (perf : ∀ B : Finset (Fin q), B.card ≤ cap → Perfect hash B)
    (e : Nat) (hA : A.card ≤ cap)
    (hsk : ExactSketch v s sk word hash A) (hx : ∀ a, v.rep s (X a) (XP a)) :
    Good v s ((stages layouts e).foldlM (fun src layout => step src word X layout checks) sk)
      (fun t out => ExactSketch v t out word hash (lookupSteps word XP (fun j => (mdls j).hash) e A)) := by
  induction e generalizing s sk A with
  | zero =>
    change Good v s (step sk word X (layouts 0) checks >>= fun s' => pure s')
      (fun t out => ExactSketch v t out word hash (advance word (mdls 0).hash XP A))
    exact Good.bind v
      (step_correct v hsk (perf A hA) (layouts 0) (mdls 0) checks own X XP hx)
      (fun t a _ ht => Good.ret v t a _ ht)
  | succ e ih =>
    change Good v s (step sk word X (layouts (e+1)) checks >>= fun s' =>
      (stages layouts e).foldlM (fun src layout => step src word X layout checks) s')
      (fun t out => ExactSketch v t out word hash
        (lookupSteps word XP (fun j => (mdls j).hash) e (advance word (mdls (e+1)).hash XP A)))
    apply Good.bind v
      (step_correct v hsk (perf A hA) (layouts (e+1)) (mdls (e+1)) checks own X XP hx)
    intro t a hst ht
    exact ih ((Finset.card_le_card (advance_subset word (mdls (e+1)).hash XP A)).trans hA)
      ht (fun j => v.stabilize hst (hx j))

theorem lookup_noHit_bounded {q w : Nat} (word : Fin q → Fin w → Bool) (XP : Fin q → Prop)
    {H B : Nat → Nat} (maps : (j : Nat) → Fin (H j) → Fin q → Fin (B j))
    (inj : Function.Injective word) (e : Nat)
    (family : ∀ n ≤ e, ∀ (A : Finset (Fin q)), halfThreshold n < A.card → A.card ≤ 2^n →
      ∃ I : Finset (Fin q), I ⊆ A ∧ A.card ≤ 2*I.card ∧ ∀ a ∈ I, ∃ h, isolated (maps n) A h a)
    (A : Finset (Fin q)) (hc : A.card ≤ 2^e) (noHit : ∀ a ∈ A, ¬ XP a) :
    lookupSteps word XP maps e A = ∅ := by
  induction e generalizing A with
  | zero =>
    have hh : (advance word (maps 0) XP A).card ≤ 0 :=
      advance_card_le word (maps 0) XP inj noHit (by simpa using hc)
        (fun h => family 0 (Nat.le_refl _) A h hc)
    exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hh)
  | succ e ih =>
    have hc' : A.card ≤ 2*(2^e)+1 := by
      rw [pow_succ] at hc
      omega
    have ha : (advance word (maps (e+1)) XP A).card ≤ 2^e :=
      advance_card_le word (maps (e+1)) XP inj noHit hc'
        (fun h => family (e+1) (Nat.le_refl _) A h hc)
    exact ih (fun n hn => family n (hn.trans (Nat.le_succ _))) _ ha
      (fun a ha' => noHit a (advance_subset word (maps (e+1)) XP A ha'))

theorem lookup_correct {q r b w : Nat} {s : S} {sk : Sketch W r b w}
    {word : Fin q → Fin w → Bool} {hash : Fin r → Fin q → Fin b} {A : Finset (Fin q)}
    (X : Fin q → W) (XP : Fin q → Prop)
    (layouts : Nat → Layout (StateM S) W q w) (mdls : ∀ e, StageModel v word (layouts e))
    (checks : Fin r → Fin b → Word W w → StateM S W)
    (own : HashCheck v word hash checks) (e : Nat) (owner : Fin r)
    (perf : ∀ B : Finset (Fin q), B.card ≤ 2^e → Perfect hash B)
    (family : ∀ n ≤ e, ∀ (B : Finset (Fin q)), halfThreshold n < B.card → B.card ≤ 2^n →
      ∃ I : Finset (Fin q), I ⊆ B ∧ B.card ≤ 2*I.card ∧ ∀ a ∈ I, ∃ h, isolated (mdls n).hash B h a)
    (inj : Function.Injective word) (hA : A.card ≤ 2^e)
    (hsk : ExactSketch v s sk word hash A) (hx : ∀ a, v.rep s (X a) (XP a)) :
    Good v s (lookup sk word X (stages layouts e) checks owner)
      (fun t out => v.rep t out (∃ a ∈ A, XP a)) := by
  unfold lookup
  apply Good.bind v (compiled_steps v X XP layouts mdls checks own (2^e) perf e hA hsk hx)
  intro t final _ hfinal
  let result := lookupSteps word XP (fun j => (mdls j).hash) e A
  have hb : Good v t (anyFin b (fun c => pure (final owner c).present))
      (fun u out => v.rep u out (∃ c, active hash result owner c)) := by
    apply any_correct v
    intro c u htu
    exact Good.ret v u _ _ (v.stabilize htu (hfinal owner c).1)
  apply Good.post v hb
  intro u out ho
  apply v.congr _ ho
  constructor
  · rintro ⟨c,a,ha,hh⟩
    by_contra hn
    have hnone : ∀ a ∈ A, ¬ XP a := fun a ha hp => hn ⟨a,ha,hp⟩
    have h0 := lookup_noHit_bounded word XP (fun j => (mdls j).hash) inj e family A hA hnone
    have habs : a ∈ (∅ : Finset (Fin q)) := h0 ▸ ha
    exact Finset.notMem_empty _ habs
  · rintro ⟨a,ha,hp⟩
    have hr := keeps_lookup word XP (fun j => (mdls j).hash) e ha hp
    exact ⟨hash owner a,a,hr,rfl⟩

end Step

theorem sumFin_eq_sum (n : Nat) (f : Fin n → Nat) : sumFin n f = ∑ i, f i := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    rw [sumFin, Fin.sum_univ_succ, ih]

theorem length_partition {α : Type} {n : Nat} (words : List α) (bucket : α → Fin n) :
    sumFin n (fun c => (words.filter (fun a => bucket a == c)).length) = words.length := by
  classical
  induction words with
  | nil =>
    simpa [sumFin_const]
  | cons a as ih =>
    have terms : (fun c => ((a::as).filter (fun x => bucket x == c)).length) =
        fun c => (as.filter (fun x => bucket x == c)).length + if c = bucket a then 1 else 0 := by
      funext c
      by_cases h : c = bucket a
      · simp [h]
      · have hn := Ne.symm h
        simp [h,hn]
    rw [terms,sumFin_add,ih,sumFin_eq_sum]
    simp

theorem staticLayout_entries_count {S W : Type} {q r b w : Nat}
    (hash : Fin r → Fin q → Fin b) (check : Fin r → Fin b → Word W w → StateM S W)
    (h : Fin r) :
    sumFin b (fun c => ((staticLayout hash check).entries h c).length) = q := by
  change sumFin b (fun c => ((List.finRange q).filter (fun a => hash h a == c)).length) = q
  simpa using (length_partition (List.finRange q) (hash h))

end Refute2003.BundleBuild

namespace Refute2003.BundleBuild
open Refute2003.Bundle

section Emit
variable {M : Type → Type} {W : Type} [Monad M] [Inhabited (Ops M W)]

def encodeRaw {α : Type} {r b w : Nat} (labels : List α)
    (word : α → Fin w → Bool) (hash : Fin r → α → Fin b) (Y : α → W) :
    M (Sketch W r b w) :=
  let fiber h c := labels.filter (fun a => hash h a == c)
  let f (ys : List α) := reduceF Ops.lor (Ops.const (M := M) (W := W) false) ys
    (fun a => pure (Y a))
  mkSketch (fun h c => f (fiber h c))
    (fun h c j z => f ((fiber h c).filter (fun a => word a j == z)))

def detectGroup {α : Type} {q r b w ra ba wa : Nat} (labels : List α)
    (word : α → Fin w → Bool) (hash : Fin r → α → Fin b) (Y : α → W)
    (addr : Fin q → Fin wa → Bool) (X : Fin q → Fin q → W)
    (map : Fin q → Word W w → M (Word W wa))
    (check : Fin ra → Fin ba → Word W wa → M W)
    (layouts : Nat → Layout M W q wa) (e : Nat) (owner : Fin ra) : M W := do
  let raw ← encodeRaw labels word hash Y
  anyFin q (fun col => do
    let ad ← project raw (map col) (fun _ => pure (Ops.const (M := M) (W := W) true)) check
    lookup ad addr (X col) (stages layouts e) check owner)

end Emit

section Semantics
variable {S W : Type} [Inhabited (Ops (StateM S) W)] (v : Sem S W)

theorem raw_or_correct {α : Type} {s : S} (labels : List α) (Y : α → W) (YP : α → Prop)
    (hY : ∀ a, v.rep s (Y a) (YP a)) :
    Good v s
      (reduceF Ops.lor (Ops.const (M := StateM S) (W := W) false) labels (fun a => pure (Y a)))
      (fun t out => v.rep t out (∃ a ∈ labels, YP a)) := by
  apply Good.post v (reduce_correct v labels _ YP Ops.lor Or (fun a b => lor_good v a b)
    (fun a _ t hst => Good.ret v t _ _ (v.stabilize hst (hY a))) _ False (const_false v s))
  intro t out ho
  exact v.congr (by simpa using fold_or_iff labels YP False) ho

theorem encodeRaw_correct {α : Type} {r b w : Nat} {s : S} (labels : List α)
    (word : α → Fin w → Bool) (hash : Fin r → α → Fin b)
    (Y : α → W) (YP : α → Prop) (A : Finset α)
    (hY : ∀ a, v.rep s (Y a) (YP a))
    (hA : ∀ a, a ∈ A ↔ a ∈ labels ∧ YP a) :
    Good v s (encodeRaw labels word hash Y) (fun t sk => ExactSketch v t sk word hash A) := by
  unfold encodeRaw ExactSketch
  apply mkSketch_correct v
  · intro h c t hst
    apply Good.post v
      (raw_or_correct v (labels.filter (fun a => hash h a == c)) Y YP (fun a => v.stabilize hst (hY a)))
    intro u out hu
    apply v.congr _ hu
    simp only [List.mem_filter,beq_iff_eq,active,hA]
    aesop
  · intro h c j z t hst
    apply Good.post v (raw_or_correct v ((labels.filter (fun a => hash h a == c)).filter
      (fun a => word a j == z)) Y YP (fun a => v.stabilize hst (hY a)))
    intro u out hu
    apply v.congr _ hu
    simp only [List.mem_filter,beq_iff_eq,rails,hA]
    aesop

theorem detectGroup_correct {α : Type} {q r b w ra ba wa : Nat} {s : S}
    (labels : List α) (word : α → Fin w → Bool) (hash : Fin r → α → Fin b)
    (Y : α → W) (YP : α → Prop) (A : Finset α)
    (hY : ∀ a, v.rep s (Y a) (YP a)) (hA : ∀ a, a ∈ A ↔ a ∈ labels ∧ YP a)
    (addr : Fin q → Fin wa → Bool) (X : Fin q → Fin q → W) (XP : Fin q → Fin q → Prop)
    (hX : ∀ u a, v.rep s (X u a) (XP u a))
    (mapLabel : Fin q → α → Fin q)
    (map : Fin q → Word W w → StateM S (Word W wa))
    (mapOK : ∀ u, MapCheck v word addr (mapLabel u) (map u))
    (addrHash : Fin ra → Fin q → Fin ba)
    (checks : Fin ra → Fin ba → Word W wa → StateM S W)
    (own : HashCheck v addr addrHash checks)
    (layouts : Nat → Layout (StateM S) W q wa) (mdls : ∀ j, StageModel v addr (layouts j))
    (e : Nat) (owner : Fin ra) (cardA : A.card ≤ 2^e) (perf : Perfect hash A)
    (perfAddr : ∀ B : Finset (Fin q), B.card ≤ 2^e → Perfect addrHash B)
    (family : ∀ n ≤ e, ∀ (B : Finset (Fin q)), halfThreshold n < B.card → B.card ≤ 2^n →
      ∃ I : Finset (Fin q), I ⊆ B ∧ B.card ≤ 2*I.card ∧ ∀ a ∈ I, ∃ h, isolated (mdls n).hash B h a)
    (inj : Function.Injective addr) :
    Good v s (detectGroup labels word hash Y addr X map checks layouts e owner)
      (fun t out => v.rep t out (∃ a ∈ A, ∃ u, XP u (mapLabel u a))) := by
  unfold detectGroup
  apply Good.bind v (encodeRaw_correct v labels word hash Y YP A hY hA)
  intro t raw hst hraw
  have runCols : ∀ u z, v.ext t z → Good v z
        (do let ad ← project raw (map u)
              (fun _ => pure (Ops.const (M := StateM S) (W := W) true)) checks
            lookup ad addr (X u) (stages layouts e) checks owner)
        (fun j out => v.rep j out (∃ a ∈ A, XP u (mapLabel u a))) := by
    intro u z htz
    have hp := project_correct v (ExactSketch.extend v hraw htz) perf
      (mapLabel u) (fun _ => True) (map u) _ checks (mapOK u) own
      (fun _ => True) (fun _ h => h) (fun _ => Iff.rfl)
      (fun zz _ _ _ _ => Good.ret v zz _ _ (const_true v zz))
    apply Good.bind v hp
    intro zz ad hzz had
    let B := transfer A (fun _ => True) (mapLabel u)
    have cardB : B.card ≤ 2^e := (transfer_card A (fun _ => True) (mapLabel u)).trans cardA
    have pp := lookup_correct v (X u) (XP u) layouts mdls checks own e owner perfAddr
      family inj cardB had (fun a => v.stabilize (v.trans hst (v.trans htz hzz)) (hX u a))
    apply Good.post v pp
    intro j out ho
    apply v.congr _ ho
    change (∃ a ∈ transfer A (fun _ => True) (mapLabel u), XP u a) ↔ _
    simp only [mem_transfer]
    aesop
  apply Good.post v (any_correct v _ _ _ runCols)
  intro j out ho
  apply v.congr _ ho
  aesop

end Semantics

section Budgets
variable {M : Type → Type} {W : Type} [Monad M] [Inhabited (Ops M W)] [Inhabited (Budget M)] [Fact (UnitGateBudget M W)]

theorem encodeRaw_cost {α : Type} {r b w : Nat} (labels : List α)
    (word : α → Fin w → Bool) (hash : Fin r → α → Fin b) (Y : α → W) :
    Budget.within (encodeRaw (M := M) labels word hash Y) (r*(labels.length*(1+w*(1+1)))) := by
  let f (ys : List α) : M W := reduceF Ops.lor (Ops.const (M := M) (W := W) false) ys
    (fun a => pure (Y a))
  have hf (ys : List α) : Budget.within (f ys) ys.length := by
    simpa [f] using reduce_cost ys (fun a => pure (Y a)) Ops.lor
      (Ops.const (M := M) (W := W) false) 0 1 (fun a => Budget.ret (Y a)) lor_cost
  unfold encodeRaw mkSketch
  apply tab_uniform
  intro h
  let F (c : Fin b) := labels.filter (fun a => hash h a == c)
  let p (c : Fin b) : M (Cell W w) := do
    let present ← f (F c)
    let code ← tabM w (fun j => do
      let yes ← f ((F c).filter (fun a => word a j == true))
      let no ← f ((F c).filter (fun a => word a j == false))
      pure (yes,no))
    pure (Cell.mk present code)
  have hc (c : Fin b) (j : Fin w) (z : Bool) :
      Budget.within (f ((F c).filter (fun a => word a j == z))) (F c).length :=
    Budget.weaken (hf _) (List.length_filter_le _ _)
  have hl (c : Fin b) : Budget.within (p c) ((F c).length*(1+w*(1+1))) := by
    have hcnt : (F c).length + w*((F c).length+(F c).length) =
        (F c).length*(1+w*(1+1)) := by ring
    rw [←hcnt]
    exact Budget.seq (hf (F c)) (fun present =>
      then_ret (fun out => Cell.mk present out) (tab_uniform w _ _ (fun j =>
        Budget.seq (hc c j true) (fun yes => then_ret (fun no => (yes,no)) (hc c j false)))))
  have ht := tab_cost b p _ hl
  rw [sumFin_mul, length_partition labels (hash h)] at ht
  exact ht

theorem staged_cost {q r b w : Nat} (sk : Sketch W r b w)
    (addr : Fin q → Fin w → Bool) (X : Fin q → W) (layouts : Nat → Layout M W q w)
    (checks : Fin r → Fin b → Word W w → M W) (e : Nat) (bound : Nat)
    (hStep : ∀ k ≤ e, ∀ s, Budget.within (step s addr X (layouts k) checks) bound) :
    Budget.within ((stages layouts e).foldlM (fun src lay => step src addr X lay checks) sk)
      ((e+1)*bound) := by
  induction e generalizing sk with
  | zero =>
    change Budget.within ((step sk addr X (layouts 0) checks) >>= fun s => pure s) _
    simpa using then_ret id (hStep 0 (by simp) sk)
  | succ e ih =>
    change Budget.within ((step sk addr X (layouts (e+1)) checks) >>= fun s =>
      (stages layouts e).foldlM (fun src lay => step src addr X lay checks) s) _
    have hh := Budget.seq (hStep (e+1) (Nat.le_refl _) sk)
      (fun s => ih s (fun j hj => hStep j (hj.trans (Nat.le_succ _))))
    rw [show (e+1+1)*bound = bound+(e+1)*bound by ring]
    exact hh

theorem lookup_uniform_cost {q r b w : Nat} (sk : Sketch W r b w)
    (addr : Fin q → Fin w → Bool) (X : Fin q → W) (layouts : Nat → Layout M W q w)
    (checks : Fin r → Fin b → Word W w → M W) (e : Nat) (owner : Fin r) (bound : Nat)
    (hStep : ∀ k ≤ e, ∀ s, Budget.within (step s addr X (layouts k) checks) bound) :
    Budget.within (lookup sk addr X (stages layouts e) checks owner) ((e+1)*bound+b) := by
  apply Budget.seq (staged_cost sk addr X layouts checks e bound hStep)
  intro final
  simpa using (anyFin_cost b 0 (fun c => pure (final owner c).present)
    (fun c => Budget.ret (final owner c).present))

theorem detectGroup_cost {α : Type} {q r b w ra ba wa : Nat} (labels : List α)
    (word : α → Fin w → Bool) (hash : Fin r → α → Fin b) (Y : α → W)
    (addr : Fin q → Fin wa → Bool) (X : Fin q → Fin q → W)
    (map : Fin q → Word W w → M (Word W wa))
    (checks : Fin ra → Fin ba → Word W wa → M W)
    (layouts : Nat → Layout M W q wa) (e : Nat) (owner : Fin ra)
    (mp own bound : Nat)
    (hMap : ∀ u a, Budget.within (map u a) mp)
    (hOwn : ∀ h c a, Budget.within (checks h c a) own)
    (hStep : ∀ u k, k ≤ e → ∀ s, Budget.within (step s addr (X u) (layouts k) checks) bound) :
    Budget.within (detectGroup labels word hash Y addr X map checks layouts e owner)
      (r*(labels.length*(1+w*(1+1))) +
        q*((projCharge r b ra ba wa mp 0 own+((e+1)*bound+ba))+1)) := by
  apply Budget.seq (encodeRaw_cost labels word hash Y)
  intro raw
  apply anyFin_cost
  intro u
  apply Budget.seq (project_cost raw (map u)
    (fun _ => pure (Ops.const (M := M) (W := W) true)) checks
    mp 0 own (hMap u) (fun _ => Budget.ret _) hOwn)
  intro ad
  exact lookup_uniform_cost ad addr (X u) layouts checks e owner bound (hStep u)

end Budgets
end Refute2003.BundleBuild

namespace Refute2003.Outer

noncomputable section

variable {Point Line Chart Bucket : Type*}
variable [DecidableEq Line] [DecidableEq Bucket]

set_option maxHeartbeats 600000 in
def edge (inc : Point → Line → Prop) (X : Finset Point) (Y : Finset Line) : Prop :=
  ∃ p ∈ X, ∃ ℓ ∈ Y, inc p ℓ

set_option maxHeartbeats 600000 in
theorem edge_mono_y (inc : Point → Line → Prop) {X : Finset Point}
    {Y Z : Finset Line} (hsub : Y ⊆ Z) (he : edge inc X Y) : edge inc X Z := by
  rcases he with ⟨p, hp, ℓ, hℓ, hpl⟩
  exact ⟨p, hp, ℓ, hsub hℓ, hpl⟩

set_option maxHeartbeats 600000 in
def bucket (h : Chart → Line → Bucket) (i : Chart) (b : Bucket)
    (Y : Finset Line) : Finset Line :=
  Y.filter (fun ℓ => h i ℓ = b)

set_option maxHeartbeats 600000 in
theorem bucket_subset (h : Chart → Line → Bucket) (i : Chart) (b : Bucket)
    (Y : Finset Line) : bucket h i b Y ⊆ Y := by
  intro ℓ hℓ
  exact (Finset.mem_filter.mp hℓ).1

set_option maxHeartbeats 600000 in
theorem mem_own_bucket (h : Chart → Line → Bucket) (i : Chart)
    {Y : Finset Line} {ℓ : Line} (hℓ : ℓ ∈ Y) : ℓ ∈ bucket h i (h i ℓ) Y :=
  Finset.mem_filter.mpr ⟨hℓ, rfl⟩

set_option maxHeartbeats 600000 in
def light (h : Chart → Line → Bucket) (T : ℕ) (i : Chart)
    (Y : Finset Line) : Finset Line :=
  Y.filter (fun ℓ => (bucket h i (h i ℓ) Y).card ≤ T)

set_option maxHeartbeats 600000 in
def GoodFamily (h : Chart → Line → Bucket) (q T : ℕ) : Prop :=
  ∀ (Y : Finset Line), Y.Nonempty → Y.card ≤ q →
    ∃ i, Y.card ≤ 2 * (light h T i Y).card

set_option maxHeartbeats 600000 in
structure DetectorSpec (h : Chart → Line → Bucket) (inc : Point → Line → Prop)
    (T : ℕ) (D : Chart → Bucket → Finset Point → Finset Line → Bool) : Prop where
  complete : ∀ i b X Y, (∀ ℓ ∈ Y, h i ℓ = b) → edge inc X Y → D i b X Y = true
  sound : ∀ i b X Y, (∀ ℓ ∈ Y, h i ℓ = b) → Y.card ≤ T →
    ¬ edge inc X Y → D i b X Y = false

set_option maxHeartbeats 600000 in
def step (h : Chart → Line → Bucket)
    (D : Chart → Bucket → Finset Point → Finset Line → Bool)
    (X : Finset Point) (Y : Finset Line) : Finset Line := by
  classical
  exact Y.filter (fun ℓ => ∀ i, D i (h i ℓ) X (bucket h i (h i ℓ) Y) = true)

set_option maxHeartbeats 600000 in
theorem step_mem_iff (h : Chart → Line → Bucket)
    (D : Chart → Bucket → Finset Point → Finset Line → Bool)
    (X : Finset Point) (Y : Finset Line) (ℓ : Line) :
    ℓ ∈ step h D X Y ↔ ℓ ∈ Y ∧
      ∀ i, D i (h i ℓ) X (bucket h i (h i ℓ) Y) = true := by
  classical
  simp only [step, Finset.mem_filter]

set_option maxHeartbeats 600000 in
theorem step_subset (h : Chart → Line → Bucket)
    (D : Chart → Bucket → Finset Point → Finset Line → Bool)
    (X : Finset Point) (Y : Finset Line) : step h D X Y ⊆ Y := by
  intro ℓ hℓ
  exact ((step_mem_iff h D X Y ℓ).mp hℓ).1

set_option maxHeartbeats 600000 in
theorem step_keeps_line (h : Chart → Line → Bucket)
    {D : Chart → Bucket → Finset Point → Finset Line → Bool}
    {inc : Point → Line → Prop} {T : ℕ}
    (Dspec : DetectorSpec h inc T D) {X : Finset Point} {Y : Finset Line}
    {p : Point} {ℓ : Line} (hp : p ∈ X) (hℓ : ℓ ∈ Y) (he : inc p ℓ) :
    ℓ ∈ step h D X Y := by
  apply (step_mem_iff h D X Y ℓ).mpr
  refine ⟨hℓ, ?_⟩
  intro i
  apply Dspec.complete
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · exact ⟨p, hp, ℓ, mem_own_bucket h i hℓ, he⟩

set_option maxHeartbeats 600000 in
theorem half_step (h : Chart → Line → Bucket)
    {D : Chart → Bucket → Finset Point → Finset Line → Bool}
    {inc : Point → Line → Prop} {q T : ℕ}
    (Dspec : DetectorSpec h inc T D) (Hspec : GoodFamily h q T)
    {X : Finset Point} {Y : Finset Line} (hcap : Y.card ≤ q)
    (hneg : ¬ edge inc X Y) : 2 * (step h D X Y).card ≤ Y.card := by
  classical
  by_cases hy : Y.Nonempty
  · obtain ⟨i, hi⟩ := Hspec Y hy hcap
    have hd : Disjoint (light h T i Y) (step h D X Y) := by
      apply Finset.disjoint_left.mpr
      intro ℓ hl hs
      have hlt : (bucket h i (h i ℓ) Y).card ≤ T := (Finset.mem_filter.mp hl).2
      have htest : D i (h i ℓ) X (bucket h i (h i ℓ) Y) = true :=
        ((step_mem_iff h D X Y ℓ).mp hs).2 i
      have hnot : D i (h i ℓ) X (bucket h i (h i ℓ) Y) = false := by
        apply Dspec.sound
        · intro u hu
          exact (Finset.mem_filter.mp hu).2
        · exact hlt
        · intro hu
          exact hneg (edge_mono_y inc (bucket_subset h i (h i ℓ) Y) hu)
      simp [hnot] at htest
    have hu : light h T i Y ∪ step h D X Y ⊆ Y := by
      intro ℓ hℓ
      rcases Finset.mem_union.mp hℓ with hl | hs
      · exact (Finset.mem_filter.mp hl).1
      · exact step_subset h D X Y hs
    have hc := Finset.card_le_card hu
    rw [Finset.card_union_of_disjoint hd] at hc
    omega
  · have hY : Y = ∅ := by simpa using hy
    subst Y
    simp [step]

set_option maxHeartbeats 600000 in
def iterate (h : Chart → Line → Bucket)
    (D : Chart → Bucket → Finset Point → Finset Line → Bool)
    (X : Finset Point) (Y : Finset Line) : ℕ → Finset Line
  | 0 => Y
  | j + 1 => step h D X (iterate h D X Y j)

set_option maxHeartbeats 600000 in
theorem iterate_subset (h : Chart → Line → Bucket)
    (D : Chart → Bucket → Finset Point → Finset Line → Bool)
    (X : Finset Point) (Y : Finset Line) (j : ℕ) :
    iterate h D X Y j ⊆ Y := by
  induction j with
  | zero => intro ℓ hℓ; exact hℓ
  | succ j ih =>
    exact (step_subset h D X (iterate h D X Y j)).trans ih

set_option maxHeartbeats 600000 in
theorem iterate_keeps_line (h : Chart → Line → Bucket)
    {D : Chart → Bucket → Finset Point → Finset Line → Bool}
    {inc : Point → Line → Prop} {T : ℕ} (Dspec : DetectorSpec h inc T D)
    {X : Finset Point} {Y : Finset Line} {p : Point} {ℓ : Line}
    (hp : p ∈ X) (hℓ : ℓ ∈ Y) (he : inc p ℓ) (j : ℕ) :
    ℓ ∈ iterate h D X Y j := by
  induction j with
  | zero => exact hℓ
  | succ j ih =>
    exact step_keeps_line h Dspec hp ih he

set_option maxHeartbeats 600000 in
theorem iteration_bound (h : Chart → Line → Bucket)
    {D : Chart → Bucket → Finset Point → Finset Line → Bool}
    {inc : Point → Line → Prop} {q T : ℕ}
    (Dspec : DetectorSpec h inc T D) (Hspec : GoodFamily h q T)
    {X : Finset Point} {Y : Finset Line} (hcap : Y.card ≤ q)
    (hneg : ¬ edge inc X Y) (j : ℕ) :
    2 ^ j * (iterate h D X Y j).card ≤ Y.card := by
  induction j with
  | zero => simp [iterate]
  | succ j ih =>
    let Z := iterate h D X Y j
    have hzsub : Z ⊆ Y := iterate_subset h D X Y j
    have hzcap : Z.card ≤ q := (Finset.card_le_card hzsub).trans hcap
    have hzneg : ¬ edge inc X Z := fun he => hneg (edge_mono_y inc hzsub he)
    have hh := half_step h Dspec Hspec hzcap hzneg
    calc
      2 ^ (j+1) * (iterate h D X Y (j+1)).card =
          2 ^ j * (2 * (step h D X Z).card) := by
            simp only [pow_succ, Nat.mul_assoc, iterate, Z]
      _ ≤ 2 ^ j * Z.card := Nat.mul_le_mul_left _ hh
      _ ≤ Y.card := ih

set_option maxHeartbeats 600000 in
theorem iteration_empty (h : Chart → Line → Bucket)
    {D : Chart → Bucket → Finset Point → Finset Line → Bool}
    {inc : Point → Line → Prop} {q T : ℕ}
    (Dspec : DetectorSpec h inc T D) (Hspec : GoodFamily h q T)
    {X : Finset Point} {Y : Finset Line} (hcap : Y.card ≤ q)
    (hneg : ¬ edge inc X Y) {j : ℕ} (hsteps : q < 2 ^ j) :
    iterate h D X Y j = ∅ := by
  classical
  by_contra hn
  have hp : 1 ≤ (iterate h D X Y j).card :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hn)
  have hle : 2 ^ j ≤ 2 ^ j * (iterate h D X Y j).card := by
    simpa using Nat.mul_le_mul_left (2 ^ j) hp
  exact (Nat.not_le_of_gt hsteps)
    (hle.trans ((iteration_bound h Dspec Hspec hcap hneg j).trans hcap))

set_option maxHeartbeats 600000 in
def accept (h : Chart → Line → Bucket)
    (D : Chart → Bucket → Finset Point → Finset Line → Bool)
    (X : Finset Point) (Y : Finset Line) (j : ℕ) : Bool := by
  classical
  exact decide ((iterate h D X Y j).Nonempty)

set_option maxHeartbeats 600000 in
theorem accept_true (h : Chart → Line → Bucket)
    {D : Chart → Bucket → Finset Point → Finset Line → Bool}
    {inc : Point → Line → Prop} {T : ℕ} (Dspec : DetectorSpec h inc T D)
    {X : Finset Point} {Y : Finset Line} (he : edge inc X Y) (j : ℕ) :
    accept h D X Y j = true := by
  classical
  rcases he with ⟨p, hp, ℓ, hℓ, hpℓ⟩
  have hne : (iterate h D X Y j).Nonempty :=
    ⟨ℓ, iterate_keeps_line h Dspec hp hℓ hpℓ j⟩
  simp [accept, hne]

set_option maxHeartbeats 600000 in
theorem accept_false (h : Chart → Line → Bucket)
    {D : Chart → Bucket → Finset Point → Finset Line → Bool}
    {inc : Point → Line → Prop} {q T : ℕ}
    (Dspec : DetectorSpec h inc T D) (Hspec : GoodFamily h q T)
    {X : Finset Point} {Y : Finset Line} (hcap : Y.card ≤ q)
    (hneg : ¬ edge inc X Y) {j : ℕ} (hsteps : q < 2 ^ j) :
    accept h D X Y j = false := by
  classical
  simp [accept, iteration_empty h Dspec Hspec hcap hneg hsteps]

end

end Refute2003.Outer

namespace Refute2003.OuterCharts

open scoped BigOperators
open Function

noncomputable section

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

set_option maxHeartbeats 600000 in
abbrev Coloring (Line : Type*) (G : ℕ) := Line → Fin G

set_option maxHeartbeats 600000 in
def witness (S : Finset Line) (r b G : ℕ) (f : Coloring Line G) : Prop :=
  ∃ A ∈ S.powersetCard r, ∃ B : Fin b → Fin G, ∀ a ∈ A, ∃ i, B i = f a

set_option maxHeartbeats 600000 in
def witness' (S : Finset Line) (r b G : ℕ) (f : Coloring Line G) : Bool := by
  classical
  exact decide (witness S r b G f)

set_option maxHeartbeats 600000 in
abbrev Encoding (S : Finset Line) (r b G : ℕ) :=
  Σ A : ↥(S.powersetCard r),
    (Fin b → Fin G) × (↥A.val → Fin b) × ({a : Line // a ∉ A.val} → Fin G)

set_option maxHeartbeats 600000 in
def decode {S : Finset Line} {r b G : ℕ} (e : Encoding S r b G) :
    Coloring Line G :=
  fun a => if ha : a ∈ e.1.val then e.2.1 (e.2.2.1 ⟨a, ha⟩)
    else e.2.2.2 ⟨a, ha⟩

set_option maxHeartbeats 600000 in
theorem decode_of_witness {S : Finset Line} {r b G : ℕ} {f : Coloring Line G}
    (hw : witness S r b G f) : ∃ e : Encoding S r b G, decode e = f := by
  classical
  rcases hw with ⟨A, hA, B, hB⟩
  have hselector : ∀ a : ↥A, ∃ i, B i = f a := fun a => hB a a.property
  choose sel hsel using hselector
  let enc : Encoding S r b G := ⟨⟨A,hA⟩, B, sel, fun a => f a⟩
  refine ⟨enc, ?_⟩
  funext a
  by_cases ha : a ∈ A
  · simpa [decode, enc, ha] using hsel ⟨a, ha⟩
  · simp [decode, enc, ha]

set_option maxHeartbeats 600000 in
theorem cardinal_witness (S : Finset Line) (r b G : ℕ) :
    Fintype.card {f : Coloring Line G // witness' S r b G f = true} ≤
      2 ^ S.card * (G ^ b * (b ^ r * G ^ (Fintype.card Line - r))) := by
  classical
  have he : ∀ f : {f : Coloring Line G // witness' S r b G f = true},
      ∃ e : Encoding S r b G, decode e = f.val :=
    fun f => decode_of_witness (by simpa [witness'] using f.property)
  choose enc henc using he
  have hI : Injective enc := by
    intro f f' heq
    apply Subtype.ext
    exact (henc f).symm.trans ((congrArg decode heq).trans (henc f'))
  have hcard := Fintype.card_le_of_injective enc hI
  let W := G ^ b * (b ^ r * G ^ (Fintype.card Line - r))
  have hencCard : Fintype.card (Encoding S r b G) = (S.powersetCard r).card * W := by
    rw [Fintype.card_sigma]
    calc
      _ = ∑ _A : ↥(S.powersetCard r), W := by
        apply Finset.sum_congr rfl
        intro A hA
        have hAr : A.val.card = r := (Finset.mem_powersetCard.mp A.property).2
        have hcomp : Fintype.card {a : Line // a ∉ A.val} = Fintype.card Line - r := by
          rw [Fintype.card_subtype_compl, Fintype.card_coe, hAr]
        simp [W, Fintype.card_prod, Fintype.card_fun, hcomp, hAr]
      _ = _ := by simp
  have hsubset : S.powersetCard r ⊆ S.powerset := by
    intro A ha
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp ha).1
  have hpow : (S.powersetCard r).card ≤ 2 ^ S.card := by
    simpa only [Finset.card_powerset] using Finset.card_le_card hsubset
  rw [hencCard] at hcard
  exact hcard.trans (Nat.mul_le_mul_right W hpow)

set_option maxHeartbeats 600000 in
def low (S : Finset Line) (T G : ℕ) (f : Coloring Line G) : Finset Line :=
  S.filter (fun a => (S.filter (fun x => f x = f a)).card ≤ T)

set_option maxHeartbeats 600000 in
def bad (S : Finset Line) (T G : ℕ) (f : Coloring Line G) : Bool :=
  decide (2 * (low S T G f).card < S.card)

set_option maxHeartbeats 600000 in
theorem many_in_few_of_bad (S : Finset Line) (T G : ℕ)
    (f : Coloring Line G) (hb : bad S T G f = true)
    (hG : S.card / (T+1) ≤ G) :
    witness S ((S.card+1)/2) (S.card/(T+1)) G f := by
  classical
  have hbad : 2 * (low S T G f).card < S.card := by simpa [bad] using hb
  let H := S \ low S T G f
  let F := H.image f
  have hsub : low S T G f ⊆ S := Finset.filter_subset _ _
  have hsize : H.card + (low S T G f).card = S.card :=
    Finset.card_sdiff_add_card_eq_card hsub
  have hHa : ∀ a ∈ H, T < (S.filter (fun x => f x = f a)).card := by
    intro a ha
    have ha' := Finset.mem_sdiff.mp ha
    apply Nat.lt_of_not_ge
    intro hf
    exact ha'.2 (Finset.mem_filter.mpr ⟨ha'.1, hf⟩)
  have hfiber : ∀ c ∈ F, T+1 ≤ (H.filter (fun x => f x = c)).card := by
    intro c hc
    obtain ⟨a, ha, hac⟩ := Finset.mem_image.mp hc
    have heq : H.filter (fun x => f x = c) = S.filter (fun x => f x = c) := by
      ext u
      constructor
      · intro hu
        have hm := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hm.1).1, hm.2⟩
      · intro hu
        have hm := Finset.mem_filter.mp hu
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_sdiff.mpr ⟨hm.1, ?_⟩, hm.2⟩
        intro huL
        have hsmall := (Finset.mem_filter.mp huL).2
        rw [hm.2, ← hac] at hsmall
        exact (Nat.not_le_of_gt (hHa a ha)) hsmall
    rw [heq, ← hac]
    exact Nat.succ_le_of_lt (hHa a ha)
  have hprod : F.card * (T+1) ≤ H.card := by
    calc
      F.card * (T+1) = ∑ _c ∈ F, (T+1) := by simp
      _ ≤ ∑ c ∈ F, (H.filter (fun x => f x = c)).card := Finset.sum_le_sum hfiber
      _ = H.card := (Finset.card_eq_sum_card_image f H).symm
  have hF : F.card ≤ S.card/(T+1) := by
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos T)).mpr
    exact hprod.trans (by omega)
  have hR : (S.card+1)/2 ≤ H.card := by omega
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq hR
  have hAs : A ⊆ S := hA.trans (Finset.sdiff_subset)
  obtain ⟨B, hB, hBc⟩ := Finset.exists_superset_card_eq hF (by simpa using hG)
  let Bvec : Fin (S.card/(T+1)) → Fin G :=
    fun i => ((B.equivFinOfCardEq hBc).symm i).val
  refine ⟨A, Finset.mem_powersetCard.mpr ⟨hAs,hAc⟩, Bvec, ?_⟩
  intro a ha
  have hm : f a ∈ B := hB (Finset.mem_image.mpr ⟨a,hA ha,rfl⟩)
  refine ⟨B.equivFinOfCardEq hBc ⟨f a, hm⟩, ?_⟩
  simp [Bvec]

set_option maxHeartbeats 600000 in
theorem bad_count_scaled (S : Finset Line) (T g : ℕ)
    (hg : 6 ≤ g) (hT : g ≤ T+1) (hB : S.card/(T+1) ≤ 2 ^ (g-6)) :
    2 ^ S.card * Fintype.card {f : Coloring Line (2^g) // bad S T (2^g) f = true}
      ≤ (2^g) ^ Fintype.card Line := by
  classical
  let k := S.card
  let r := (k+1)/2
  let b := k/(T+1)
  let N := Fintype.card Line
  have hbG : b ≤ 2^g := hB.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hinj : Injective
      (fun f : {f : Coloring Line (2^g) // bad S T (2^g) f = true} =>
        (⟨f.val, by
          simpa [witness'] using many_in_few_of_bad S T (2^g) f.val f.property hbG⟩ :
          { f : Coloring Line (2^g) // witness' S r b (2^g) f = true })) := by
    intro x y hxy
    have hv := congrArg (fun u : { f : Coloring Line (2^g) // witness' S r b (2^g) f = true }
      => u.val) hxy
    exact Subtype.ext hv
  have hCount := (Fintype.card_le_of_injective _ hinj).trans
    (cardinal_witness S r b (2^g))
  have hgb : g*b ≤ k :=
    (Nat.mul_le_mul_right b hT).trans (by
      change (T+1)*(k/(T+1)) ≤ k
      rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _)
  have hrN : r ≤ N := by
    have hkN : k ≤ N := Finset.card_le_univ S
    dsimp [r]
    omega
  have hr2 : k ≤ 2*r := by dsimp [r]; omega
  have h_exp : k + (k + (g*b + ((g-6)*r + g*(N-r)))) ≤ g*N := by
    have h1 : (g-6)*r + 6*r = g*r := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hg]
    have h2 : g*r + g*(N-r) = g*N := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hrN]
    omega
  calc
    _ ≤ 2^k * (2^k * ((2^g)^b * (b^r * (2^g)^(N-r)))) :=
      Nat.mul_le_mul_left _ hCount
    _ ≤ 2^k * (2^k * ((2^g)^b * ((2^(g-6))^r * (2^g)^(N-r)))) := by
      gcongr
    _ = 2 ^ (k + (k + (g*b + ((g-6)*r + g*(N-r))))) := by
      simp only [← pow_mul, ← pow_add]
    _ ≤ 2^(g*N) := Nat.pow_le_pow_right (by decide) h_exp
    _ = _ := by rw [pow_mul]

end

end Refute2003.OuterCharts

namespace Refute2003.OuterCharts

open scoped BigOperators
noncomputable section

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

set_option maxHeartbeats 600000 in
theorem exists_good_charts (q T g L B : ℕ)
    (hg : 6 ≤ g) (hT : g ≤ T+1)
    (hG : q ≤ (T+1)*2^(g-6))
    (hN : Fintype.card Line ≤ 2^L) (hq : q < 2^B) :
    ∃ H : Fin (L+B) → Line → Fin (2^g), Refute2003.Outer.GoodFamily H q T := by
  classical
  let K : Fin q → Type _ :=
    fun j => ↥((Finset.univ : Finset Line).powersetCard (j.val+1))
  let w : Fin q → ℕ := fun j => j.val+1
  let Bad : (j : Fin q) → K j → Coloring Line (2^g) → Bool :=
    fun _ A f => bad A.val T (2^g) f
  letI : Nonempty (Coloring Line (2^g)) :=
    ⟨fun _ => ⟨0, by positivity⟩⟩
  have hW : ∀ j, 1 ≤ w j := by intro j; simp [w]
  have hK : ∀ j, Fintype.card (K j) ≤ (2^L)^(w j) := by
    intro j
    simp only [K, w, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ]
    exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hN _)
  have hs : ∀ j A, 2^(w j) *
      Fintype.card (Refute2003.HashCounting.BadChoice (Bad j) A) ≤
        Fintype.card (Coloring Line (2^g)) := by
    intro j A
    have hcard : A.val.card = w j := (Finset.mem_powersetCard.mp A.property).2
    have hcap : A.val.card ≤ q := by
      rw [hcard]
      exact Nat.succ_le_of_lt j.isLt
    have hb : A.val.card/(T+1) ≤ 2^(g-6) := by
      apply Nat.le_of_mul_le_mul_right _ (Nat.succ_pos T)
      exact (Nat.div_mul_le_self _ _).trans (hcap.trans (by simpa [Nat.mul_comm] using hG))
    simpa [Bad, Refute2003.HashCounting.BadChoice, Coloring, hcard, Fintype.card_fun]
      using bad_count_scaled A.val T g hg hT hb
  obtain ⟨H,hH⟩ := Refute2003.HashCounting.exists_family_weighted K Bad w L B hW hK hs
    (by simpa using hq)
  refine ⟨H, ?_⟩
  intro S hSn hSc
  have hpos : 0 < S.card := Finset.card_pos.mpr hSn
  let j : Fin q := ⟨S.card-1, by omega⟩
  have hj : w j = S.card := by dsimp [w,j]; omega
  let A : K j := ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hj.symm⟩⟩
  obtain ⟨i,hi⟩ := hH j A
  refine ⟨i, ?_⟩
  have hh : ¬ (2*(low S T (2^g) (H i)).card < S.card) := by
    simpa [Bad, A, bad] using hi
  have hl : low S T (2^g) (H i) = Refute2003.Outer.light H T i S := by
    unfold low Refute2003.Outer.light
    apply Finset.filter_congr
    intro a ha
    unfold Refute2003.Outer.bucket
    apply Iff.of_eq
    congr 2
  rw [← hl]
  exact Nat.le_of_not_gt hh

end

end Refute2003.OuterCharts

namespace Refute2003.Budget

set_option maxHeartbeats 600000 in
private theorem square_le_expAux (j : ℕ) : (4+j)^2 ≤ 2^(4+j) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    calc
      (4+(j+1))^2 ≤ 2*(4+j)^2 := by nlinarith [Nat.zero_le j, Nat.zero_le (j ^ 2)]
      _ ≤ 2*2^(4+j) := Nat.mul_le_mul_left _ ih
      _ = 2^(4+(j+1)) := by
        rw [show 4+(j+1) = (4+j)+1 by omega, pow_succ]
        exact Nat.mul_comm _ _

set_option maxHeartbeats 600000 in
private theorem square_le_exp (m : ℕ) (hm : 4 ≤ m) : m^2 ≤ 2^m := by
  have h := square_le_expAux (m-4)
  simpa [Nat.add_sub_of_le hm] using h

set_option maxHeartbeats 600000 in
theorem exists_exp_dominates (C d K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ C*(k+1)^d < 2^k := by
  let m := C+d+K+10
  let k := 2^m
  have hm4 : 4 ≤ m := by dsimp [m]; omega
  have hk : m^2 ≤ k := square_le_exp m hm4
  have hKm : K ≤ m := by dsimp [m]; omega
  have hCm : C ≤ m := by dsimp [m]; omega
  have hdm : d+2 ≤ m := by dsimp [m]; omega
  have hmself : m ≤ k := Nat.lt_two_pow_self.le
  have hlin : C+(m+1)*d < k := by
    have haux := Nat.mul_le_mul_right (m+1) hdm
    nlinarith
  have hC : C ≤ 2^C := Nat.lt_two_pow_self.le
  have hk1 : k+1 ≤ 2^(m+1) := by
    dsimp [k]
    rw [Nat.two_pow_succ m]
    have : 1 ≤ 2^m := Nat.one_le_two_pow
    omega
  refine ⟨k, hKm.trans hmself, ?_⟩
  calc
    C*(k+1)^d ≤ 2^C*(2^(m+1))^d := by gcongr
    _ = 2 ^ (C+(m+1)*d) := by rw [← pow_mul, ← pow_add]
    _ < 2^k := Nat.pow_lt_pow_right (by decide) hlin

set_option maxHeartbeats 600000 in
def q (k : ℕ) : ℕ := 2^(20*k)
set_option maxHeartbeats 600000 in
def cap (k : ℕ) : ℕ := 2^k
set_option maxHeartbeats 600000 in
def bins (k : ℕ) : ℕ := 2^(19*k+6)
set_option maxHeartbeats 600000 in
def charts (k : ℕ) : ℕ := 100*(k+1)
set_option maxHeartbeats 600000 in
def rounds (k : ℕ) : ℕ := 20*k+1
set_option maxHeartbeats 600000 in
def nPlane (k : ℕ) : ℕ := (q k)^2+q k+1

set_option maxHeartbeats 600000 in
def phaseUnits (k : ℕ) : ℕ :=
  bins k * ((q k)^2 + q k * (cap k)^8) + (q k)^2*cap k + (q k)^2

set_option maxHeartbeats 600000 in
def totalUnits (k C d : ℕ) : ℕ :=
  C*(k+1)^d*(charts k*rounds k*phaseUnits k + (q k)^2)

set_option maxHeartbeats 600000 in
theorem q_lt_round_power (k : ℕ) : q k < 2^(rounds k) := by
  exact Nat.pow_lt_pow_right (by decide) (by simp [rounds])

set_option maxHeartbeats 600000 in
theorem q_large (k : ℕ) (hk : 1 ≤ k) : 100 < q k := by
  have hpow : 2^20 ≤ 2^(20*k) := Nat.pow_le_pow_right (by decide) (by omega)
  exact (by decide : 100 < 2^20).trans_le hpow

set_option maxHeartbeats 600000 in
theorem chart_count_bound (k : ℕ) : phaseUnits k ≤ 256*2^(59*k) := by
  have h0 : (q k)^2 = 2^(40*k) := by
    unfold q
    rw [← pow_mul]
    congr 1
    omega
  have h1 : q k * (cap k)^8 = 2^(28*k) := by
    unfold cap q
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have h2 : (q k)^2*cap k = 2^(41*k) := by
    rw [h0]
    unfold cap
    rw [← pow_add]
    congr 1
    omega
  have hG : bins k = 64*2^(19*k) := by
    unfold bins
    rw [pow_add]
    norm_num [Nat.mul_comm]
  rw [phaseUnits, h2, h0, h1, hG]
  have hA : 2^(19*k) * 2^(40*k) = 2^(59*k) := by
    rw [← pow_add]
    congr 1
    omega
  have hB : 2^(19*k) * 2^(28*k) = 2^(47*k) := by
    rw [← pow_add]
    congr 1
    omega
  have hle47 : 2^(47*k) ≤ 2^(59*k) := Nat.pow_le_pow_right (by decide) (by omega)
  have hle41 : 2^(41*k) ≤ 2^(59*k) := Nat.pow_le_pow_right (by decide) (by omega)
  have hle40 : 2^(40*k) ≤ 2^(59*k) := Nat.pow_le_pow_right (by decide) (by omega)
  calc
    _ = 64*(2^(59*k) + 2^(47*k)) + 2^(41*k) + 2^(40*k) := by
      rw [Nat.mul_assoc, Nat.mul_add, hA, hB]
    _ ≤ 64*(2^(59*k) + 2^(59*k)) + 2^(59*k) + 2^(59*k) := by gcongr
    _ ≤ _ := by omega

set_option maxHeartbeats 600000 in
theorem total_bound (k C d : ℕ) :
    totalUnits k C d ≤ (2^20*C)*(k+1)^(d+2)*2^(59*k) := by
  have hr : rounds k ≤ 21*(k+1) := by unfold rounds; omega
  have hq2 : (q k)^2 ≤ 2^(59*k) := by
    unfold q
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  unfold totalUnits
  calc
    _ ≤ C*(k+1)^d*(100*(k+1)*(21*(k+1))*(256*2^(59*k))+2^(59*k)) := by
      unfold charts
      gcongr
      exact chart_count_bound k
    _ ≤ C*(k+1)^d*(100*(k+1)*(21*(k+1))*(256*2^(59*k))
                    + (k+1)^2*2^(59*k)) := by
      gcongr
      simpa using (Nat.mul_le_mul_right (2^(59*k)) (Nat.one_le_pow 2 (k+1) (by omega)))
    _ = (537601*C)*(k+1)^(d+2)*2^(59*k) := by
      rw [pow_add]
      ring
    _ ≤ _ := by gcongr <;> norm_num

set_option maxHeartbeats 600000 in
theorem exists_small_total (C d K : ℕ) :
    ∃ k, max K 8 ≤ k ∧ 100*totalUnits k C d < q k * nPlane k := by
  obtain ⟨k,hk,hsmall⟩ := exists_exp_dominates (100*2^20*C) (d+2) (max K 8)
  refine ⟨k,hk,?_⟩
  calc
    100*totalUnits k C d ≤ 100*((2^20*C)*(k+1)^(d+2)*2^(59*k)) :=
      Nat.mul_le_mul_left _ (total_bound k C d)
    _ = ((100*2^20*C)*(k+1)^(d+2))*2^(59*k) := by ring
    _ < 2^k*2^(59*k) := Nat.mul_lt_mul_of_pos_right hsmall (by positivity)
    _ = q k * (q k)^2 := by
      unfold q
      rw [← pow_add, ← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ q k*nPlane k := by
      unfold nPlane
      exact Nat.mul_le_mul_left _ (by omega)

end Refute2003.Budget

namespace Refute2003.OuterCode

open BundleBuild
noncomputable section

section Emit
variable {M : Type → Type} {α W : Type} [Monad M] [Inhabited (Ops M W)]
variable {n R G : ℕ}

set_option maxHeartbeats 600000 in
abbrev Detect (M : Type → Type) (α W : Type) (R G : ℕ) :=
  (α → W) → Fin R → Fin G → M W

set_option maxHeartbeats 600000 in
def round (scan : Fin n ≃ α) (h : Fin R → α → Fin G)
    (D : Detect M α W R G) (Y : α → W) : M (α → W) := do
  let outputs ← tabM R (fun i => tabM G (D Y i))
  let next ← tabM n (fun j => do
    let all ← allFin R (fun i => pure (outputs i (h i (scan j))))
    Ops.land (Y (scan j)) all)
  pure (next ∘ scan.symm)

set_option maxHeartbeats 600000 in
def iterate (scan : Fin n ≃ α) (h : Fin R → α → Fin G)
    (D : Detect M α W R G) : ℕ → (α → W) → M (α → W)
  | 0, Y => pure Y
  | j+1, Y => do
    let Z ← iterate scan h D j Y
    round scan h D Z

set_option maxHeartbeats 600000 in
def accept (scan : Fin n ≃ α) (h : Fin R → α → Fin G)
    (D : Detect M α W R G) (j : ℕ) (Y : α → W) : M W := do
  let Z ← iterate scan h D j Y
  anyFin n (fun a => pure (Z (scan a)))

end Emit

section CoreSemantics
variable {α S W : Type} [DecidableEq α] [Inhabited (Ops (StateM S) W)] (v : Sem S W)
variable {n R G q T : ℕ}

set_option maxHeartbeats 600000 in
def VecRep (t : S) (Y : α → W) (A : Finset α) : Prop :=
  ∀ a, v.rep t (Y a) (a ∈ A)

set_option maxHeartbeats 600000 in
def hit (A : Finset α) (p : α → Prop) : Prop := ∃ a ∈ A, p a

set_option maxHeartbeats 600000 in
theorem hit_mono {A B : Finset α} {p : α → Prop} (h : A ⊆ B) (yes : hit A p) :
    hit B p := by
  rcases yes with ⟨a, ha, hp⟩
  exact ⟨a, h ha, hp⟩

set_option maxHeartbeats 600000 in
def DetectorOK (h : Fin R → α → Fin G) (p : α → Prop) (T : ℕ)
    (D : Detect (StateM S) α W R G) : Prop :=
  ∀ (s : S) (Y : α → W) (A : Finset α), VecRep v s Y A →
    ∀ i b, Good v s (D Y i b) (fun t w =>
      ∃ P : Prop, v.rep t w P ∧ ((Outer.bucket h i b A).card ≤ T →
        (P ↔ hit (Outer.bucket h i b A) p)))

set_option maxHeartbeats 600000 in
def progress (p : α → Prop) (q T f : ℕ) (A B : Finset α) : Prop :=
  B ⊆ A ∧
  (A.card ≤ T → ∀ a ∈ A, p a → a ∈ B) ∧
  (A.card ≤ q → ¬ hit A p → f*B.card ≤ A.card)

set_option maxHeartbeats 600000 in
theorem round_good (scan : Fin n ≃ α) (h : Fin R → α → Fin G)
    {D : Detect (StateM S) α W R G} {p : α → Prop}
    (hd : DetectorOK v h p T D) (hh : Outer.GoodFamily h q T)
    {s : S} {Y : α → W} {A : Finset α} (hy : VecRep v s Y A) :
    Good v s (round scan h D Y) (fun t out =>
      ∃ B, VecRep v t out B ∧ progress p q T 2 A B) := by
  classical
  unfold round
  let test (i : Fin R) (b : Fin G) (t : S) (w : W) :=
    ∃ P : Prop, v.rep t w P ∧ ((Outer.bucket h i b A).card ≤ T →
      (P ↔ hit (Outer.bucket h i b A) p))
  have ht (i : Fin R) (b : Fin G) (t u : S) (w : W) (hTU : v.ext t u)
      (hw : test i b t w) : test i b u w := by
    rcases hw with ⟨P,hP,hf⟩
    exact ⟨P,v.stabilize hTU hP,hf⟩
  have hog (i : Fin R) (t : S) (hst : v.ext s t) :
      Good v t (tabM G (D Y i)) (fun u r => ∀ b, test i b u (r b)) := by
    apply tab_correct v G _ (test i) (ht i)
    intro b u htu
    exact hd u Y A (fun a => v.stabilize (v.trans hst htu) (hy a)) i b
  have hg := tab_correct v R (fun i => tabM G (D Y i))
    (fun i t r => ∀ b, test i b t (r b))
    (fun i t u r e h b => ht i b t u _ e (h b)) hog
  apply Good.bind v hg
  intro t outs hst hout
  have hout' : ∀ i b, ∃ P : Prop, v.rep t (outs i b) P ∧
      ((Outer.bucket h i b A).card ≤ T →
        (P ↔ hit (Outer.bucket h i b A) p)) := hout
  choose P hP hExact using hout'
  let B := A.filter (fun a => ∀ i : Fin R, P i (h i a))
  have hB (a : α) : a ∈ B ↔ a ∈ A ∧ ∀ i : Fin R, P i (h i a) :=
    Finset.mem_filter
  have hBsub : B ⊆ A := fun a ha => ((hB a).mp ha).1
  have hProg : progress p q T 2 A B := by
    refine ⟨hBsub, ?_, ?_⟩
    · intro hsmall a ha hpa
      refine (hB a).mpr ⟨ha, ?_⟩
      intro i
      exact (hExact i (h i a) ((Finset.card_le_card (Outer.bucket_subset h i _ _)).trans hsmall)).mpr
        ⟨a,Outer.mem_own_bucket h i ha,hpa⟩
    · intro hsize hneg
      by_cases hne : A.Nonempty
      · obtain ⟨i,hi⟩ := hh A hne hsize
        have hd : Disjoint (Outer.light h T i A) B := by
          apply Finset.disjoint_left.mpr
          intro a ha hb
          have hl : (Outer.bucket h i (h i a) A).card ≤ T := (Finset.mem_filter.mp ha).2
          exact hneg (hit_mono (Outer.bucket_subset h i _ _) ((hExact i (h i a) hl).mp (((hB a).mp hb).2 i)))
        have hu : Outer.light h T i A ∪ B ⊆ A := by
          intro a ha
          rcases Finset.mem_union.mp ha with hlight | hlast
          · exact (Finset.mem_filter.mp hlight).1
          · exact hBsub hlast
        have hsz := Finset.card_le_card hu
        rw [Finset.card_union_of_disjoint hd] at hsz
        omega
      · have ha : A = ∅ := by simpa using hne
        have hb : B = ∅ := Finset.subset_empty.mp (by simpa [ha] using hBsub)
        simp [ha,hb]
  have hhW (j : Fin n) (u : S) (htu : v.ext t u) :
      Good v u (do
        let all ← allFin R (fun i => pure (outs i (h i (scan j))))
        Ops.land (Y (scan j)) all)
        (fun t' z => v.rep t' z (scan j ∈ B)) := by
    have hall := all_correct v (s := u) R (fun i => pure (outs i (h i (scan j))))
      (fun i => P i (h i (scan j))) (fun i u' huu' =>
        Good.ret v u' _ _ (v.stabilize (v.trans htu huu') (hP i (h i (scan j)))))
    apply Good.bind v hall
    intro u' all huu' ha
    apply Good.post v (land_good v (v.stabilize (v.trans hst (v.trans htu huu')) (hy (scan j))) ha)
    intro u'' a h'
    exact v.congr (hB (scan j)).symm h'
  apply Good.bind v (tab_correct v n _ (fun j u z => v.rep u z (scan j ∈ B))
    (fun j t u z htu hz => v.stabilize htu hz) hhW)
  intro u res htu hres
  apply Good.ret
  refine ⟨B, ?_, hProg⟩
  intro a
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hres (scan.symm a)

set_option maxHeartbeats 600000 in
theorem iterate_good (scan : Fin n ≃ α) (h : Fin R → α → Fin G)
    {D : Detect (StateM S) α W R G} {p : α → Prop}
    (hd : DetectorOK v h p T D) (hh : Outer.GoodFamily h q T)
    (j : ℕ) {s : S} {Y : α → W} {A : Finset α} (hy : VecRep v s Y A) :
    Good v s (iterate scan h D j Y) (fun t out =>
      ∃ B, VecRep v t out B ∧ progress p q T (2^j) A B) := by
  induction j with
  | zero =>
    apply Good.ret
    exact ⟨A, hy, Finset.Subset.refl _, fun _ a ha _ => ha, by simp⟩
  | succ j ih =>
    unfold iterate
    apply Good.bind v ih
    intro t Z hst hhZ
    rcases hhZ with ⟨B,hB,hAB⟩
    apply Good.post v (round_good v scan h hd hh hB)
    intro u out hh'
    rcases hh' with ⟨C,hC,hBC⟩
    refine ⟨C,hC,hBC.1.trans hAB.1, ?_, ?_⟩
    · intro hSmall a ha hpa
      exact hBC.2.1 ((Finset.card_le_card hAB.1).trans hSmall) a
        (hAB.2.1 hSmall a ha hpa) hpa
    · intro hCap hNo
      have hSmall := (Finset.card_le_card hAB.1).trans hCap
      have hNo' : ¬ hit B p := fun hb => hNo (hit_mono hAB.1 hb)
      calc
        2^(j+1)*C.card = 2^j*(2*C.card) := by rw [pow_succ,Nat.mul_assoc]
        _ ≤ 2^j*B.card := Nat.mul_le_mul_left _ (hBC.2.2 hSmall hNo')
        _ ≤ A.card := hAB.2.2 hCap hNo

set_option maxHeartbeats 600000 in
theorem accept_good (scan : Fin n ≃ α) (h : Fin R → α → Fin G)
    {D : Detect (StateM S) α W R G} {p : α → Prop}
    (hd : DetectorOK v h p T D) (hh : Outer.GoodFamily h q T)
    (j : ℕ) {s : S} {Y : α → W} {A : Finset α} (hy : VecRep v s Y A) :
    Good v s (accept scan h D j Y) (fun t out =>
      ∃ B, v.rep t out B.Nonempty ∧ progress p q T (2^j) A B) := by
  unfold accept
  apply Good.bind v (iterate_good v scan h hd hh j hy)
  intro t Z hst hh'
  rcases hh' with ⟨B,hB,prog⟩
  apply Good.post v (any_correct v (s := t) n (fun j => pure (Z (scan j)))
    (fun j => scan j ∈ B)
    (fun a u htu => Good.ret v u _ _ (v.stabilize htu (hB (scan a)))))
  intro u out hh'
  refine ⟨B, v.congr ?_ hh',prog⟩
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨scan i,hi⟩
  · rintro ⟨a,ha⟩
    exact ⟨scan.symm a, by simpa only [Equiv.apply_symm_apply] using ha⟩

set_option maxHeartbeats 600000 in
theorem accept_promised (scan : Fin n ≃ α) (h : Fin R → α → Fin G)
    {D : Detect (StateM S) α W R G} {p : α → Prop}
    (hd : DetectorOK v h p T D) (hh : Outer.GoodFamily h q T)
    {j : ℕ} (hj : q < 2^j) {s : S} {Y : α → W} {A : Finset α}
    (hA : A.card ≤ q) (hPromise : A.card ≤ T ∨ ¬ hit A p) (hy : VecRep v s Y A) :
    Good v s (accept scan h D j Y) (fun t out => v.rep t out (hit A p)) := by
  apply Good.post v (accept_good v scan h hd hh j hy)
  intro t out hout
  rcases hout with ⟨B,hB,prog⟩
  apply v.congr _ hB
  constructor
  · intro hb
    by_contra hno
    have hc := prog.2.2 hA hno
    have h1 : 1 ≤ B.card := Finset.card_pos.mpr hb
    have h2 : 2^j ≤ 2^j*B.card := by simpa using Nat.mul_le_mul_left (2^j) h1
    exact (Nat.not_le_of_gt hj) (h2.trans (hc.trans hA))
  · rintro ⟨a,ha,hpa⟩
    have hcap : A.card ≤ T := hPromise.resolve_right (fun hno => hno ⟨a,ha,hpa⟩)
    exact ⟨a, prog.2.1 hcap a ha hpa⟩

end CoreSemantics

section Cost
variable {M : Type → Type} {α W : Type} [Monad M] [Inhabited (Ops M W)]
variable [Inhabited (BundleBuild.Budget M)] [Fact (UnitGateBudget M W)]
variable {n R G : ℕ}

set_option maxHeartbeats 600000 in
def roundCharge (n R G : ℕ) (c : Fin R → Fin G → ℕ) : ℕ :=
  sumFin R (fun i => sumFin G (c i)) + n*(R+1)

set_option maxHeartbeats 600000 in
theorem round_budget (scan : Fin n ≃ α) (h : Fin R → α → Fin G)
    (D : Detect M α W R G) (c : Fin R → Fin G → ℕ)
    (hc : ∀ Y i b, BundleBuild.Budget.within (D Y i b) (c i b)) (Y : α → W) :
    BundleBuild.Budget.within (round scan h D Y) (roundCharge n R G c) := by
  unfold round roundCharge
  apply BundleBuild.Budget.seq (tab_cost _ _ _ (fun i => tab_cost _ _ _ (hc Y i)))
  intro outs
  apply then_ret (fun next => next ∘ scan.symm)
  apply tab_uniform
  intro j
  have costAll : BundleBuild.Budget.within
      (allFin (M := M) R (fun i => pure (outs i (h i (scan j))))) R := by
    simpa using allFin_cost (M := M) R 0 (fun i => pure (outs i (h i (scan j))))
      (fun i => BundleBuild.Budget.ret (M := M) (outs i (h i (scan j))))
  exact BundleBuild.Budget.seq costAll (land_cost _)

set_option maxHeartbeats 600000 in
theorem iterate_budget (scan : Fin n ≃ α) (h : Fin R → α → Fin G)
    (D : Detect M α W R G) (c : Fin R → Fin G → ℕ)
    (hc : ∀ Y i b, BundleBuild.Budget.within (D Y i b) (c i b))
    (j : ℕ) (Y : α → W) :
    BundleBuild.Budget.within (iterate scan h D j Y) (j*roundCharge n R G c) := by
  induction j with
  | zero => simpa [iterate] using BundleBuild.Budget.ret (M := M) Y
  | succ j ih =>
    rw [Nat.succ_mul]
    unfold iterate
    apply BundleBuild.Budget.seq ih
    intro Z
    exact round_budget scan h D c hc Z

set_option maxHeartbeats 600000 in
theorem accept_budget (scan : Fin n ≃ α) (h : Fin R → α → Fin G)
    (D : Detect M α W R G) (c : Fin R → Fin G → ℕ)
    (hc : ∀ Y i b, BundleBuild.Budget.within (D Y i b) (c i b))
    (j : ℕ) (Y : α → W) :
    BundleBuild.Budget.within (accept scan h D j Y) (j*roundCharge n R G c+n) := by
  unfold accept
  apply BundleBuild.Budget.seq (iterate_budget scan h D c hc j Y)
  intro Z
  simpa using anyFin_cost (M := M) n 0 (fun i => pure (Z (scan i)))
    (fun i => BundleBuild.Budget.ret (M := M) (Z (scan i)))

set_option maxHeartbeats 600000 in
theorem roundCharge_partition (scan : Fin n ≃ α) (h : Fin R → α → Fin G)
    (base per : ℕ) :
    roundCharge n R G (fun i b => base +
      ((List.finRange n).map scan |>.filter (fun a => h i a == b)).length*per)
      = R*(G*base+n*per)+n*(R+1) := by
  unfold roundCharge
  simp only [sumFin_add, sumFin_const, sumFin_mul, length_partition,
    List.length_map, List.length_finRange]
  ring

end Cost

end
end Refute2003.OuterCode

namespace Refute2003

abbrev Label (K : Type*) := (K × K) ⊕ (K ⊕ Unit)

section Geometry
variable {K : Type*} [Field K]

def Incident : Label K → Label K → Prop
  | .inl (u, v), .inl (a, b) => v = a*u+b
  | .inl (u, _), .inr (.inl c) => u = c
  | .inl _, .inr (.inr _) => False
  | .inr (.inl d), .inl (a, _) => d = a
  | .inr (.inl _), .inr (.inl _) => False
  | .inr (.inl _), .inr (.inr _) => True
  | .inr (.inr _), .inl _ => False
  | .inr (.inr _), .inr _ => True

def lineMap (l : Label K) : K ⊕ Unit → Label K :=
  match l with
  | .inl (a,b) => fun
    | .inl u => .inl (u,a*u+b)
    | .inr _ => .inr (.inl a)
  | .inr (.inl c) => fun
    | .inl v => .inl (c,v)
    | .inr _ => .inr (.inr ())
  | .inr (.inr _) => Sum.inr

theorem lineMap_injective (l : Label K) : Function.Injective (lineMap l) := by
  rcases l with ⟨a,b⟩|c|⟨⟩ <;>
    rintro (u|⟨⟩) (v|⟨⟩) h <;> simp [lineMap] at h ⊢ <;> aesop

theorem lineMap_range (l p : Label K) : (∃ u, lineMap l u = p) ↔ Incident p l := by
  rcases l with ⟨a,b⟩|c|⟨⟩ <;>
    rcases p with ⟨u,v⟩|d|⟨⟩ <;>
    simp [lineMap, Incident, Sum.exists] <;> aesop

private theorem join_affine (u v u' v' : K) (hne : (u,v) ≠ (u',v')) :
    ∃! l : Label K, Incident (.inl (u,v)) l ∧ Incident (.inl (u',v')) l := by
  by_cases he : u = u'
  · subst u'
    have hv : v ≠ v' := fun h => hne (h ▸ rfl)
    refine ⟨.inr (.inl u), ⟨rfl,rfl⟩, ?_⟩
    rintro (⟨a,b⟩|c|⟨⟩) h
    · exact (hv (h.1.trans h.2.symm)).elim
    · exact congrArg (fun z => Sum.inr (Sum.inl z)) h.1.symm
    · exact h.1.elim
  · let a : K := (v-v')/(u-u')
    let b : K := v-a*u
    have hu : u-u' ≠ 0 := sub_ne_zero.mpr he
    have hdelta : a*(u-u') = v-v' := div_mul_cancel₀ _ hu
    have h₁ : v = a*u+b := by dsimp [b]; ring
    have h₂ : v' = a*u'+b := by dsimp [b]; linear_combination hdelta
    refine ⟨.inl (a,b), ⟨h₁,h₂⟩, ?_⟩
    rintro (⟨a',b'⟩|c|⟨⟩) h
    · have hl : v = a'*u+b' := h.1
      have hr : v' = a'*u'+b' := h.2
      have ha : a' = a := (eq_div_iff hu).2 (by linear_combination -hl + hr)
      have hb : b' = b := by rw [ha] at hl; dsimp [b]; linear_combination -hl
      rw [ha,hb]
    · exact (he (h.1.trans h.2.symm)).elim
    · exact h.1.elim

private theorem join_affine_nonaffine (u v : K) (r : K ⊕ Unit) :
    ∃! l : Label K, Incident (.inl (u,v)) l ∧ Incident (.inr r) l := by
  rcases r with a|⟨⟩
  · refine ⟨.inl (a,v-a*u), ⟨by change v = a*u+(v-a*u); ring,rfl⟩, ?_⟩
    rintro (⟨c,d⟩|c|⟨⟩) h
    · have ha : c = a := h.2.symm
      have h₁ : v = c*u+d := h.1
      rw [ha] at h₁
      have hd : d = v-a*u := by linear_combination -h₁
      rw [ha,hd]
    · exact h.2.elim
    · exact h.1.elim
  · refine ⟨.inr (.inl u), ⟨rfl,True.intro⟩, ?_⟩
    rintro (⟨a,b⟩|c|⟨⟩) h
    · exact h.2.elim
    · exact congrArg (fun z => Sum.inr (Sum.inl z)) h.1.symm
    · exact h.1.elim

private theorem join_infinity (r s : K ⊕ Unit) (hne : r ≠ s) :
    ∃! l : Label K, Incident (.inr r) l ∧ Incident (.inr s) l := by
  refine ⟨.inr (.inr ()), ?_, ?_⟩
  · rcases r with a|⟨⟩ <;> rcases s with b|⟨⟩ <;> exact ⟨True.intro,True.intro⟩
  · rintro (⟨a,b⟩|c|⟨⟩) h
    · rcases r with d|⟨⟩ <;> rcases s with e|⟨⟩
      · exact (hne (congrArg Sum.inl (h.1.trans h.2.symm))).elim
      · exact h.2.elim
      · exact h.1.elim
      · exact h.1.elim
    · rcases r with d|⟨⟩ <;> rcases s with e|⟨⟩
      · exact h.1.elim
      · exact h.1.elim
      · exact h.2.elim
      · exact (hne rfl).elim
    · rfl

theorem incident_join (p r : Label K) (hne : p ≠ r) :
    ∃! l : Label K, Incident p l ∧ Incident r l := by
  rcases p with ⟨u,v⟩|p <;> rcases r with ⟨w,z⟩|r
  · exact join_affine u v w z (fun h => hne (congrArg Sum.inl h))
  · exact join_affine_nonaffine u v r
  · simpa [and_comm] using join_affine_nonaffine w z p
  · exact join_infinity p r (fun h => hne (congrArg Sum.inr h))

variable [Fintype K]

theorem label_card : Fintype.card (Label K) = Fintype.card K ^ 2 + Fintype.card K + 1 := by
  simp [Label, pow_two, Nat.add_assoc]

noncomputable def plane {n : Nat} (e : Label K ≃ Fin n) (l : Fin n) : Finset (Fin n) :=
  Finset.univ.map ⟨e ∘ lineMap (e.symm l), e.injective.comp (lineMap_injective _)⟩

theorem plane_card {n : Nat} (e : Label K ≃ Fin n) (l : Fin n) :
    (plane e l).card = Fintype.card K+1 := by simp [plane]

theorem mem_plane {n : Nat} (e : Label K ≃ Fin n) (l p : Fin n) :
    p ∈ plane e l ↔ Incident (e.symm p) (e.symm l) := by
  rw [← lineMap_range]
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨u, _, hu⟩
    refine ⟨u, e.injective ?_⟩
    simpa [Function.comp_def] using hu
  · rintro ⟨u,hu⟩
    apply Finset.mem_map.mpr
    refine ⟨u, Finset.mem_univ _, ?_⟩
    change e (lineMap (e.symm l) u) = p
    simp [hu]

theorem plane_join {n : Nat} (e : Label K ≃ Fin n) (p r : Fin n) (hne : p ≠ r) :
    ∃! l : Fin n, p ∈ plane e l ∧ r ∈ plane e l := by
  have h := incident_join (e.symm p) (e.symm r) (fun h => hne (e.symm.injective h))
  exact (e.existsUnique_congr' (fun l => by rw [mem_plane, mem_plane])).mp h

theorem plane_label_count {n : Nat} (e : Label K ≃ Fin n) :
    n = Fintype.card K ^ 2 + Fintype.card K + 1 := by
  have h := Fintype.card_congr e
  rw [Fintype.card_fin, label_card] at h
  exact h.symm

end Geometry
end Refute2003

namespace Refute2003

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

inductive AOOp where
  | and
  | or

def AOOp.compile : AOOp → GateOp
  | .and => .and
  | .or => .or

def AOOp.eval : AOOp → Bool → Bool → Bool
  | .and => (· && ·)
  | .or => (· || ·)

theorem AOOp.eval_compile (op : AOOp) (a b : Bool) :
    op.compile.eval [a, b] = op.eval a b := by
  cases op <;> cases a <;> cases b <;> rfl

def mkGate (op : AOOp) (a b : Fin m) : Gate :=
  ⟨op.compile, [a.val, b.val]⟩

inductive Program (n : Nat) : Nat → Type
  | nil : Program n 0
  | push : Program n s → AOOp → Fin (n+s) → Fin (n+s) → Program n (s+1)

def Program.gates : Program n s → List Gate
  | .nil => []
  | .push P op a b => P.gates ++ [mkGate op a b]

@[simp] theorem Program.gates_length (P : Program n s) : P.gates.length = s := by
  induction P <;> simp_all [gates]

def Program.toCircuit (P : Program n s) (o : Fin (n+s)) : Circuit :=
  ⟨P.gates, o.val⟩

@[simp] theorem Program.size_toCircuit (P : Program n s) (o : Fin (n+s)) :
    (P.toCircuit o).size = s := P.gates_length

theorem Program.valid_output (P : Program n s) (o : Fin (n+s)) :
    (P.toCircuit o).output < n+(P.toCircuit o).size := by
  simpa [toCircuit, Circuit.size] using o.isLt

theorem Program.gate_ops (P : Program n s) :
    ∀ g ∈ P.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
  induction P with
  | nil => simp [gates]
  | @push s P op a b ih =>
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact ih g h
    · have he : g = mkGate op a b := by simpa using h
      subst g
      cases op <;> simp [mkGate, AOOp.compile]

theorem Program.gate_back (P : Program n s) :
    ∀ j < s, ∀ i ∈ (P.gates.getD j ⟨.or, []⟩).inputs, i < n+j := by
  induction P with
  | nil => simp
  | @push s P op a b ih =>
    intro j hj i hi
    by_cases h : j < s
    · rw [gates, List.getD_append _ _ _ _ (by simpa using h)] at hi
      exact ih j h i hi
    · have hej : j = s := by omega
      subst j
      rw [gates, List.getD_append_right _ _ _ _ (by simp), gates_length,
        Nat.sub_self] at hi
      have hh : i = a.val ∨ i = b.val := by simpa [mkGate] using hi
      rcases hh with rfl | rfl
      · exact a.isLt
      · exact b.isLt

theorem Program.toCircuit_IsAO2 (P : Program n s) (o : Fin (n+s)) :
    IsAO2 n (P.toCircuit o) := by
  refine ⟨fun g hg => (P.gate_ops g hg).1, ?_, fun g hg => (P.gate_ops g hg).2⟩
  intro j hj i hi
  exact P.gate_back j (by simpa [toCircuit] using hj) i hi

def Program.wires (P : Program n s) (x : Fin n → Bool) : List Bool :=
  match P with
  | .nil => List.ofFn x
  | .push Q op a b =>
    let r := Q.wires x
    r ++ [op.eval (r.getD a.val false) (r.getD b.val false)]

@[simp] theorem Program.wires_length (P : Program n s) (x : Fin n → Bool) :
    (P.wires x).length = n+s := by
  induction P <;> simp_all [wires, Nat.add_assoc]

def Program.read (P : Program n s) (x : Fin n → Bool) (a : Fin (n+s)) : Bool :=
  (P.wires x).getD a.val false

theorem Program.read_input (P : Program n s) (x : Fin n → Bool) (a : Fin n) :
    P.read x (Fin.castLE (Nat.le_add_right n s) a) = x a := by
  induction P with
  | nil => simp [read, wires, List.getD_eq_getElem?_getD]
  | @push s P op l r ih =>
    unfold read at *
    simp only [wires, Fin.val_castLE]
    rw [List.getD_append _ _ _ _ (by rw [wires_length]; omega)]
    exact ih

theorem Program.read_old (P : Program n s) (x : Fin n → Bool) (op : AOOp)
    (l r a : Fin (n+s)) :
    (P.push op l r).read x (Fin.castSucc a) = P.read x a := by
  simp only [read, wires, Fin.val_castSucc]
  rw [List.getD_append _ _ _ _ (by simpa using a.isLt)]

theorem Program.read_new (P : Program n s) (x : Fin n → Bool) (op : AOOp)
    (l r : Fin (n+s)) :
    (P.push op l r).read x (Fin.last (n+s)) = op.eval (P.read x l) (P.read x r) := by
  simp only [read, wires, Fin.val_last]
  rw [List.getD_append_right _ _ _ _ (by simp), wires_length, Nat.sub_self]
  rfl

theorem Program.toCircuit_wires (P : Program n s) (x : Fin n → Bool)
    (o : Fin (n+s)) : (P.toCircuit o).wires (List.ofFn x) = P.wires x := by
  induction P with
  | nil => rfl
  | @push s P op l r ih =>
    have h : (P.toCircuit l).wires (List.ofFn x) = P.wires x := ih l
    change P.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x) = P.wires x at h
    simp only [toCircuit, Circuit.wires, gates, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [h]
    simp only [mkGate, List.map_cons, List.map_nil, AOOp.eval_compile, wires]

theorem Program.toCircuit_eval (P : Program n s) (x : Fin n → Bool)
    (o : Fin (n+s)) : (P.toCircuit o).eval (List.ofFn x) = P.read x o := by
  simp only [Circuit.eval, toCircuit_wires]
  rfl

inductive Ref (m : Nat) where
  | const : Bool → Ref m
  | wire : Fin m → Ref m

def Ref.castLE (h : m ≤ k) : Ref m → Ref k
  | .const c => .const c
  | .wire w => .wire (Fin.castLE h w)

def Ref.read (P : Program n s) (x : Fin n → Bool) : Ref (n+s) → Bool
  | .const c => c
  | .wire w => P.read x w

inductive Extends : Program n s → Program n t → Prop
  | refl (P : Program n s) : Extends P P
  | more {P : Program n s} {Q : Program n t} (h : Extends P Q)
      (op : AOOp) (a b : Fin (n+t)) : Extends P (Q.push op a b)

theorem Extends.le {P : Program n s} {Q : Program n t} (h : Extends P Q) : s ≤ t := by
  induction h with
  | refl => exact le_rfl
  | more _ _ _ _ ih => exact ih.trans (Nat.le_succ _)

theorem Extends.trans {P : Program n s} {Q : Program n t} {R : Program n u}
    (h : Extends P Q) (h' : Extends Q R) : Extends P R := by
  induction h' with
  | refl => exact h
  | more _ op a b ih => exact ih h |>.more op a b

theorem Extends.read {P : Program n s} {Q : Program n t} (h : Extends P Q)
    (x : Fin n → Bool) (a : Fin (n+s)) :
    Q.read x (Fin.castLE (Nat.add_le_add_left h.le n) a) = P.read x a := by
  induction h with
  | refl => rfl
  | more hm op l r ih =>
    have he : Fin.castLE (Nat.add_le_add_left (hm.more op l r).le n) a =
        (Fin.castLE (Nat.add_le_add_left hm.le n) a).castSucc := Fin.ext rfl
    rw [he, Program.read_old, ih]

theorem Extends.readRef {P : Program n s} {Q : Program n t} (h : Extends P Q)
    (x : Fin n → Bool) (a : Ref (n+s)) :
    Ref.read Q x (a.castLE (Nat.add_le_add_left h.le n)) = Ref.read P x a := by
  cases a with
  | const c => rfl
  | wire a => exact h.read x a

structure Build (P : Program n s) (k : Nat) (O : Nat → Type) where
  stop : Nat
  prog : Program n stop
  prefixProof : Extends P prog
  bound : stop ≤ s+k
  out : O (n+stop)

def Build.liftRef {P : Program n s} {O : Nat → Type} {k : Nat}
    (r : Build P k O) (a : Ref (n+s)) : Ref (n+r.stop) :=
  a.castLE (Nat.add_le_add_left r.prefixProof.le n)

theorem Build.liftRef_read {P : Program n s} {O : Nat → Type} {k : Nat}
    (r : Build P k O) (x : Fin n → Bool) (a : Ref (n+s)) :
    Ref.read r.prog x (r.liftRef a) = Ref.read P x a :=
  r.prefixProof.readRef x a

def Build.pure (P : Program n s) (a : O (n+s)) : Build P k O :=
  ⟨s, P, .refl P, Nat.le_add_right s k, a⟩

def Build.bind {P : Program n s} {k j : Nat} {I O : Nat → Type}
    (a : Build P k I) (b : Build a.prog j O) : Build P (k+j) O :=
  ⟨b.stop, b.prog, a.prefixProof.trans b.prefixProof, by
    have h := Nat.add_le_add_right a.bound j
    have h' := b.bound
    omega, b.out⟩

def emit (P : Program n s) (op : AOOp) (a b : Ref (n+s)) : Build P 1 Ref :=
  match a, b with
  | .wire a, .wire b =>
    ⟨s+1, P.push op a b, (Extends.refl P).more op a b, le_rfl,
      .wire (Fin.last (n+s))⟩
  | .const a, .const b => .pure P (.const (op.eval a b))
  | .const false, .wire b => .pure P (match op with | .and => .const false | .or => .wire b)
  | .const true, .wire b => .pure P (match op with | .and => .wire b | .or => .const true)
  | .wire a, .const false => .pure P (match op with | .and => .const false | .or => .wire a)
  | .wire a, .const true => .pure P (match op with | .and => .wire a | .or => .const true)

theorem emit_correct (P : Program n s) (x : Fin n → Bool) (op : AOOp)
    (a b : Ref (n+s)) :
    let r := emit P op a b
    Ref.read r.prog x r.out = op.eval (Ref.read P x a) (Ref.read P x b) := by
  cases a with
  | const a =>
    cases b with
    | const b => simp [emit, Build.pure, Ref.read]
    | wire b => cases a <;> cases op <;> simp [emit, Build.pure, Ref.read, AOOp.eval]
  | wire a =>
    cases b with
    | const b => cases b <;> cases op <;> simp [emit, Build.pure, Ref.read, AOOp.eval]
    | wire b => exact P.read_new x op a b

end Refute2003


namespace Refute2003
open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm

def input {n : Nat} (X Y : Finset (Fin n)) : Fin (n+n) → Bool :=
  Fin.append (fun p : Fin n => decide (p ∈ X)) (fun l : Fin n => decide (l ∈ Y))

theorem input_eq {n : Nat} (X Y : Finset (Fin n)) :
    List.ofFn (input X Y) = incidenceInput X Y := by
  rw [input, List.ofFn_fin_append]
  rfl

theorem incidenceFun_false {n : Nat} {S : Fin n → Finset (Fin n)} {X Y : Finset (Fin n)}
    (hn : IsFalseInput S X Y) : incidenceFun S X Y = false := by
  apply decide_eq_false
  rintro ⟨p,hp,l,hl,h⟩
  exact Finset.disjoint_left.mp (hn l hl) h hp

theorem incidenceFun_pair_true {n : Nat} {S : Fin n → Finset (Fin n)} {p l : Fin n}
    (hp : p ∈ S l) : incidenceFun S {p} {l} = true := by
  apply decide_eq_true
  exact ⟨p, Finset.mem_singleton_self _, l, Finset.mem_singleton_self _, hp⟩

open PEqualNP.MetaComplexity

theorem input_pair {n : Nat} (p l : Fin n) :
    input {p} {l} = fun k => decide (k = Fin.castAdd n p ∨ k = Fin.natAdd n l) := by
  have hsep (i j : Fin n) : Fin.castAdd n i ≠ Fin.natAdd n j := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hright (i j : Fin n) : Fin.natAdd n i = Fin.natAdd n j ↔ i = j := by
    constructor
    · intro h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hv
      omega
    · exact congrArg (Fin.natAdd n)
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp only [input, Fin.append_left, Finset.mem_singleton, Fin.castAdd_inj, hsep, or_false]
  · intro i
    simp only [input, Fin.append_right, Finset.mem_singleton, (hsep p i).symm, false_or, hright]

end Refute2003

namespace Refute2003

abbrev Machine (n : Nat) := (s : Nat) × Program n s
abbrev Code (n : Nat) := StateM (Machine n)

def Machine.Extends (S T : Machine n) : Prop := Refute2003.Extends S.2 T.2

theorem Machine.Extends.refl (S : Machine n) : S.Extends S := Refute2003.Extends.refl _

theorem Machine.Extends.trans {S T U : Machine n}
    (a : S.Extends T) (b : T.Extends U) : S.Extends U :=
  Refute2003.Extends.trans a b

theorem Machine.Extends.le {S T : Machine n} (h : S.Extends T) : S.1 ≤ T.1 :=
  Refute2003.Extends.le h

def Machine.empty (n : Nat) : Machine n := ⟨0, .nil⟩

inductive Signal where
  | const : Bool → Signal
  | index : Nat → Signal

def Signal.valid (S : Machine n) : Signal → Prop
  | .const _ => True
  | .index i => i < n+S.1

def Signal.read (S : Machine n) (x : Fin n → Bool) : Signal → Bool
  | .const c => c
  | .index w => (S.2.wires x).getD w false

def Signal.ofRef {m : Nat} : Ref m → Signal
  | .const b => .const b
  | .wire i => .index i.val

def Signal.asRef (S : Machine n) : Signal → Ref (n+S.1)
  | .const b => .const b
  | .index i => if h : i < n+S.1 then .wire ⟨i,h⟩ else .const false

theorem Signal.ofRef_valid (S : Machine n) (a : Ref (n+S.1)) : (ofRef a).valid S := by
  cases a with
  | const b => trivial
  | wire i => exact i.isLt

theorem Signal.read_ofRef (S : Machine n) (x : Fin n → Bool) (a : Ref (n+S.1)) :
    (Signal.ofRef a).read S x = Ref.read S.2 x a := by cases a <;> rfl

theorem Signal.read_asRef (S : Machine n) (x : Fin n → Bool) (a : Signal) :
    Ref.read S.2 x (a.asRef S) = a.read S x := by
  cases a with
  | const b => rfl
  | index i =>
    by_cases h : i < n+S.1
    · simp [asRef, h, Ref.read, read, Program.read]
    · have hw : (S.2.wires x).length ≤ i := by
        rw [Program.wires_length]
        omega
      simp [asRef, h, Ref.read, read, List.getD_eq_default (S.2.wires x) false hw]

def Signal.input (i : Fin n) : Signal := .index i.val

theorem Signal.input_valid (S : Machine n) (i : Fin n) : (Signal.input i).valid S := by
  change i.val < n+S.1
  omega

theorem Signal.read_input (S : Machine n) (x : Fin n → Bool) (i : Fin n) :
    (Signal.input i).read S x = x i :=
  S.2.read_input x i

theorem Signal.valid_of_extends {S T : Machine n} {a : Signal}
    (h : S.Extends T) (ha : a.valid S) : a.valid T := by
  cases a with
  | const b => trivial
  | index i =>
    change i < n+S.1 at ha
    change i < n+T.1
    have ht := h.le
    omega

theorem Signal.read_of_extends {S T : Machine n} {a : Signal}
    (h : S.Extends T) (ha : a.valid S) (x : Fin n → Bool) :
    a.read T x = a.read S x := by
  cases a with
  | const b => rfl
  | index i =>
    change i < n+S.1 at ha
    exact Refute2003.Extends.read h x ⟨i,ha⟩

def emitCode (op : AOOp) (a b : Signal) : Code n Signal :=
  fun S =>
    let r := emit S.2 op (a.asRef S) (b.asRef S)
    (.ofRef r.out, ⟨r.stop,r.prog⟩)

theorem emitCode_append (op : AOOp) (a b : Signal) (S : Machine n) :
    S.Extends ((emitCode op a b).run S).2 :=
  (emit S.2 op (a.asRef S) (b.asRef S)).prefixProof

theorem emitCode_bound (op : AOOp) (a b : Signal) (S : Machine n) :
    ((emitCode op a b).run S).2.1 ≤ S.1+1 :=
  (emit S.2 op (a.asRef S) (b.asRef S)).bound

theorem emitCode_valid (op : AOOp) (a b : Signal) (S : Machine n) :
    ((emitCode op a b).run S).1.valid ((emitCode op a b).run S).2 :=
  Signal.ofRef_valid _ _

theorem emitCode_eval (op : AOOp) (a b : Signal) (S : Machine n) (x : Fin n → Bool) :
    ((emitCode op a b).run S).1.read ((emitCode op a b).run S).2 x =
      op.eval (a.read S x) (b.read S x) := by
  let r := emit S.2 op (a.asRef S) (b.asRef S)
  change (Signal.ofRef r.out).read ⟨r.stop,r.prog⟩ x = _
  rw [Signal.read_ofRef]
  change Ref.read r.prog x r.out = _
  rw [emit_correct, Signal.read_asRef, Signal.read_asRef]

instance physicalOps (n : Nat) : Inhabited (BundleBuild.Ops (Code n) Signal) where
  default := {
    constant := .const
    andGate := emitCode .and
    orGate := emitCode .or
  }

theorem run_pure (a : A) (S : Machine n) : ((pure a : Code n A).run S) = (a,S) := rfl

theorem run_bind (a : Code n A) (b : A → Code n B) (S : Machine n) :
    ((a >>= b).run S) = (b (a.run S).1).run (a.run S).2 := rfl

def Realizes (S : Machine n) (x : Fin n → Bool) (a : Signal) (v : Bool) : Prop :=
  a.valid S ∧ a.read S x = v

theorem Realizes.mono {S T : Machine n} {x : Fin n → Bool} {a : Signal} {v : Bool}
    (hr : Realizes S x a v) (h : S.Extends T) : Realizes T x a v :=
  ⟨Signal.valid_of_extends h hr.1, (Signal.read_of_extends h hr.1 x).trans hr.2⟩

theorem Realizes.ofConst (S : Machine n) (x : Fin n → Bool) (b : Bool) :
    Realizes S x (.const b) b := ⟨trivial,rfl⟩

theorem Realizes.ofInput (S : Machine n) (x : Fin n → Bool) (i : Fin n) :
    Realizes S x (Signal.input i) (x i) :=
  ⟨Signal.input_valid S i, Signal.read_input S x i⟩

theorem Realizes.emit {S : Machine n} {x : Fin n → Bool} {a b : Signal} {p q : Bool}
    (ha : Realizes S x a p) (hb : Realizes S x b q) (op : AOOp) :
    Realizes ((emitCode op a b).run S).2 x ((emitCode op a b).run S).1 (op.eval p q) := by
  refine ⟨emitCode_valid op a b S, ?_⟩
  rw [emitCode_eval, ha.2, hb.2]

end Refute2003

namespace Refute2003

def physicalWithin (a : Code n A) (k : Nat) : Prop :=
  ∀ S, S.Extends (a.run S).2 ∧ (a.run S).2.1 ≤ S.1+k

instance physicalBudget (n : Nat) : Inhabited (BundleBuild.Budget (Code n)) where
  default := {
    withinCost := physicalWithin
    weakenCost h hk S := ⟨(h S).1, (h S).2.trans (Nat.add_le_add_left hk _)⟩
    returnCost _ S := ⟨Machine.Extends.refl S, Nat.le_refl _⟩
    bindCost := by
      intro A B p f k l h g S
      change S.Extends ((p >>= f).run S).2 ∧ ((p >>= f).run S).2.1 ≤ S.1+(k+l)
      rw [run_bind]
      have h₁ := h S
      have h₂ := g (p.run S).1 (p.run S).2
      refine ⟨h₁.1.trans h₂.1, ?_⟩
      have h₃ := h₁.2
      have h₄ := h₂.2
      omega
  }

instance physicalUnitBudget (n : Nat) : Fact (BundleBuild.UnitGateBudget (Code n) Signal) where
  out := {
    andCost a b S := ⟨emitCode_append .and a b S, emitCode_bound .and a b S⟩
    orCost a b S := ⟨emitCode_append .or a b S, emitCode_bound .or a b S⟩
  }

theorem budget_append (a : Code n A) (k : Nat)
    (h : BundleBuild.Budget.within a k) (S : Machine n) : S.Extends (a.run S).2 :=
  (h S).1

theorem budget_size (a : Code n A) (k : Nat)
    (h : BundleBuild.Budget.within a k) (S : Machine n) : (a.run S).2.1 ≤ S.1+k :=
  (h S).2

end Refute2003

namespace Refute2003
open BundleBuild

def AOOp.prop : AOOp → Prop → Prop → Prop
  | .and => And
  | .or => Or

theorem AOOp.eval_iff (op : AOOp) (a b : Bool) :
    op.eval a b = true ↔ op.prop (a = true) (b = true) := by
  cases op <;> cases a <;> cases b <;> simp [AOOp.eval, AOOp.prop]

def Truth (S : Machine n) (x : Fin n → Bool) (a : Signal) (P : Prop) : Prop :=
  a.valid S ∧ (a.read S x = true ↔ P)

theorem Truth.mono {S T : Machine n} {x : Fin n → Bool} {a : Signal} {P : Prop}
    (ha : Truth S x a P) (h : S.Extends T) : Truth T x a P := by
  refine ⟨Signal.valid_of_extends h ha.1, ?_⟩
  rw [Signal.read_of_extends h ha.1 x]
  exact ha.2

theorem Truth.congr {S : Machine n} {x : Fin n → Bool} {a : Signal} {P Q : Prop}
    (ha : Truth S x a P) (h : P ↔ Q) : Truth S x a Q :=
  ⟨ha.1,ha.2.trans h⟩

theorem Truth.ofConst (S : Machine n) (x : Fin n → Bool) (b : Bool) :
    Truth S x (.const b) (b = true) := ⟨trivial,Iff.rfl⟩

theorem Truth.ofInput (S : Machine n) (x : Fin n → Bool) (i : Fin n) :
    Truth S x (Signal.input i) (x i = true) := by
  exact ⟨Signal.input_valid S i, by rw [Signal.read_input]⟩

theorem Truth.emit {S : Machine n} {x : Fin n → Bool} {a b : Signal} {P Q : Prop}
    (ha : Truth S x a P) (hb : Truth S x b Q) (op : AOOp) :
    Truth ((emitCode op a b).run S).2 x ((emitCode op a b).run S).1 (op.prop P Q) := by
  refine ⟨emitCode_valid op a b S, ?_⟩
  rw [emitCode_eval, AOOp.eval_iff, ha.2, hb.2]

def physicalSem (x : Fin n → Bool) : BundleBuild.Sem (Machine n) Signal where
  ext := Machine.Extends
  refl := Machine.Extends.refl
  trans := Machine.Extends.trans
  rep := fun S a P => Truth S x a P
  stabilize h h' := h'.mono h
  congr h h' := h'.congr h
  konst S b := Truth.ofConst S x b
  land ha hb := ⟨emitCode_append .and _ _ _, ha.emit hb .and⟩
  lor ha hb := ⟨emitCode_append .or _ _ _, ha.emit hb .or⟩

end Refute2003

namespace Refute2003
open BundleBuild
open PEqualNP.GenericRejection

def affineHit {K : Type*} [Field K] (P L : Label K → Prop) : Prop :=
  ∃ ab : K×K, L (.inl ab) ∧ ∃ u : K, P (.inl (u,ab.1*u+ab.2))

def verticalHit {K : Type*} (P L : Label K → Prop) : Prop :=
  ∃ c : K, L (.inr (.inl c)) ∧ (P (.inr (.inr ())) ∨ ∃ v : K, P (.inl (c,v)))

def slopeInfinityHit {K : Type*} (P L : Label K → Prop) : Prop :=
  ∃ a : K, P (.inr (.inl a)) ∧ ∃ b : K, L (.inl (a,b))

def infinityHit {K : Type*} (P L : Label K → Prop) : Prop :=
  L (.inr (.inr ())) ∧ (P (.inr (.inr ())) ∨ ∃ a : K, P (.inr (.inl a)))

def extraHit {K : Type*} (P L : Label K → Prop) : Prop :=
  verticalHit P L ∨ slopeInfinityHit P L ∨ infinityHit P L

theorem geometry_hit {K : Type*} [Field K] (P L : Label K → Prop) :
    (affineHit P L ∨ extraHit P L) ↔ ∃ p, P p ∧ ∃ l, L l ∧ Incident p l := by
  constructor
  · intro h
    rcases h with ⟨⟨a,b⟩, hl,u,hp⟩ | h
    · exact ⟨.inl (u,a*u+b),hp,.inl (a,b),hl,rfl⟩
    · rcases h with h | h | h
      · rcases h with ⟨c,hl,h⟩
        rcases h with hp | ⟨v,hp⟩
        · exact ⟨.inr (.inr ()),hp,.inr (.inl c),hl,True.intro⟩
        · exact ⟨.inl (c,v),hp,.inr (.inl c),hl,rfl⟩
      · rcases h with ⟨a,hp,b,hl⟩
        exact ⟨.inr (.inl a),hp,.inl (a,b),hl,rfl⟩
      · rcases h with ⟨hl,h⟩
        rcases h with hp | ⟨a,hp⟩
        · exact ⟨.inr (.inr ()),hp,.inr (.inr ()),hl,True.intro⟩
        · exact ⟨.inr (.inl a),hp,.inr (.inr ()),hl,True.intro⟩
  · rintro ⟨(⟨u,v⟩|d|⟨⟩),hp,(⟨a,b⟩|c|⟨⟩),hl,h⟩
    · have he : v = a*u+b := h
      exact Or.inl ⟨(a,b),hl,u,he ▸ hp⟩
    · have he : u = c := h
      exact Or.inr (Or.inl ⟨c,hl,Or.inr ⟨v,he ▸ hp⟩⟩)
    · exact h.elim
    · have he : d = a := h
      exact Or.inr (Or.inr (Or.inl ⟨a,he ▸ hp,b,hl⟩))
    · exact h.elim
    · exact Or.inr (Or.inr (Or.inr ⟨hl,Or.inr ⟨d,hp⟩⟩))
    · exact h.elim
    · exact Or.inr (Or.inl ⟨c,hl,Or.inl hp⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hl,Or.inl hp⟩))

def verticalCode {K : Type} (number : K ≃ Fin q)
    {M : Type → Type} {W : Type} [Monad M] [Inhabited (Ops M W)] (px ly : Label K → W) : M W :=
  BundleBuild.anyFin q (fun i => do
    let ps ← BundleBuild.anyFin q (fun j => pure (px (.inl (number.symm i,number.symm j))))
    let hasP ← Ops.lor (px (.inr (.inr ()))) ps
    Ops.land (ly (.inr (.inl (number.symm i)))) hasP)

def slopeInfinityCode {K : Type} (number : K ≃ Fin q)
    {M : Type → Type} {W : Type} [Monad M] [Inhabited (Ops M W)] (px ly : Label K → W) : M W :=
  BundleBuild.anyFin q (fun i => do
    let ls ← BundleBuild.anyFin q (fun j => pure (ly (.inl (number.symm i, number.symm j))))
    Ops.land (px (.inr (.inl (number.symm i)))) ls)

def infinityCode {K : Type} (number : K ≃ Fin q)
    {M : Type → Type} {W : Type} [Monad M] [Inhabited (Ops M W)] (px ly : Label K → W) : M W := do
  let sl ← BundleBuild.anyFin q (fun i => pure (px (.inr (.inl (number.symm i)))))
  let hasP ← Ops.lor (px (.inr (.inr ()))) sl
  Ops.land (ly (.inr (.inr ()))) hasP

def specialCode {K : Type} (number : K ≃ Fin q)
    {M : Type → Type} {W : Type} [Monad M] [Inhabited (Ops M W)] (px ly : Label K → W) : M W := do
  let a ← verticalCode number px ly
  let b ← slopeInfinityCode number px ly
  let c ← infinityCode number px ly
  let k ← Ops.lor b c
  Ops.lor a k

def specialCost (q : Nat) : Nat := q*(q+3) + q*(q+2) + (q+2) + 2

section SpecialBudget
variable {M : Type → Type} {W : Type} [Monad M] [Inhabited (Ops M W)] [Inhabited (Budget M)] [Fact (UnitGateBudget M W)]
variable {K : Type} (number : K ≃ Fin q) (px ly : Label K → W)

theorem vertical_budget :
    Budget.within (verticalCode (M := M) number px ly) (q*(q+3)) := by
  unfold verticalCode
  apply anyFin_cost q (q+2)
  intro i
  have h : Budget.within
      (BundleBuild.anyFin q (fun j => (pure (px (.inl (number.symm i,number.symm j))) : M W))) q := by
    simpa using anyFin_cost q 0 _ (fun j => Budget.ret (px (.inl (number.symm i,number.symm j))))
  simpa [Nat.add_assoc] using Budget.seq h (fun ps => Budget.seq (lor_cost (px (.inr (.inr ()))) ps)
    (fun hp => land_cost (ly (.inr (.inl (number.symm i)))) hp))

theorem slope_budget :
    Budget.within (slopeInfinityCode (M := M) number px ly) (q*(q+2)) := by
  unfold slopeInfinityCode
  apply anyFin_cost q (q+1)
  intro i
  have h : Budget.within
      (BundleBuild.anyFin q (fun j => (pure (ly (.inl (number.symm i,number.symm j))) : M W))) q := by
    simpa using anyFin_cost q 0 _ (fun j => Budget.ret (ly (.inl (number.symm i,number.symm j))))
  exact Budget.seq h (fun ls => land_cost (px (.inr (.inl (number.symm i)))) ls)

theorem infinity_budget :
    Budget.within (infinityCode (M := M) number px ly) (q+2) := by
  unfold infinityCode
  have h : Budget.within
      (BundleBuild.anyFin q (fun i => (pure (px (.inr (.inl (number.symm i)))) : M W))) q := by
    simpa using anyFin_cost q 0 _ (fun i => Budget.ret (px (.inr (.inl (number.symm i)))))
  simpa [Nat.add_assoc] using Budget.seq h (fun ps => Budget.seq (lor_cost (px (.inr (.inr ()))) ps)
    (fun hp => land_cost (ly (.inr (.inr ()))) hp))

theorem special_budget :
    Budget.within (specialCode (M := M) number px ly) (specialCost q) := by
  unfold specialCode specialCost
  simpa only [Nat.add_assoc] using Budget.seq (vertical_budget number px ly) (fun a =>
    Budget.seq (slope_budget number px ly) (fun b =>
      Budget.seq (infinity_budget number px ly) (fun c =>
        Budget.seq (lor_cost b c) (fun k => lor_cost a k))))

end SpecialBudget

section SpecialCorrect
variable {S W : Type} [Inhabited (Ops (StateM S) W)] (v : Sem S W)
variable {K : Type} (number : K ≃ Fin q)

private theorem exists_number (P : K → Prop) : (∃ i, P (number.symm i)) ↔ ∃ p, P p := by
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨_,hi⟩
  · rintro ⟨p,hp⟩
    exact ⟨number p,by simpa using hp⟩

theorem vertical_correct {s : S} {px ly : Label K → W} {P L : Label K → Prop}
    (hp : ∀ p, v.rep s (px p) (P p)) (hl : ∀ l, v.rep s (ly l) (L l)) :
    Good v s (verticalCode number px ly) (fun t out => v.rep t out (verticalHit P L)) := by
  unfold verticalCode verticalHit
  refine Good.post v (any_correct v q _ (fun i => L (.inr (.inl (number.symm i))) ∧
    (P (.inr (.inr ())) ∨ ∃ x, P (.inl (number.symm i,x)))) ?_) ?_
  · intro i t hst
    have hv := any_correct v q
      (fun j => (pure (px (.inl (number.symm i,number.symm j))) : StateM S W))
      (fun j => P (.inl (number.symm i,number.symm j)))
      (fun j u htu => Good.ret v u _ _ (v.stabilize (v.trans hst htu) (hp _)))
    apply Good.bind v hv
    intro u ns htu hn
    have hu := v.trans hst htu
    have hn' := v.congr (exists_number number (fun j => P (.inl (number.symm i,j)))) hn
    apply Good.bind v (lor_good v (v.stabilize hu (hp _)) hn')
    intro z hasP huz hz
    exact land_good v (v.stabilize (v.trans hu huz) (hl _)) hz
  · intro t a ha
    exact v.congr (exists_number number _) ha

theorem slope_correct {s : S} {px ly : Label K → W} {P L : Label K → Prop}
    (hp : ∀ p, v.rep s (px p) (P p)) (hl : ∀ l, v.rep s (ly l) (L l)) :
    Good v s (slopeInfinityCode number px ly) (fun t out => v.rep t out (slopeInfinityHit P L)) := by
  unfold slopeInfinityCode slopeInfinityHit
  refine Good.post v (any_correct v q _ (fun i =>
    P (.inr (.inl (number.symm i))) ∧ ∃ b, L (.inl (number.symm i,b))) ?_) ?_
  · intro i t hst
    have hh := any_correct v q
      (fun j => (pure (ly (.inl (number.symm i,number.symm j))) : StateM S W))
      (fun j => L (.inl (number.symm i,number.symm j)))
      (fun j u htu => Good.ret v u _ _ (v.stabilize (v.trans hst htu) (hl _)))
    apply Good.bind v hh
    intro u ns htu hn
    exact land_good v (v.stabilize (v.trans hst htu) (hp _))
      (v.congr (exists_number number (fun b => L (.inl (number.symm i,b)))) hn)
  · intro t a ha
    exact v.congr (exists_number number _) ha

theorem infinity_correct {s : S} {px ly : Label K → W} {P L : Label K → Prop}
    (hp : ∀ p, v.rep s (px p) (P p)) (hl : ∀ l, v.rep s (ly l) (L l)) :
    Good v s (infinityCode number px ly) (fun t out => v.rep t out (infinityHit P L)) := by
  unfold infinityCode infinityHit
  have hh := any_correct v q
    (fun i => (pure (px (.inr (.inl (number.symm i)))) : StateM S W))
    (fun i => P (.inr (.inl (number.symm i))))
    (fun j u hsu => Good.ret v u _ _ (v.stabilize hsu (hp _)))
  apply Good.bind v hh
  intro u ns hsu hn
  have h' := v.congr (exists_number number (fun a => P (.inr (.inl a)))) hn
  apply Good.bind v (lor_good v (v.stabilize hsu (hp _)) h')
  intro u' pp huu' hpp
  exact land_good v (v.stabilize (v.trans hsu huu') (hl _)) hpp

theorem special_correct {s : S} {px ly : Label K → W} {P L : Label K → Prop}
    (hp : ∀ p, v.rep s (px p) (P p)) (hl : ∀ l, v.rep s (ly l) (L l)) :
    Good v s (specialCode number px ly) (fun t out => v.rep t out (extraHit P L)) := by
  unfold specialCode extraHit
  apply Good.bind v (vertical_correct v number hp hl)
  intro t a hst ha
  apply Good.bind v (slope_correct v number
    (fun p => v.stabilize hst (hp p)) (fun l => v.stabilize hst (hl l)))
  intro u b htu hb
  have hsu := v.trans hst htu
  apply Good.bind v (infinity_correct v number
    (fun p => v.stabilize hsu (hp p)) (fun l => v.stabilize hsu (hl l)))
  intro z c huz hc
  apply Good.bind v (lor_good v (v.stabilize huz hb) hc)
  intro z' d hzz' hd
  exact lor_good v (v.stabilize (v.trans htu (v.trans huz hzz')) ha) hd

end SpecialCorrect

section Physical
variable {K : Type} [Field K] [Fintype K]
variable (number : K ≃ Fin q) (lab : Label K ≃ Fin n)

def pointWire (p : Label K) : Signal :=
  Signal.input ((lab p).castAdd n)

def lineWire (l : Label K) : Signal :=
  Signal.input ((lab l).natAdd n)

theorem pointRep (S : Machine (n+n)) (X Y : Finset (Fin n)) (p : Label K) :
    Truth S (input X Y) (pointWire lab p) (lab p ∈ X) := by
  apply (Truth.ofInput S (input X Y) ((lab p).castAdd n)).congr
  simp [input]

theorem lineRep (S : Machine (n+n)) (X Y : Finset (Fin n)) (l : Label K) :
    Truth S (input X Y) (lineWire lab l) (lab l ∈ Y) := by
  apply (Truth.ofInput S (input X Y) ((lab l).natAdd n)).congr
  simp only [input, Fin.append_right, decide_eq_true_eq]

def planeCode (aff : Code (n+n) Signal) : Code (n+n) Signal := do
  let a ← aff
  let extra ← specialCode number (pointWire lab) (lineWire lab)
  Ops.lor a extra

theorem planeCode_budget (aff : Code (n+n) Signal) (c : Nat)
    (h : Budget.within aff c) :
    Budget.within (planeCode number lab aff) (c + specialCost q + 1) := by
  simpa only [planeCode, Nat.add_assoc] using Budget.seq h (fun a =>
    Budget.seq (special_budget number (pointWire lab) (lineWire lab)) (lor_cost a))

theorem code_correct (X Y : Finset (Fin n)) (S : Machine (n+n)) (aff : Code (n+n) Signal)
    (ok : Good (physicalSem (input X Y)) S aff (fun t a =>
      Truth t (input X Y) a (affineHit (fun p => lab p ∈ X) (fun l => lab l ∈ Y)))) :
    let r := (planeCode number lab aff).run S
    r.1.read r.2 (input X Y) = incidenceFun (plane lab) X Y := by
  let v := physicalSem (input X Y)
  have h : Good v S (planeCode number lab aff) (fun t out =>
      Truth t (input X Y) out ((affineHit (fun p => lab p ∈ X) (fun l => lab l ∈ Y)) ∨
        extraHit (fun p => lab p ∈ X) (fun l => lab l ∈ Y))) := by
    unfold planeCode
    apply Good.bind v ok
    intro t a hst ha
    apply Good.bind v (special_correct v number (pointRep lab t X Y) (lineRep lab t X Y))
    intro u b htu hb
    exact lor_good v (v.stabilize htu ha) hb
  have ht := (h.2.2.trans (geometry_hit _ _))
  apply Bool.eq_iff_iff.mpr
  refine ht.trans ?_
  unfold incidenceFun
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨p,hp,l,hl,hm⟩
    exact ⟨lab p,hp,lab l,hl,(mem_plane lab _ _).mpr (by simpa using hm)⟩
  · rintro ⟨p,hp,l,hl,hm⟩
    exact ⟨lab.symm p,by simpa,lab.symm l,by simpa,(mem_plane lab _ _).mp hm⟩

end Physical
end Refute2003

namespace Refute2003
open BundleBuild

theorem AOOp.eval_mono (op : AOOp) {a b a' b' : Bool}
    (ha : a = true → a' = true) (hb : b = true → b' = true) :
    op.eval a b = true → op.eval a' b' = true := by
  cases op
  · simp only [AOOp.eval, Bool.and_eq_true]
    rintro ⟨h₁,h₂⟩
    exact ⟨ha h₁,hb h₂⟩
  · simp only [AOOp.eval, Bool.or_eq_true]
    intro h
    exact h.elim (fun h => Or.inl (ha h)) (fun h => Or.inr (hb h))

theorem Program.read_mono (P : Program n s) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) (w : Fin (n+s)) :
    P.read x w = true → P.read y w = true := by
  induction P with
  | nil =>
    change PEqualNP.CircuitLowerBounds.Circuit.eval ⟨[],w.val⟩ (List.ofFn x) = true →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨[],w.val⟩ (List.ofFn y) = true
    simpa [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.getD_eq_getElem?_getD] using hxy w
  | @push s p op a b ih =>
    refine Fin.lastCases ?_ (fun i => ?_) w
    · intro h
      have hx : op.eval (p.read x a) (p.read x b) = true :=
        (p.read_new x op a b).symm.trans h
      exact (p.read_new y op a b).trans (op.eval_mono (ih a) (ih b) hx)
    · rw [Program.read_old, Program.read_old]
      exact ih i

theorem Ref.read_mono (P : Program n s) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) (a : Ref (n+s)) :
    Ref.read P x a = true → Ref.read P y a = true := by
  cases a with
  | const b => exact id
  | wire w => exact P.read_mono hxy w

theorem Signal.read_mono (S : Machine n) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) (a : Signal) :
    a.read S x = true → a.read S y = true := by
  rw [← Signal.read_asRef, ← Signal.read_asRef]
  exact Ref.read_mono S.2 hxy (a.asRef S)

theorem input_mono {n : Nat} {X X' Y Y' : Finset (Fin n)}
    (hx : X ⊆ X') (hy : Y ⊆ Y') (i : Fin (n+n)) :
    input X Y i = true → input X' Y' i = true := by
  refine Fin.addCases ?_ ?_ i
  · intro p
    simpa only [input,Fin.append_left,decide_eq_true_eq] using fun h : p ∈ X => hx h
  · intro l
    simpa only [input,Fin.append_right,decide_eq_true_eq] using fun h : l ∈ Y => hy h

end Refute2003

namespace Refute2003
open BundleBuild

theorem affineGoodForAll {K : Type} [Field K] [Fintype K]
    (lab : Label K ≃ Fin n) (aff : Code (n+n) Signal) (q : Nat) (positive : 1 ≤ q)
    (promise : ∀ X Y : Finset (Fin n), Y.card ≤ q →
      (Y.card ≤ 1 ∨ ¬affineHit (fun p => lab p ∈ X) (fun l => lab l ∈ Y)) →
      Good (physicalSem (input X Y)) (Machine.empty (n+n)) aff (fun t a =>
        Truth t (input X Y) a (affineHit (fun p => lab p ∈ X) (fun l => lab l ∈ Y)))) :
    ∀ X Y : Finset (Fin n), Y.card ≤ q →
      Good (physicalSem (input X Y)) (Machine.empty (n+n)) aff (fun t a =>
        Truth t (input X Y) a (affineHit (fun p => lab p ∈ X) (fun l => lab l ∈ Y))) := by
  intro X Y hY
  by_cases ha : affineHit (fun p => lab p ∈ X) (fun l => lab l ∈ Y)
  · obtain ⟨ab, hLine,u,hPoint⟩ := ha
    let p := lab (.inl (u, ab.1*u+ab.2))
    let l := lab (.inl ab)
    have ha' : affineHit (fun p' => lab p' ∈ ({p} : Finset (Fin n)))
        (fun l' => lab l' ∈ ({l} : Finset (Fin n))) := by
      exact ⟨ab, Finset.mem_singleton_self _, u, Finset.mem_singleton_self _⟩
    have h := promise {p} {l} (by simp; omega) (Or.inl (by simp))
    let r := aff.run (Machine.empty (n+n))
    have ht : r.1.read r.2 (input {p} {l}) = true := h.2.2.mpr ha'
    have hp' : ({p} : Finset (Fin n)) ⊆ X := Finset.singleton_subset_iff.mpr hPoint
    have hl' : ({l} : Finset (Fin n)) ⊆ Y := Finset.singleton_subset_iff.mpr hLine
    have hm := Signal.read_mono r.2 (input_mono hp' hl') r.1 ht
    exact ⟨h.1, h.2.1, fun _ => ⟨ab,hLine,u,hPoint⟩, fun _ => hm⟩
  · exact promise X Y hY (Or.inr ha)

end Refute2003

namespace Refute2003
namespace WordAlgebra
open scoped BigOperators

abbrev Rail := Bool → Prop
abbrev RWord (w : Nat) := Fin w → Rail

def coded (b : Bool) : Rail := fun v => b = v

def codedWord (f : Fin w → Bool) : RWord w := fun i => coded (f i)

def railLE (r s : Rail) : Prop := ∀ b, r b → s b
def wordLE (r s : RWord w) : Prop := ∀ i, railLE (r i) (s i)

def andR (a b : Rail) : Rail
  | true => a true ∧ b true
  | false => a false ∨ b false

def xorR (a b : Rail) : Rail
  | true => (a true ∧ b false) ∨ (a false ∧ b true)
  | false => (a true ∧ b true) ∨ (a false ∧ b false)

theorem andR_mono {a a' b b' : Rail} (h : railLE a a') (h' : railLE b b') :
    railLE (andR a b) (andR a' b') := by
  intro z hz
  cases z
  · exact hz.elim (fun u => Or.inl (h _ u)) (fun u => Or.inr (h' _ u))
  · exact ⟨h _ hz.1, h' _ hz.2⟩

theorem xorR_mono {a a' b b' : Rail} (h : railLE a a') (h' : railLE b b') :
    railLE (xorR a b) (xorR a' b') := by
  intro z hz
  cases z <;>
    exact hz.elim (fun u => Or.inl ⟨h _ u.1,h' _ u.2⟩) (fun u => Or.inr ⟨h _ u.1,h' _ u.2⟩)

theorem andR_coded (a b : Bool) : andR (coded a) (coded b) = coded (a && b) := by
  funext z
  apply propext
  cases a <;> cases b <;> cases z <;> simp [andR, xorR, coded]

theorem xorR_coded (a b : Bool) : xorR (coded a) (coded b) = coded (a ^^ b) := by
  funext z
  apply propext
  cases a <;> cases b <;> cases z <;> simp [andR, xorR, coded]

theorem fold_rel {A B C : Type*} (I : B → C → Prop) (xs : List A)
    (f : B → A → B) (g : C → A → C) (b : B) (c : C)
    (h₀ : I b c) (hs : ∀ a ∈ xs, ∀ x y, I x y → I (f x a) (g y a)) :
    I (xs.foldl f b) (xs.foldl g c) := by
  induction xs generalizing b c with
  | nil => exact h₀
  | cons a as ih =>
    exact ih (f b a) (g c a) (hs a (by simp) _ _ h₀)
      (fun i hi => hs i (List.mem_cons_of_mem _ hi))

def addR (a b : RWord w) : RWord w := fun i => xorR (a i) (b i)

def selectedPairs (w : Nat) (f : Fin w → Fin w → Bool) : List (Fin w × Fin w) :=
  ((List.finRange w).flatMap (fun j => (List.finRange w).map (fun k => (j,k)))).filter
    (fun jk => f jk.1 jk.2)

def mulR (c : Fin w → Fin w → Fin w → Bool) (a b : RWord w) : RWord w :=
  fun i => (selectedPairs w (c i)).foldl
    (fun e jk => xorR e (andR (a jk.1) (b jk.2))) (coded false)

def affineR (M : Fin o → Fin w → Bool) (c : Fin o → Bool) (a : RWord w) : RWord o :=
  fun j => ((List.finRange w).filter (M j)).foldl (fun p i => xorR p (a i)) (coded (c j))

def hornerR (c : Fin w → Fin w → Fin w → Bool) (cs : List (Fin w → Bool))
    (a : RWord w) : RWord w :=
  cs.foldl (fun s k => addR (mulR c s a) (codedWord k)) (codedWord (fun _ => false))

theorem addR_mono {a a' b b' : RWord w} (ha : wordLE a a') (hb : wordLE b b') :
    wordLE (addR a b) (addR a' b') := fun i => xorR_mono (ha i) (hb i)

theorem mulR_mono (c : Fin w → Fin w → Fin w → Bool) {a a' b b' : RWord w}
    (ha : wordLE a a') (hb : wordLE b b') : wordLE (mulR c a b) (mulR c a' b') := by
  intro i
  exact fold_rel railLE (selectedPairs w (c i)) _ _ _ _ (fun _ h => h)
    (fun jk _ x y h => xorR_mono h (andR_mono (ha jk.1) (hb jk.2)))

theorem affineR_mono (M : Fin o → Fin w → Bool) (c : Fin o → Bool) {a a' : RWord w}
    (h : wordLE a a') : wordLE (affineR M c a) (affineR M c a') := by
  intro i
  exact fold_rel railLE ((List.finRange w).filter (M i)) _ _ _ _ (fun _ hx => hx)
    (fun j _ x y hx => xorR_mono hx (h j))

theorem hornerR_mono (c : Fin w → Fin w → Fin w → Bool) (cs : List (Fin w → Bool))
    {a a' : RWord w} (h : wordLE a a') : wordLE (hornerR c cs a) (hornerR c cs a') :=
  fold_rel wordLE cs _ _ _ _ (fun _ _ hp => hp)
    (fun k _ x y hx => addR_mono (mulR_mono c hx h) (fun _ _ hk => hk))

def affineWord (M : Fin o → Fin w → Bool) (c : Fin o → Bool) (a : Fin w → Bool) :
    Fin o → Bool :=
  fun j => ((List.finRange w).filter (M j)).foldl (fun p i => p ^^ a i) (c j)

theorem affineR_coded (M : Fin o → Fin w → Bool) (c : Fin o → Bool) (a : Fin w → Bool) :
    affineR M c (codedWord a) = codedWord (affineWord M c a) := by
  funext j
  exact fold_rel (fun r k => r = coded k) ((List.finRange w).filter (M j)) _ _ _ _ rfl
    (fun i _ r k hr => by rw [hr]; exact xorR_coded k (a i))

def bit (x : ZMod 2) : Bool := decide (x = 1)

theorem bit_zero : bit 0 = false := by decide
theorem bit_one : bit 1 = true := by decide
theorem bit_add (a b : ZMod 2) : bit (a+b) = (bit a ^^ bit b) := by
  revert a b
  decide
theorem bit_mul (a b : ZMod 2) : bit (a*b) = (bit a && bit b) := by
  revert a b
  decide
theorem bit_injective : Function.Injective bit := by
  have h : ∀ a b : ZMod 2, bit a = bit b → a = b := by decide
  exact fun {a b} => h a b

theorem zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem foldXorCode {A : Type*} (xs : List A) (f : A → ZMod 2) (init : ZMod 2) :
    xs.foldl (fun acc a => xorR acc (coded (bit (f a)))) (coded (bit init)) =
      coded (bit (init + (xs.map f).sum)) := by
  induction xs generalizing init with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [xorR_coded, ← bit_add, ih, add_assoc]

private theorem sum_finList {A : Type*} [AddCommMonoid A] (w : Nat) (f : Fin w → A) :
    ((List.finRange w).map f).sum = ∑ i, f i := by
  induction w with
  | zero => simp
  | succ w ih => simp [List.finRange_succ, List.map_map, Function.comp_def, ih, Fin.sum_univ_succ]

private theorem sum_productList {A : Type*} [AddCommMonoid A] (w : Nat)
    (f : Fin w × Fin w → A) :
    (((List.finRange w).flatMap (fun j => (List.finRange w).map (fun k => (j,k)))).map f).sum =
      ∑ j, ∑ k, f (j,k) := by
  have h (xs : List (Fin w)) :
      ((xs.flatMap (fun j => (List.finRange w).map (fun k => (j,k)))).map f).sum =
        (xs.map (fun j => ∑ k : Fin w, f (j,k))).sum := by
    induction xs with
    | nil => rfl
    | cons j js ih =>
      simp [List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
        Function.comp_def, sum_finList, ih]
  rw [h, sum_finList]

private theorem sum_filtered {A : Type*} (xs : List A) (f c : A → ZMod 2) :
    (((xs.filter fun a => bit (c a)).map f).sum) = (xs.map fun a => c a * f a).sum := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rcases zero_or_one (c a) with h | h <;> simp [h, bit_zero, bit_one, ih]

private theorem foldBit {A : Type*} (xs : List A) (f : A → ZMod 2) (init : ZMod 2) :
    xs.foldl (fun acc a => acc ^^ bit (f a)) (bit init) =
      bit (init + (xs.map f).sum) := by
  induction xs generalizing init with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [← bit_add, ih, add_assoc]

theorem affineWord_sum (M : Fin o → Fin w → ZMod 2) (c : Fin o → ZMod 2)
    (a : Fin w → ZMod 2) (j : Fin o) :
    affineWord (fun j i => bit (M j i)) (fun j => bit (c j)) (fun i => bit (a i)) j =
      bit (c j + ∑ i, M j i * a i) := by
  simp only [affineWord, foldBit, sum_filtered, sum_finList]

theorem affineWord_linear (M : Fin o → Fin w → ZMod 2) (a : Fin w → ZMod 2) (j : Fin o) :
    affineWord (fun j i => bit (M j i)) (fun _ => false) (fun i => bit (a i)) j =
      bit (∑ i, M j i * a i) := by
  simpa only [bit_zero,zero_add] using affineWord_sum M (fun _ => 0) a j

section Coordinates
variable {K : Type*} [Field K] [Algebra (ZMod 2) K]
variable (b : Module.Basis (Fin w) (ZMod 2) K)

noncomputable def code (x : K) : Fin w → Bool := fun i => bit (b.coord i x)

theorem code_injective : Function.Injective (code b) := by
  intro u v h
  apply b.repr.injective
  ext i
  exact bit_injective (congrFun h i)

theorem code_surjective : Function.Surjective (code b) := by
  intro f
  let g : Fin w → ZMod 2 := fun i => if f i then 1 else 0
  refine ⟨b.equivFun.symm g, ?_⟩
  funext i
  have he : b.coord i (b.equivFun.symm g) = g i := by
    rw [Module.Basis.coord_apply, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp only [code, he, g]
  cases f i <;> simp [bit_zero, bit_one]

noncomputable def codeEquiv : K ≃ (Fin w → Bool) :=
  Equiv.ofBijective (code b) ⟨code_injective b, code_surjective b⟩

@[simp] theorem codeEquiv_apply (x : K) : codeEquiv b x = code b x := rfl

noncomputable def constants (i j k : Fin w) : Bool := bit (b.coord i (b j * b k))

theorem coord_mul (x y : K) (i : Fin w) :
    b.coord i (x*y) = ∑ j, ∑ k, b.coord i (b j * b k) * (b.coord j x * b.coord k y) := by
  calc
    _ = b.coord i ((∑ j, b.coord j x • b j) * (∑ k, b.coord k y • b k)) := by
      simp only [Module.Basis.coord_apply, Module.Basis.sum_repr]
    _ = _ := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum, map_sum, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem code_zero : code b 0 = fun _ => false := by
  funext j
  simp [code, bit_zero]

theorem addR_coded (x y : K) :
    addR (codedWord (code b x)) (codedWord (code b y)) = codedWord (code b (x+y)) := by
  funext i
  simp only [addR, codedWord, code, map_add, bit_add, xorR_coded]

theorem mulR_coded (x y : K) :
    mulR (constants b) (codedWord (code b x)) (codedWord (code b y)) =
      codedWord (code b (x*y)) := by
  funext i
  simp only [mulR, codedWord, code, andR_coded, ← bit_mul]
  rw [← bit_zero]
  rw [foldXorCode, zero_add]
  change coded (bit ((((List.finRange w).flatMap (fun j => (List.finRange w).map
      (fun k => (j,k)))).filter (fun jk => bit (b.coord i (b jk.1 * b jk.2)))).map
      (fun jk => b.coord jk.1 x * b.coord jk.2 y)).sum) = _
  rw [sum_filtered, sum_productList, ← coord_mul]

theorem hornerR_coded (cs : List K) (x : K) :
    hornerR (constants b) (cs.map (code b)) (codedWord (code b x)) =
      codedWord (code b (cs.foldl (fun a k => a*x+k) 0)) := by
  unfold hornerR
  rw [List.foldl_map]
  apply fold_rel (fun r z => r = codedWord (code b z)) cs _ _ _ _ (by rw [code_zero])
  intro k _ r z hr
  rw [hr, mulR_coded, addR_coded]

end Coordinates

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev BinaryField (w : Nat) := GaloisField 2 w

noncomputable def binaryFintype (w : Nat) : Fintype (BinaryField w) := Fintype.ofFinite _

theorem binaryCard (w : Nat) (hw : w ≠ 0) :
    @Fintype.card (BinaryField w) (binaryFintype w) = 2^w := by
  letI := binaryFintype w
  change Fintype.card (BinaryField w) = 2^w
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 w hw

noncomputable def binaryBasis (w : Nat) (hw : w ≠ 0) :
    Module.Basis (Fin w) (ZMod 2) (BinaryField w) :=
  Module.finBasisOfFinrankEq (ZMod 2) (BinaryField w) (GaloisField.finrank 2 hw)

end WordAlgebra
end Refute2003

namespace Refute2003
namespace BundleBuild
open WordAlgebra

section GenericWord
variable {S W : Type} [Inhabited (Ops (StateM S) W)] (v : Sem S W)

def DualRep (s : S) (a : Dual W) (r : Rail) : Prop :=
  ∀ z, v.rep s (selected a z) (r z)

theorem DualRep.extend {s t : S} {a : Dual W} {r : Rail}
    (h : DualRep v s a r) (he : v.ext s t) : DualRep v t a r :=
  fun z => v.stabilize he (h z)

theorem dualConst_correct (s : S) (b : Bool) :
    DualRep v s (dualConst (M := StateM S) (W := W) b) (coded b) := by
  intro z
  cases z with
  | true => exact v.konst s b
  | false =>
    exact v.congr (by cases b <;> simp [coded]) (v.konst s (!b))

theorem dualAnd_correct {s : S} {a b : Dual W} {p q : Rail}
    (ha : DualRep v s a p) (hb : DualRep v s b q) :
    Good v s (dualAnd a b) (fun t d => DualRep v t d (andR p q)) := by
  unfold dualAnd
  apply Good.bind v (land_good v (ha true) (hb true))
  intro t pos hst hp
  apply Good.bind v (lor_good v (v.stabilize hst (ha false)) (v.stabilize hst (hb false)))
  intro u neg htu hn
  apply Good.ret
  intro z
  cases z
  · exact hn
  · exact v.stabilize htu hp

theorem dualXor_correct {s : S} {a b : Dual W} {p q : Rail}
    (ha : DualRep v s a p) (hb : DualRep v s b q) :
    Good v s (dualXor a b) (fun t d => DualRep v t d (xorR p q)) := by
  unfold dualXor
  apply Good.bind v (land_good v (ha true) (hb false))
  intro s₁ p₁ e₁ P₁
  apply Good.bind v (land_good v (v.stabilize e₁ (ha false)) (v.stabilize e₁ (hb true)))
  intro s₂ p₂ e₂ P₂
  have e12 := v.trans e₁ e₂
  apply Good.bind v (land_good v (v.stabilize e12 (ha true)) (v.stabilize e12 (hb true)))
  intro s₃ n₁ e₃ N₁
  have e123 := v.trans e12 e₃
  apply Good.bind v (land_good v (v.stabilize e123 (ha false)) (v.stabilize e123 (hb false)))
  intro s₄ n₂ e₄ N₂
  apply Good.bind v (lor_good v (v.stabilize (v.trans e₂ (v.trans e₃ e₄)) P₁)
    (v.stabilize (v.trans e₃ e₄) P₂))
  intro s₅ pos e₅ P
  apply Good.bind v (lor_good v (v.stabilize (v.trans e₄ e₅) N₁) (v.stabilize e₅ N₂))
  intro s₆ neg e₆ N
  apply Good.ret
  intro z
  cases z
  · exact N
  · exact v.stabilize e₆ P

theorem foldWordM {A B C : Type} (xs : List A) (f : B → A → StateM S B)
    (g : C → A → C) (Rep : S → B → C → Prop)
    {s : S} {b : B} {c : C} (hb : Rep s b c)
    (step : ∀ a ∈ xs, ∀ t w z, v.ext s t → Rep t w z →
      Good v t (f w a) (fun u r => Rep u r (g z a))) :
    Good v s (xs.foldlM f b) (fun t r => Rep t r (xs.foldl g c)) := by
  induction xs generalizing s b c with
  | nil => exact Good.ret v s b _ hb
  | cons a as ih =>
    change Good v s (f b a >>= fun y => as.foldlM f y)
      (fun t r => Rep t r (as.foldl g (g c a)))
    apply Good.bind v (step a (by simp) s b c (v.refl s) hb)
    intro t w hst hw
    exact ih hw (fun a ha u x y e hy => step a (List.mem_cons_of_mem _ ha)
      u x y (v.trans hst e) hy)

theorem constWord_correct (s : S) (b : Fin w → Bool) :
    WordRep v s (fun i => dualConst (M := StateM S) (W := W) (b i)) (codedWord b) :=
  fun i => dualConst_correct v s (b i)

theorem addBits_correct {s : S} {a b : Word W w} {p q : RWord w}
    (ha : WordRep v s a p) (hb : WordRep v s b q) :
    Good v s (addBits a b) (fun t d => WordRep v t d (addR p q)) := by
  unfold addBits
  refine tab_correct v w _ (fun i t d => DualRep v t d (addR p q i)) ?_ ?_
  · intro i t u d ht hd
    exact DualRep.extend v hd ht
  · intro i t ht
    exact dualXor_correct v (DualRep.extend v (ha i) ht) (DualRep.extend v (hb i) ht)

theorem mulBits_correct {s : S} (c : Fin w → Fin w → Fin w → Bool)
    {a b : Word W w} {p q : RWord w} (ha : WordRep v s a p) (hb : WordRep v s b q) :
    Good v s (mulBits c a b) (fun t d => WordRep v t d (mulR c p q)) := by
  unfold mulBits
  refine tab_correct v w _ (fun i t d => DualRep v t d (mulR c p q i)) ?_ ?_
  · intro i t u d ht hd
    exact DualRep.extend v hd ht
  · intro i t ht
    exact foldWordM v (selectedPairs w (c i))
      (fun acc jk => do
        let prod ← dualAnd (a jk.1) (b jk.2)
        dualXor acc prod)
      (fun e jk => xorR e (andR (p jk.1) (q jk.2)))
      (DualRep v) (dualConst_correct v t false) (by
      intro jk _ u acc r htu hr
      have hsu := v.trans ht htu
      have h := dualAnd_correct v
        (DualRep.extend v (ha jk.1) hsu) (DualRep.extend v (hb jk.2) hsu)
      apply Good.bind v h
      intro u' prod hu' hprod
      exact dualXor_correct v (DualRep.extend v hr hu') hprod)

theorem affineBits_correct {s : S} (m : Fin o → Fin w → Bool) (c : Fin o → Bool)
    {a : Word W w} {p : RWord w} (ha : WordRep v s a p) :
    Good v s (affineBits m c a) (fun t d => WordRep v t d (affineR m c p)) := by
  unfold affineBits
  refine tab_correct v o _ (fun i t d => DualRep v t d (affineR m c p i)) ?_ ?_
  · intro i t u d ht hd
    exact DualRep.extend v hd ht
  · intro i t hst
    exact foldWordM v ((List.finRange w).filter (m i))
      (fun acc j => dualXor acc (a j)) (fun acc j => xorR acc (p j))
      (DualRep v) (dualConst_correct v t (c i)) (by
        intro j _ u x z htu hr
        exact dualXor_correct v hr (DualRep.extend v (ha j) (v.trans hst htu)))

theorem hornerBits_correct {s : S} (c : Fin w → Fin w → Fin w → Bool)
    (cs : List (Fin w → Bool)) {a : Word W w} {p : RWord w}
    (ha : WordRep v s a p) :
    Good v s (hornerBits c cs a) (fun t d => WordRep v t d (hornerR c cs p)) := by
  unfold hornerBits hornerR
  exact foldWordM v cs
    (fun acc k => do
      let prod ← mulBits c acc a
      addBits prod (fun j => dualConst (M := StateM S) (W := W) (k j)))
    (fun acc k => addR (mulR c acc p) (codedWord k))
    (WordRep v) (constWord_correct v s (fun _ => false)) (by
      intro k _ t acc r hst hr
      apply Good.bind v (mulBits_correct v c hr (WordRep.extend v ha hst))
      intro u prod htu hp
      exact addBits_correct v hp (constWord_correct v u k))

end GenericWord

section PolyColumn
variable {S W : Type} [Inhabited (Ops (StateM S) W)]
variable {K : Type*} [Field K] [Algebra (ZMod 2) K]
variable (basis : Module.Basis (Fin w) (ZMod 2) K)

def columnBits (c : Fin w → Fin w → Fin w → Bool) (x : Fin w → Bool)
    (ab : Word W (w+w)) : StateM S (Word W w) := do
  let p ← mulBits c (fun i => dualConst (M := StateM S) (W := W) (x i))
    (fun i => ab (i.castAdd w))
  addBits p (fun i => ab (i.natAdd w))

def columnR (c : Fin w → Fin w → Fin w → Bool) (x : Fin w → Bool)
    (ab : RWord (w+w)) : RWord w :=
  addR (mulR c (codedWord x) (fun i => ab (i.castAdd w))) (fun i => ab (i.natAdd w))

def lowWord (hle : o ≤ w) (a : Word W w) : Word W o := fun j => a (j.castLE hle)

def polyCheckBits (c : Fin w → Fin w → Fin w → Bool) (cs : List (Fin w → Bool))
    (hle : o ≤ w) (want : Fin o → Bool) (a : Word W w) : StateM S W := do
  let b ← hornerBits c cs a
  sameWord (lowWord hle b) want

def polyCheckR (c : Fin w → Fin w → Fin w → Bool) (cs : List (Fin w → Bool))
    (hle : o ≤ w) (want : Fin o → Bool) (a : RWord w) : Prop :=
  ∀ j, hornerR c cs a (Fin.castLE hle j) (want j)

theorem polyCheck_mono (c : Fin w → Fin w → Fin w → Bool) (cs : List (Fin w → Bool))
    (hle : o ≤ w) (want : Fin o → Bool) : RailsMono (polyCheckR c cs hle want) := by
  intro a b hab ha j
  exact hornerR_mono c cs hab _ _ (ha j)

theorem polyCheckBits_correct (v : Sem S W) {s : S}
    (c : Fin w → Fin w → Fin w → Bool) (cs : List (Fin w → Bool))
    (hle : o ≤ w) (want : Fin o → Bool) {a : Word W w} {p : RWord w}
    (ha : WordRep v s a p) :
    Good v s (polyCheckBits c cs hle want a) (fun t z => v.rep t z (polyCheckR c cs hle want p)) := by
  unfold polyCheckBits
  apply Good.bind v (hornerBits_correct v c cs ha)
  intro t b htb hb
  exact sameWord_correct v want (fun j z => hb (j.castLE hle) z)

theorem columnBits_correct (v : Sem S W) {s : S}
    (c : Fin w → Fin w → Fin w → Bool) (x : Fin w → Bool)
    {ab : Word W (w+w)} {p : RWord (w+w)} (ha : WordRep v s ab p) :
    Good v s (columnBits c x ab) (fun t a => WordRep v t a (columnR c x p)) := by
  unfold columnBits columnR
  apply Good.bind v (mulBits_correct v c (constWord_correct v s x) (fun j => ha (j.castAdd w)))
  intro t b htb hb
  exact addBits_correct v hb (fun j => WordRep.extend v ha htb (j.natAdd w))

noncomputable def pairCode (ab : K × K) : Fin (w+w) → Bool :=
  Fin.append (code basis ab.1) (code basis ab.2)

theorem columnR_code (u : K) (ab : K × K) :
    columnR (constants basis) (code basis u) (codedWord (pairCode basis ab)) =
      codedWord (code basis (ab.1*u+ab.2)) := by
  unfold columnR
  have hl : (fun i : Fin w => codedWord (pairCode basis ab) (i.castAdd w)) =
      codedWord (code basis ab.1) := by funext i z; simp only [codedWord,pairCode,Fin.append_left,Fin.append_right]
  have hr : (fun i : Fin w => codedWord (pairCode basis ab) (i.natAdd w)) =
      codedWord (code basis ab.2) := by funext i z; simp only [codedWord,pairCode,Fin.append_left,Fin.append_right]
  rw [hl,hr,mulR_coded,addR_coded,mul_comm u]

noncomputable def renderColumn (v : Sem S W)
    (label : α → K × K) (address : K ≃ Fin q) (u : K) :
    MapCheck v (fun a => pairCode basis (label a)) (fun i => code basis (address.symm i))
      (fun a => address ((label a).1 * u + (label a).2))
      (columnBits (constants basis) (code basis u)) where
  spec := columnR (constants basis) (code basis u)
  mono := fun h => addR_mono
    (mulR_mono _ (fun _ _ h => h) (fun i => h (i.castAdd w)))
    (fun i => h (i.natAdd w))
  singleton := by
    intro a
    change columnR (constants basis) (code basis u) (codedWord (pairCode basis (label a))) =
      codedWord (code basis (address.symm (address ((label a).1 * u + (label a).2))))
    rw [Equiv.symm_apply_apply]
    exact columnR_code basis u (label a)
  good := fun s a p h => columnBits_correct v (constants basis) (code basis u) h

noncomputable def polyHash (buckets : (Fin o → Bool) ≃ Fin m) (hle : o ≤ w)
    (coeff : Fin r → List K) (value : α → K) (h : Fin r) (a : α) : Fin m :=
  buckets (fun j => code basis ((coeff h).foldl (fun z k => z * value a + k) 0) (j.castLE hle))

noncomputable def renderPolyHash (v : Sem S W)
    (buckets : (Fin o → Bool) ≃ Fin m) (hle : o ≤ w)
    (coeff : Fin r → List K) (value : α → K) :
    HashCheck v (fun a => code basis (value a)) (polyHash basis buckets hle coeff value)
      (fun h c => polyCheckBits (constants basis) ((coeff h).map (code basis)) hle (buckets.symm c)) where
  spec := fun h c => polyCheckR (constants basis) ((coeff h).map (code basis)) hle (buckets.symm c)
  mono := fun h c => polyCheck_mono _ _ _ _
  singleton := by
    intro h c a
    change (∀ j, hornerR (constants basis) ((coeff h).map (code basis))
      (codedWord (code basis (value a))) (j.castLE hle) (buckets.symm c j)) ↔ _
    rw [hornerR_coded]
    constructor
    · intro hj
      rw [polyHash, ← buckets.apply_symm_apply c]
      apply congrArg buckets
      funext j
      exact hj j
    · intro hp j
      have he := congrArg buckets.symm hp
      simp only [polyHash, Equiv.symm_apply_apply] at he
      exact congrFun he j
  good := fun h c s a p ha =>
    polyCheckBits_correct v _ _ hle (buckets.symm c) ha

end PolyColumn

section WordCost
variable {M : Type → Type} {W : Type} [Monad M] [Inhabited (Ops M W)] [Inhabited (Budget M)] [Fact (UnitGateBudget M W)]

theorem column_do_cost (c : Fin w → Fin w → Fin w → Bool) (x : Fin w → Bool)
    (ab : Word W (w+w)) :
    Budget.within (do
      let p ← mulBits (M := M) c (fun i => dualConst (M := M) (W := W) (x i))
        (fun i => ab (i.castAdd w))
      addBits p (fun i => ab (i.natAdd w))) (w*(w*w*8)+w*6) :=
  Budget.seq (mulBits_cost c _ _) (fun p => addBits_cost p _)

end WordCost
section AffineHash
variable {M : Type → Type} {W : Type} [Monad M] [Inhabited (Ops M W)]

def affineCheckBits (matrix : Fin o → Fin w → Bool) (offset : Fin o → Bool)
    (want : Fin o → Bool) (a : Word W w) : M W := do
  let b ← affineBits matrix offset a
  sameWord b want

theorem affineCheckBits_cost [Inhabited (Budget M)] [Fact (UnitGateBudget M W)]
    (matrix : Fin o → Fin w → Bool) (offset : Fin o → Bool)
    (want : Fin o → Bool) (a : Word W w) :
    Budget.within (affineCheckBits (M := M) matrix offset want a) (o*(w*6)+o) :=
  Budget.seq (affineBits_cost matrix offset a) (fun b => sameWord_cost b want)

def affineHash (buckets : (Fin o → Bool) ≃ Fin m) (matrix : Fin r → Fin o → Fin w → Bool)
    (offset : Fin r → Fin o → Bool) (word : α → Fin w → Bool) (h : Fin r) (a : α) : Fin m :=
  buckets (affineWord (matrix h) (offset h) (word a))

end AffineHash

section AffineHashCorrect
variable {S W : Type} [Inhabited (Ops (StateM S) W)]

def renderAffineHash (v : Sem S W) (buckets : (Fin o → Bool) ≃ Fin m)
    (matrix : Fin r → Fin o → Fin w → Bool) (offset : Fin r → Fin o → Bool)
    (word : α → Fin w → Bool) :
    HashCheck v word (affineHash buckets matrix offset word)
      (fun h c => affineCheckBits (matrix h) (offset h) (buckets.symm c)) where
  spec := fun h c rr => ∀ i, affineR (matrix h) (offset h) rr i (buckets.symm c i)
  mono := by
    intro h c a b hab ha i
    exact affineR_mono (matrix h) (offset h) hab _ _ (ha i)
  singleton := by
    intro h c a
    change (∀ i, affineR (matrix h) (offset h) (codedWord (word a)) i (buckets.symm c i)) ↔ _
    rw [affineR_coded]
    change (∀ i, affineWord (matrix h) (offset h) (word a) i = buckets.symm c i) ↔ _
    constructor
    · intro hh
      rw [affineHash, ← buckets.apply_symm_apply c]
      exact congrArg buckets (funext hh)
    · intro hh i
      have he := congrArg buckets.symm hh
      simp only [affineHash, Equiv.symm_apply_apply] at he
      exact congrFun he i
  good := by
    intro h c t a rr ha
    unfold affineCheckBits
    apply Good.bind v (affineBits_correct v (matrix h) (offset h) ha)
    intro u b htu hb
    exact sameWord_correct v (buckets.symm c) hb

end AffineHashCorrect

section ArithmeticCost
variable {S W : Type} [Inhabited (Ops (StateM S) W)] [Inhabited (Budget (StateM S))] [Fact (UnitGateBudget (StateM S) W)]

theorem columnBits_cost (c : Fin w → Fin w → Fin w → Bool) (x : Fin w → Bool)
    (ab : Word W (w+w)) :
    Budget.within (columnBits (S := S) c x ab) (w*(w*w*8)+w*6) :=
  column_do_cost c x ab

theorem polyCheckBits_cost (c : Fin w → Fin w → Fin w → Bool)
    (cs : List (Fin w → Bool)) (hle : o ≤ w) (want : Fin o → Bool) (a : Word W w) :
    Budget.within (polyCheckBits (S := S) c cs hle want a)
      (cs.length*(w*(w*w*8)+w*6)+o) :=
  Budget.seq (hornerBits_cost c cs a) (fun b => sameWord_cost (lowWord hle b) want)

end ArithmeticCost

end BundleBuild
end Refute2003

namespace Refute2003.BundleBuild

theorem projCharge_upper (r b ra ba w cm ck ch : Nat) :
    projCharge r b ra ba w cm ck ch ≤ ra*ba*r*(b+1)*(1+2*w)*(ck+cm+ch+5) := by
  let c := ck+cm+ch+5
  have h1 : b*((ck+cm+ch+1)+2)+1 ≤ (b+1)*c := by unfold c; nlinarith
  have h2 : b*((ck+cm+ch+2)+2)+1 ≤ (b+1)*c := by unfold c; nlinarith
  calc
    _ ≤ ra*(ba*(r*((b+1)*c)+w*(r*((b+1)*c)+r*((b+1)*c)))) := by
      unfold projCharge
      gcongr
    _ = _ := by unfold c; ring

theorem aggCharge_upper (r b w H B c : Nat) :
    aggCharge r b w H B c ≤ H*B*r*(b+1)*(1+2*w)*(c+4) := by
  have h1 : b*(c+2)+1 ≤ (b+1)*(c+4) := by nlinarith
  have h2 : b*((c+1)+2)+1 ≤ (b+1)*(c+4) := by nlinarith
  calc
    _ ≤ H*(B*(r*((b+1)*(c+4))+w*(r*((b+1)*(c+4))+r*((b+1)*(c+4))))) := by
      unfold aggCharge
      gcongr
    _ = _ := by ring

private theorem append_mul {a b : Nat} (hb : 1 ≤ b) : a ≤ a*b := by
  simpa using Nat.mul_le_mul_left a hb

private theorem append_mul_l {a b : Nat} (hb : 1 ≤ b) : a ≤ b*a := by
  simpa using Nat.mul_le_mul_right a hb

private theorem incpow {a i j : Nat} (ha : 1 ≤ a) (hij : i ≤ j) : a^i ≤ a^j :=
  Nat.pow_le_pow_right (by omega) hij

theorem projCharge_scaled {d T r b ra ba w cm ck ch : Nat}
    (hd : 1 ≤ d) (hT : 1 ≤ T) (hr : r ≤ 1000*d*T) (hra : ra ≤ 1000*d*T)
    (hb : b ≤ 4*T^2) (hba : ba ≤ 4*T^2) (hw : w ≤ 20*d) :
    projCharge r b ra ba w cm ck ch ≤ 820000000*d^3*T^6*(ck+cm+ch+5) := by
  have hT2 : 1 ≤ T^2 := Nat.one_le_pow _ _ (by omega)
  have hbu : b+1 ≤ 5*T^2 := by omega
  have hwu : 1+2*w ≤ 41*d := by omega
  calc
    _ ≤ ra*ba*r*(b+1)*(1+2*w)*(ck+cm+ch+5) := projCharge_upper ..
    _ ≤ (1000*d*T)*(4*T^2)*(1000*d*T)*(5*T^2)*(41*d)*(ck+cm+ch+5) := by gcongr
    _ = _ := by ring

theorem oneStep_scaled {q d T r b w H B c own : Nat}
    (hd : 1 ≤ d) (hT : 1 ≤ T) (hr : r ≤ 1000*d*T) (hb : b ≤ 4*T^2)
    (hw : w ≤ 20*d) (hH : H ≤ 1000*d) (hB : B ≤ 512*T)
    (hc : c ≤ 100000*d^3*T) (ho : own ≤ 10000*d^2) :
    stepCharge q r b w H B c own ≤ 10^22*d^7*(q+T^8) := by
  let U := d^7*(q+T^8)
  have hd2 : 1 ≤ d^2 := Nat.one_le_pow _ _ (by omega)
  have hT2 : 1 ≤ T^2 := Nat.one_le_pow _ _ (by omega)
  have hu1 : 1 ≤ d^3*T := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  have hu2 : 1 ≤ d^4*T^2 := Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  have hd23 : d^2 ≤ d^3 := incpow hd (by decide)
  have hd24 : d^2 ≤ d^4 := incpow hd (by decide)
  have hd27 : d^2 ≤ d^7 := incpow hd (by decide)
  have hd67 : d^6 ≤ d^7 := incpow hd (by decide)
  have hT18 : T ≤ T^8 := by simpa using incpow hT (show 1 ≤ 8 by decide)
  have hT58 : T^5 ≤ T^8 := incpow hT (by decide)
  have hbu : b+1 ≤ 5*T^2 := by omega
  have hwu : 1+2*w ≤ 41*d := by omega
  have hc3 : c+3 ≤ 100003*(d^3*T) := by
    have hu := hu1
    rw [show 100000*d^3*T = 100000*(d^3*T) by ring] at hc
    omega
  have hc4 : c+4 ≤ 100004*(d^3*T) := by omega
  have agg : aggCharge r b w H B c ≤ 10^18*U := by
    calc
      _ ≤ H*B*r*(b+1)*(1+2*w)*(c+4) := aggCharge_upper ..
      _ ≤ (1000*d)*(512*T)*(1000*d*T)*(5*T^2)*(41*d)*(100004*(d^3*T)) := by gcongr
      _ = 10496419840000000*(d^6*T^5) := by ring
      _ ≤ 10^18*(d^6*T^5) := Nat.mul_le_mul_right _ (by decide)
      _ ≤ _ := by
        unfold U
        gcongr
        exact hT58.trans (Nat.le_add_left _ _)
  have table : tableCharge q w H B ≤ 10^6*U := by
    have hwt : w+2 ≤ 22*d := by omega
    have hdd : d ≤ d^2 := by simpa using incpow hd (show 1 ≤ 2 by decide)
    calc
      _ ≤ (1000*d)*(q*(22*d)+512*T) := by unfold tableCharge; gcongr
      _ = 22000*d^2*q + 512000*d*T := by ring
      _ ≤ 10^6*d^2*q + 10^6*d^2*T := by gcongr <;> decide
      _ = 10^6*(d^2*(q+T)) := by ring
      _ ≤ _ := by unfold U; gcongr
  have filt : filterCharge H B c ≤ 51301539000*(d^4*T^2) := by
    have hBu : B+1 ≤ 513*T := by omega
    have hv : B*((c+1)+1)+1 ≤ (B+1)*(c+3) := by nlinarith
    calc
      _ ≤ H*((B+1)*(c+3)) := Nat.mul_le_mul_left _ hv
      _ ≤ (1000*d)*((513*T)*(100003*(d^3*T))) := by gcongr
      _ = _ := by ring
  have hcost : filterCharge H B c + 0 + own + 5 ≤ 52000000000*(d^4*T^2) := by
    have hmont : d^2 ≤ d^4*T^2 := hd24.trans (append_mul hT2)
    have hown : own ≤ 10000*(d^4*T^2) := ho.trans (Nat.mul_le_mul_left _ hmont)
    omega
  have proj : projCharge r b r b w 0 (filterCharge H B c) own ≤ 10^21*U := by
    calc
      _ ≤ 820000000*d^3*T^6*(filterCharge H B c+0+own+5) :=
        projCharge_scaled hd hT hr hr hb hb hw
      _ ≤ 820000000*d^3*T^6*(52000000000*(d^4*T^2)) := by gcongr
      _ = 42640000000000000000*(d^7*T^8) := by ring
      _ ≤ 10^21*(d^7*T^8) := Nat.mul_le_mul_right _ (by decide)
      _ ≤ _ := by unfold U; gcongr; exact Nat.le_add_left _ _
  unfold stepCharge
  calc
    _ ≤ 10^18*U+(10^6*U+10^21*U) := Nat.add_le_add agg (Nat.add_le_add table proj)
    _ = (10^18+10^6+10^21)*U := by ring
    _ ≤ 10^22*U := Nat.mul_le_mul_right _ (by decide)
    _ = _ := by unfold U; ring

theorem GroupCharge_scaled {q d T r b w ra ba wa e L cm own : Nat}
    (hd : 1 ≤ d) (hT : 1 ≤ T) (he : e+1 ≤ d)
    (hr : r ≤ 1000*d*T) (hra : ra ≤ 1000*d*T)
    (hb : b ≤ 4*T^2) (hba : ba ≤ 4*T^2) (hw : w ≤ 40*d) (hwa : wa ≤ 20*d)
    (hm : cm ≤ 100000*d^3) (ho : own ≤ 10000*d^2) :
    r*(L*(1+w*(1+1))) +
      q*((projCharge r b ra ba wa cm 0 own+((e+1)*(10^22*d^7*(q+T^8))+ba))+1) ≤
      10^24*d^8*(q^2+q*T^8+L*T) := by
  let D := d^8
  let U := q+T^8
  have hT28 : T^2 ≤ T^8 := incpow hT (by decide)
  have hT68 : T^6 ≤ T^8 := incpow hT (by decide)
  have hd28 : d^2 ≤ d^8 := incpow hd (by decide)
  have hd68 : d^6 ≤ d^8 := incpow hd (by decide)
  have hd23 : d^2 ≤ d^3 := incpow hd (by decide)
  have hd3 : 1 ≤ d^3 := Nat.one_le_pow _ _ (by omega)
  have hd2 : 1 ≤ d^2 := Nat.one_le_pow _ _ (by omega)
  have hD : 1 ≤ D := Nat.one_le_pow _ _ (by omega)
  have hU : 1 ≤ U := (Nat.one_le_pow _ _ (by omega)).trans (Nat.le_add_left _ _)
  have hg : 1+w*(1+1) ≤ 81*d := by omega
  have hh : 0+cm+own+5 ≤ 110005*d^3 := by
    have how := ho.trans (Nat.mul_le_mul_left 10000 hd23)
    omega
  have raw : r*(L*(1+w*(1+1))) ≤ 10^6*D*(L*T) := by
    calc
      _ ≤ (1000*d*T)*(L*(81*d)) := by gcongr
      _ = 81000*d^2*(L*T) := by ring
      _ ≤ _ := by unfold D; gcongr <;> decide
  have proj : projCharge r b ra ba wa cm 0 own ≤ 10^15*(D*U) := by
    calc
      _ ≤ 820000000*d^3*T^6*(0+cm+own+5) := projCharge_scaled hd hT hr hra hb hba hwa
      _ ≤ 820000000*d^3*T^6*(110005*d^3) := by gcongr
      _ = 90204100000000*(d^6*T^6) := by ring
      _ ≤ 10^15*(d^6*T^6) := Nat.mul_le_mul_right _ (by decide)
      _ ≤ _ := by
        unfold D U
        gcongr
        exact hT68.trans (Nat.le_add_left _ _)
  have stages' : (e+1)*(10^22*d^7*(q+T^8)) ≤ 10^22*(D*U) := by
    calc
      _ ≤ d*(10^22*d^7*(q+T^8)) := Nat.mul_le_mul_right _ he
      _ = _ := by unfold D U; ring
  have bu : ba ≤ 4*(D*U) := by
    apply hba.trans
    have htu : T^2 ≤ U := hT28.trans (Nat.le_add_left _ _)
    exact Nat.mul_le_mul_left _ (htu.trans (append_mul_l hD))
  have u1 : 1 ≤ D*U := Nat.mul_pos (by omega) (by omega)
  have column : projCharge r b ra ba wa cm 0 own+((e+1)*(10^22*d^7*(q+T^8))+ba)+1 ≤
      10^23*(D*U) := by
    calc
      _ ≤ 10^15*(D*U)+(10^22*(D*U)+4*(D*U))+(D*U) :=
        Nat.add_le_add (Nat.add_le_add proj (Nat.add_le_add stages' bu)) u1
      _ = (10^15+10^22+4+1)*(D*U) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by decide)
  calc
    _ ≤ 10^6*D*(L*T)+q*(10^23*(D*U)) := Nat.add_le_add raw (Nat.mul_le_mul_left _ column)
    _ ≤ 10^24*D*(L*T)+q*(10^24*(D*U)) := by gcongr <;> decide
    _ = _ := by unfold D U; ring

section Implement
variable {M : Type → Type} {W : Type} [Monad M] [Inhabited (Ops M W)] [Inhabited (Budget M)] [Fact (UnitGateBudget M W)]

theorem detectGroup_scaled {α : Type} {q r b w ra ba wa : Nat} (labels : List α)
    (word : α → Fin w → Bool) (hash : Fin r → α → Fin b) (Y : α → W)
    (addr : Fin q → Fin wa → Bool) (X : Fin q → Fin q → W)
    (map : Fin q → Word W w → M (Word W wa))
    (checks : Fin ra → Fin ba → Word W wa → M W)
    (layouts : Nat → Layout M W q wa) (e : Nat) (owner : Fin ra)
    (d T : Nat) (hd : 1 ≤ d) (hT : 1 ≤ T) (he : e+1 ≤ d)
    (hr : r ≤ 1000*d*T) (hra : ra ≤ 1000*d*T)
    (hb : b ≤ 4*T^2) (hba : ba ≤ 4*T^2) (hw : w ≤ 40*d) (hwa : wa ≤ 20*d)
    (hMap : ∀ u a, Budget.within (map u a) (100000*d^3))
    (hOwn : ∀ h c a, Budget.within (checks h c a) (10000*d^2))
    (hH : ∀ j ≤ e, (layouts j).hashes ≤ 1000*d)
    (hB : ∀ j ≤ e, (layouts j).buckets ≤ 512*T)
    (hCheck : ∀ j ≤ e, ∀ h c a, Budget.within ((layouts j).checkCell h c a) (100000*d^3*T))
    (part : ∀ j ≤ e, ∀ h, sumFin (layouts j).buckets (fun c => ((layouts j).entries h c).length) ≤ q) :
    Budget.within (detectGroup labels word hash Y addr X map checks layouts e owner)
      (10^24*d^8*(q^2+q*T^8+labels.length*T)) := by
  have hstep : ∀ u (j : Nat), j ≤ e → ∀ s,
      Budget.within (step s addr (X u) (layouts j) checks) (10^22*d^7*(q+T^8)) := by
    intro u j hj s
    exact Budget.weaken (oneStep_cost s addr (X u) (layouts j) checks _ _
      (hCheck j hj) hOwn (part j hj))
      (oneStep_scaled hd hT hra hba hwa (hH j hj) (hB j hj) (Nat.le_refl _) (Nat.le_refl _))
  exact Budget.weaken (detectGroup_cost labels word hash Y addr X map checks layouts e owner _ _ _
    hMap hOwn hstep) (GroupCharge_scaled hd hT he hr hra hb hba hw hwa (Nat.le_refl _) (Nat.le_refl _))

end Implement
end Refute2003.BundleBuild

namespace Refute2003.ConcreteGroup
open BundleBuild Bundle WordAlgebra

def width (k : Nat) := 20*k
def q (k : Nat) := 2^(width k)
def cap (k : Nat) := 2^k
def coeffWidth (k j : Nat) := 2^(min j k)
def H (k : Nat) := 20*k+(80*k+100)
def M (k j : Nat) := 512*coeffWidth k j
def PH (k : Nat) := 100*(k+1)*cap k
def pw (k : Nat) := 2*k+2
def PB (k : Nat) := 2^(pw k)

theorem PB_eq (k : Nat) : PB k = 4*(cap k)^2 := by
  unfold PB pw cap
  rw [pow_add, ←pow_mul]
  rw [Nat.mul_comm 2 k]
  ring

theorem H_eq (k : Nat) : H k = 100*(k+1) := by unfold H; omega

theorem coeffWidth_le (k j : Nat) : coeffWidth k j ≤ cap k :=
  Nat.pow_le_pow_right (by decide) (Nat.min_le_right j k)

theorem coeffWidth_eq {k j : Nat} (h : j ≤ k) : coeffWidth k j = 2^j := by
  simp [coeffWidth,h]

theorem low_le (k j : Nat) (hk : 0 < k) : min j k+9 ≤ width k := by
  have hh := Nat.min_le_right j k
  unfold width
  omega

noncomputable def halfBucket (k j : Nat) : (Fin (min j k+9) → Bool) ≃ Fin (M k j) :=
  (PolyHash.bitsFin _).trans (finCongr (by
    unfold M coeffWidth
    rw [pow_add]
    norm_num [Nat.mul_comm]))

structure Design (K : Type) (k : Nat) [Field K] [Algebra (ZMod 2) K] where
  pos : 0 < k
  basis : Module.Basis (Fin (width k)) (ZMod 2) K
  number : K ≃ Fin (q k)
  lineMatrix : Fin (PH k) → Fin (pw k) → Fin (width k + width k) → Bool
  addrMatrix : Fin (PH k) → Fin (pw k) → Fin (width k) → Bool
  coeff : ∀ j, Fin (H k) → Fin (coeffWidth k j) → K

section Data
variable {K : Type} [Field K] [Algebra (ZMod 2) K] {k : Nat} (D : Design K k)

noncomputable def addrWord : Fin (q k) → Fin (width k) → Bool :=
  code D.basis ∘ D.number.symm

noncomputable def lineWord : K×K → Fin (width k + width k) → Bool :=
  pairCode D.basis

noncomputable def coeffs (j : Nat) (h : Fin (H k)) : List K :=
  ((List.finRange (coeffWidth k j)).reverse.map (D.coeff j h))

noncomputable def linearHash {α : Type} {w : Nat} (word : α → Fin w → Bool)
    (mat : Fin (PH k) → Fin (pw k) → Fin w → Bool) :
    Fin (PH k) → α → Fin (PB k) :=
  fun h a => PolyHash.bitsFin (pw k) (affineWord (mat h) (fun _ => false) (word a))

noncomputable def ownLine : Fin (PH k) → K×K → Fin (PB k) :=
  linearHash (lineWord D) D.lineMatrix

noncomputable def ownAddr : Fin (PH k) → Fin (q k) → Fin (PB k) :=
  linearHash (addrWord D) D.addrMatrix

noncomputable def stageHash (j : Nat) : Fin (H k) → Fin (q k) → Fin (M k j) :=
  polyHash D.basis (halfBucket k j) (low_le k j D.pos) (coeffs D j) D.number.symm

noncomputable def projectLabel (u : Fin (q k)) (ab : K×K) : Fin (q k) :=
  D.number (ab.1 * D.number.symm u + ab.2)

theorem addrWord_injective : Function.Injective (addrWord D) :=
  (code_injective D.basis).comp D.number.symm.injective

theorem lineWord_injective : Function.Injective (lineWord D) := by
  intro a b e
  apply Prod.ext <;> apply code_injective D.basis <;> funext j
  · have h := congrFun e (j.castAdd (width k))
    simpa only [lineWord,pairCode,Fin.append_left] using h
  · have h := congrFun e (j.natAdd (width k))
    simpa only [lineWord,pairCode,Fin.append_right] using h

theorem stageHash_eq (j : Nat) (h : Fin (H k)) (a : Fin (q k)) :
    stageHash D j h a =
      (PolyHash.bucketEquiv (low_le k j D.pos) (codeEquiv D.basis)
        ((PolyHash.poly (D.coeff j h)).eval (D.number.symm a))).1 := by
  unfold stageHash polyHash coeffs
  rw [PolyHash.horner_reverse]
  rfl

structure DesignSound : Prop where
  perfectLine : ∀ A : Finset (K×K), A.card ≤ cap k → Perfect (ownLine D) A
  perfectAddr : ∀ A : Finset (Fin (q k)), A.card ≤ cap k → Perfect (ownAddr D) A
  isolated : ∀ j ≤ k, ∀ A : Finset (Fin (q k)), halfThreshold j < A.card → A.card ≤ 2^j →
    ∃ I : Finset (Fin (q k)), I ⊆ A ∧ A.card ≤ 2*I.card ∧ ∀ a ∈ I, ∃ h,
      Bundle.isolated (stageHash D j) A h a

end Data

section Physical
variable {S W : Type} [Inhabited (Ops (StateM S) W)]
variable {K : Type} [Field K] [Algebra (ZMod 2) K] {k : Nat} (D : Design K k)

noncomputable def linearCheck {w : Nat} (mat : Fin (PH k) → Fin (pw k) → Fin w → Bool)
    (h : Fin (PH k)) (c : Fin (PB k)) (a : Word W w) : StateM S W := do
  let bits ← affineBits (mat h) (fun _ => false) a
  sameWord bits ((PolyHash.bitsFin (pw k)).symm c)

def linearCheck_model {α : Type} {w : Nat} (v : Sem S W) (word : α → Fin w → Bool)
    (mat : Fin (PH k) → Fin (pw k) → Fin w → Bool) :
    HashCheck v word (linearHash word mat) (linearCheck mat) where
  spec := fun h c R => ∀ j, affineR (mat h) (fun _ => false) R j ((PolyHash.bitsFin (pw k)).symm c j)
  mono := by
    intro h c r s hr he j
    exact affineR_mono (mat h) (fun _ => false) hr j _ (he j)
  singleton := by
    intro h c a
    change (∀ j, affineR (mat h) (fun _ => false) (codedWord (word a)) j
      ((PolyHash.bitsFin (pw k)).symm c j)) ↔ _
    rw [affineR_coded]
    constructor
    · intro h'
      unfold linearHash
      rw [←(PolyHash.bitsFin (pw k)).apply_symm_apply c]
      apply congrArg (PolyHash.bitsFin (pw k))
      exact funext h'
    · intro e j
      have hh := congrArg (PolyHash.bitsFin (pw k)).symm e
      simp only [linearHash,Equiv.symm_apply_apply] at hh
      exact congrFun hh j
  good := by
    intro h c t a R ha
    apply Good.bind v (affineBits_correct v (mat h) (fun _ => false) ha)
    intro u out hu ho
    exact sameWord_correct v ((PolyHash.bitsFin (pw k)).symm c) ho

noncomputable def stageCheck (j : Nat) (h : Fin (H k)) (c : Fin (M k j))
    (a : Word W (width k)) : StateM S W :=
  polyCheckBits (constants D.basis) ((coeffs D j h).map (code D.basis)) (low_le k j D.pos)
    ((halfBucket k j).symm c) a

noncomputable def layouts (j : Nat) : Layout (StateM S) W (q k) (width k) :=
  staticLayout (stageHash D j) (stageCheck D j)

noncomputable def stageModel (v : Sem S W) (j : Nat) : StageModel v (addrWord D) (layouts D j) :=
  StageModel.ofStatic v (addrWord D) (stageHash D j) (stageCheck D j)
    (renderPolyHash D.basis v (halfBucket k j) (low_le k j D.pos) (coeffs D j) D.number.symm)

def owner (k : Nat) : Fin (PH k) :=
  ⟨0, by unfold PH cap; positivity⟩

noncomputable def group (labels : List (K×K)) (Y X : K×K → W) : StateM S W :=
  detectGroup labels (lineWord D) (ownLine D) Y (addrWord D) (fun u a => X (D.number.symm u,D.number.symm a))
    (fun u => columnBits (constants D.basis) (code D.basis (D.number.symm u)))
    (linearCheck D.addrMatrix) (layouts D) k (owner k)

theorem group_correct (v : Sem S W) (data : DesignSound D) {s : S}
    (labels : List (K×K)) (A : Finset (K×K))
    (Y X : K×K → W) (YP XP : K×K → Prop)
    (hy : ∀ a, v.rep s (Y a) (YP a)) (hx : ∀ p, v.rep s (X p) (XP p))
    (hmem : ∀ a, a ∈ A ↔ a ∈ labels ∧ YP a) (hcap : A.card ≤ cap k) :
    Good v s (group D labels Y X) (fun t out =>
      v.rep t out (∃ ab ∈ A, ∃ u : K, XP (u,ab.1*u+ab.2))) := by
  unfold group
  apply Good.post v (detectGroup_correct v labels (lineWord D) (ownLine D) Y YP A hy hmem
    (addrWord D) _ _ (fun u a => hx (D.number.symm u,D.number.symm a))
    (projectLabel D) _ (fun u => renderColumn D.basis v id D.number (D.number.symm u))
    (ownAddr D) (linearCheck D.addrMatrix) (linearCheck_model v (addrWord D) D.addrMatrix)
    (layouts D) (stageModel D v) k (owner k) hcap (data.perfectLine A hcap)
    data.perfectAddr data.isolated (addrWord_injective D))
  intro t out hh
  apply v.congr _ hh
  constructor
  · rintro ⟨ab, ha, u, hu⟩
    exact ⟨ab,ha,D.number.symm u,by simpa [projectLabel] using hu⟩
  · rintro ⟨ab, ha, u, hu⟩
    exact ⟨ab,ha,D.number u,by simpa [projectLabel] using hu⟩

end Physical

section Cost
variable {S W : Type} [Inhabited (Ops (StateM S) W)] [Inhabited (Budget (StateM S))] [Fact (UnitGateBudget (StateM S) W)]
variable {K : Type} [Field K] [Algebra (ZMod 2) K] {k : Nat} (D : Design K k)

theorem arith_cost_bound (k : Nat) :
    width k*(width k*width k*8)+width k*6 ≤ 65000*(k+1)^3 := by
  have hd : k ≤ k+1 := Nat.le_succ k
  have hp : k^3 ≤ (k+1)^3 := Nat.pow_le_pow_left hd 3
  have hd3 : k+1 ≤ (k+1)^3 := by
    simpa using Nat.pow_le_pow_right (show 0 < k+1 by omega) (show 1 ≤ 3 by decide)
  calc
    _ = 64000*k^3+120*k := by unfold width; ring
    _ ≤ 64000*(k+1)^3+120*(k+1)^3 :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hp) (Nat.mul_le_mul_left _ (hd.trans hd3))
    _ ≤ _ := by omega

theorem stageCheck_budget (j : Nat) (h : Fin (H k)) (c : Fin (M k j)) (a : Word W (width k)) :
    Budget.within (stageCheck (S := S) D j h c a) (100000*(k+1)^3*(cap k)) := by
  unfold stageCheck polyCheckBits
  apply Budget.weaken (Budget.seq (hornerBits_cost (constants D.basis) ((coeffs D j h).map (code D.basis)) a)
    (fun w => sameWord_cost (lowWord (low_le k j D.pos) w) ((halfBucket k j).symm c)))
  simp only [coeffs, List.length_map, List.length_reverse, List.length_finRange]
  have hd : 1 ≤ (k+1)^3*cap k := Nat.mul_pos (by positivity) (by unfold cap; positivity)
  have hw : min j k+9 ≤ 9*(k+1)^3*cap k := by
    have hp : k+1 ≤ (k+1)^3 := by
      simpa using Nat.pow_le_pow_right (show 0 < k+1 by omega) (show 1 ≤ 3 by decide)
    have hc : 1 ≤ cap k := Nat.one_le_pow _ _ (by decide)
    have hm : (k+1)^3 ≤ (k+1)^3*cap k := by
      calc
        _ = (k+1)^3*1 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hc
    have hr : k+1 ≤ (k+1)^3*cap k := hp.trans hm
    have hh := Nat.min_le_right j k
    rw [show 9*(k+1)^3*cap k = 9*((k+1)^3*cap k) by ring]
    omega
  calc
    _ ≤ (cap k)*(65000*(k+1)^3)+9*(k+1)^3*cap k :=
      Nat.add_le_add (Nat.mul_le_mul (coeffWidth_le k j) (arith_cost_bound k)) hw
    _ = 65009*(k+1)^3*cap k := by ring
    _ ≤ _ := by gcongr; decide

theorem linearCheck_budget (h : Fin (PH k)) (c : Fin (PB k)) (a : Word W (width k)) :
    Budget.within (linearCheck (S := S) D.addrMatrix h c a) (10000*(k+1)^2) := by
  unfold linearCheck
  apply Budget.weaken (Budget.seq (affineBits_cost (D.addrMatrix h) (fun _ => false) a)
    (fun w => sameWord_cost w ((PolyHash.bitsFin (pw k)).symm c)))
  unfold width pw
  nlinarith

theorem group_budget (labels : List (K×K)) (Y X : K×K → W) :
    Budget.within (group (S := S) D labels Y X)
      (10^24*(k+1)^8*((q k)^2+q k*(cap k)^8+labels.length*cap k)) := by
  unfold group
  apply detectGroup_scaled _ _ _ _ _ _ _ _ _ _ _ (k+1) (cap k)
  · omega
  · exact Nat.one_le_pow _ _ (by decide)
  · omega
  · rw [PH]; gcongr; decide
  · rw [PH]; gcongr; decide
  · rw [PB_eq]
  · rw [PB_eq]
  · unfold width; omega
  · unfold width; omega
  · intro u a
    exact Budget.weaken (column_do_cost (constants D.basis) (code D.basis (D.number.symm u)) a)
      ((arith_cost_bound k).trans (by gcongr; decide))
  · exact linearCheck_budget D
  · intro e _
    change H k ≤ _
    rw [H_eq]
    omega
  · intro j _
    change M k j ≤ _
    exact Nat.mul_le_mul_left _ (coeffWidth_le k j)
  · intro j _ h c a
    exact stageCheck_budget D j h c a
  · intro j _ h
    exact (staticLayout_entries_count (stageHash D j) (stageCheck D j) h).le

end Cost

def validSem (n : Nat) : Sem (Machine n) Signal where
  ext := Machine.Extends
  refl := Machine.Extends.refl
  trans := Machine.Extends.trans
  rep := fun S a _ => Signal.valid S a
  stabilize := Signal.valid_of_extends
  congr := fun _ h => h
  konst := fun _ _ => trivial
  land := fun {_ _ _ _ _} _ _ => ⟨emitCode_append .and _ _ _, emitCode_valid .and _ _ _⟩
  lor := fun {_ _ _ _ _} _ _ => ⟨emitCode_append .or _ _ _, emitCode_valid .or _ _ _⟩

theorem group_valid {K : Type} [Field K] [Algebra (ZMod 2) K] {k n : Nat}
    (D : Design K k) (sound : DesignSound D) {S : Machine n}
    (labels : List (K×K)) (Y X : K×K → Signal)
    (hy : ∀ a, (Y a).valid S) (hx : ∀ a, (X a).valid S) :
    let R := (group D labels Y X).run S
    S.Extends R.2 ∧ R.1.valid R.2 := by
  exact group_correct D (validSem n) sound labels ∅ Y X (fun _ => False) (fun _ => False)
    hy hx (by simp) (by simp)

end Refute2003.ConcreteGroup

namespace Refute2003.PerfectHash

open scoped BigOperators
noncomputable section
abbrev Seed (w m : ℕ) := Fin m → Fin w → ZMod 2
abbrev Word (w : ℕ) := Fin w → ZMod 2

def linear {w m : ℕ} (M : Seed w m) (a : Word w) : Word m :=
  fun j => ∑ i : Fin w, M j i * a i

def alter {w m : ℕ} (M : Seed w m) (i : Fin w) (e : Word m) : Seed w m :=
  fun j x => M j x + if x = i then e j else 0

theorem linear_alter {w m : ℕ} (M : Seed w m) (i : Fin w) (e : Word m)
    (a : Word w) (j : Fin m) :
    linear (alter M i e) a j = linear M a j + e j * a i := by
  unfold linear
  simp only [alter, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro x _ hn
    simp [hn]
  · simp

abbrev Same {w : ℕ} (m : ℕ) (a b : Word w) :=
  { M : Seed w m // linear M a = linear M b }

theorem pair_scaled {w m : ℕ} (a b : Word w) (hab : a ≠ b) :
    2^m * Fintype.card (Same m a b) ≤ Fintype.card (Seed w m) := by
  classical
  have hn : ∃ i, a i ≠ b i := by
    by_contra! h
    exact hab (funext h)
  obtain ⟨i,hi⟩ := hn
  let enc : Word m × Same m a b → Seed w m :=
    fun p => alter p.2.val i p.1
  have hval (e : Word m) (M : Same m a b) (j : Fin m) :
      linear (alter M.val i e) a j - linear (alter M.val i e) b j =
        e j * (a i - b i) := by
    rw [linear_alter, linear_alter, congrFun M.property j]
    ring
  have hine : Function.Injective enc := by
    rintro ⟨e,M⟩ ⟨e',M'⟩ he
    change alter M.val i e = alter M'.val i e' at he
    have hee : e = e' := by
      ext j
      apply mul_right_cancel₀ (sub_ne_zero.mpr hi)
      rw [← hval e M j, ← hval e' M' j, he]
    subst e'
    congr
    apply Subtype.ext
    ext j x
    exact add_right_cancel (congrFun (congrFun he j) x)
  have hw : Fintype.card (Word m) = 2^m := by simp [Word, Fintype.card_fun]
  simpa only [Fintype.card_prod, hw] using Fintype.card_le_of_injective enc hine

def goodOn {α : Type*} {w m : ℕ} (ρ : α ↪ Word w) (S : Finset α) (M : Seed w m) : Prop :=
  Set.InjOn (fun a => linear M (ρ a)) (S : Set α)

noncomputable def bad {α : Type*} {w m : ℕ} (ρ : α ↪ Word w) (S : Finset α)
    (M : Seed w m) : Bool := by
  classical
  exact decide (¬ goodOn ρ S M)

theorem bad_scaled {α : Type*} {w m : ℕ} (ρ : α ↪ Word w) (S : Finset α) :
    2^m * Fintype.card { M : Seed w m // bad ρ S M = true } ≤
      S.card^2 * Fintype.card (Seed w m) := by
  classical
  let P := { p : ↥S × ↥S // p.1 ≠ p.2 }
  let D : P → Type _ := fun p => Same m (ρ p.val.1.val) (ρ p.val.2.val)
  let B := { M : Seed w m // bad ρ S M = true }
  have hw (M : B) : ∃ p : P, linear M.val (ρ p.val.1.val) =
      linear M.val (ρ p.val.2.val) := by
    have hp : ¬ goodOn ρ S M.val := by
      simpa [bad] using M.property
    unfold goodOn Set.InjOn at hp
    push Not at hp
    obtain ⟨a,ha,b,hb,he,hne⟩ := hp
    exact ⟨⟨(⟨a,ha⟩,⟨b,hb⟩),fun h => hne (congrArg Subtype.val h)⟩,he⟩
  choose p hp using hw
  let enc : B → (Σ x : P, D x) := fun M => ⟨p M, ⟨M.val, hp M⟩⟩
  have he : Function.Injective enc := by
    intro M M' hh
    apply Subtype.ext
    exact congrArg (fun z : Sigma D => z.2.val) hh
  have hz : Fintype.card B ≤ ∑ z : P, Fintype.card (D z) := by
    simpa only [Fintype.card_sigma] using Fintype.card_le_of_injective enc he
  have hP : Fintype.card P ≤ S.card^2 := by
    simpa [P, pow_two] using (Fintype.card_le_of_injective
      (fun p : P => p.val) Subtype.val_injective)
  calc
    _ ≤ 2^m * (∑ z : P, Fintype.card (D z)) := Nat.mul_le_mul_left _ hz
    _ = ∑ z : P, 2^m * Fintype.card (D z) := Finset.mul_sum ..
    _ ≤ ∑ _z : P, Fintype.card (Seed w m) := by
      apply Finset.sum_le_sum
      intro z _
      exact pair_scaled _ _ (fun h => z.property (Subtype.ext (ρ.injective h)))
    _ = Fintype.card P * Fintype.card (Seed w m) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hP

theorem exists_perfect_family {α : Type*} [Fintype α] {w m T R : ℕ}
    (ρ : α ↪ Word w) (hbuck : 4*T^2 ≤ 2^m) (hchart : (w+1)*T < R) :
    ∃ fam : Fin R → Seed w m, ∀ S : Finset α, S.card ≤ T →
      ∃ j, goodOn ρ S (fam j) := by
  classical
  let P (i : Fin (T+1)) := ↥((Finset.univ : Finset α).powersetCard i.val)
  let Key := Sigma P
  let BB : Key → Seed w m → Bool := fun z M => bad ρ z.2.val M
  have hα : Fintype.card α ≤ 2^w := by
    simpa [Word, Fintype.card_fun] using Fintype.card_le_of_injective ρ ρ.injective
  have htwo (n : ℕ) : n+1 ≤ 2^n := by
    induction n with
    | zero => decide
    | succ n ih => rw [pow_succ]; omega
  have hKey : Fintype.card Key < (2^1)^R := by
    change Fintype.card (Sigma P) < _
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _i : Fin (T+1), (2^w)^T := by
        apply Finset.sum_le_sum
        intro i _
        simp only [P, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ]
        exact ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hα _)).trans
          (Nat.pow_le_pow_right (by positivity) (by have := i.isLt; omega))
      _ = (T+1)*(2^w)^T := by simp
      _ ≤ 2^T*(2^w)^T := Nat.mul_le_mul_right _ (htwo T)
      _ = 2^((w+1)*T) := by rw [Nat.add_mul, pow_add, pow_mul, one_mul]; exact Nat.mul_comm _ _
      _ < _ := by
        simp only [pow_one]
        exact Nat.pow_lt_pow_right (by decide : 1 < 2) hchart
  have hbad : ∀ z : Key, 2^1 * Fintype.card (Refute2003.HashCounting.BadChoice BB z) ≤
      Fintype.card (Seed w m) := by
    intro z
    let S := z.2.val
    let C := Fintype.card (Refute2003.HashCounting.BadChoice BB z)
    let H := Fintype.card (Seed w m)
    have hc : 2^m*C ≤ S.card^2*H := bad_scaled ρ S
    have hS : S.card ≤ T := by
      have hi := z.1.isLt
      have hz := (Finset.mem_powersetCard.mp z.2.property).2
      dsimp [S]
      omega
    have hs : 2^1 * (S.card^2 * H) ≤ 2^m*H := by
      simp only [pow_one, ← Nat.mul_assoc]
      apply Nat.mul_le_mul_right
      exact ((Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hS 2)).trans
        (Nat.mul_le_mul_right _ (show 2 ≤ 4 by decide))).trans hbuck
    apply Nat.le_of_mul_le_mul_left _ (show 0 < 2^m by positivity)
    calc
      _ = 2^1*(2^m*C) := by
        change 2^m*(2^1*C)=_
        ring
      _ ≤ 2^1*(S.card^2*H) := Nat.mul_le_mul_left _ hc
      _ ≤ _ := hs
  obtain ⟨fam,hfam⟩ := Refute2003.HashCounting.exists_family_of_constant_density BB R 1 hbad hKey
  refine ⟨fam, ?_⟩
  intro S hs
  let z : Key := ⟨⟨S.card, Nat.lt_succ_of_le hs⟩,
      ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, rfl⟩⟩⟩
  obtain ⟨j,hj⟩ := hfam z
  exact ⟨j, by simpa [BB,z,bad] using hj⟩

end
end Refute2003.PerfectHash

namespace Refute2003.ConcreteGroup
open BundleBuild Bundle WordAlgebra

def fromBool (x : Bool) : ZMod 2 := if x then 1 else 0

@[simp] theorem bit_fromBool (x : Bool) : bit (fromBool x) = x := by
  cases x <;> decide

theorem exists_bool_perfect {α : Type} [Fintype α] {w k : Nat}
    (word : α → Fin w → Bool) (inj : Function.Injective word)
    (hw : (w+1)*cap k < PH k) :
    ∃ mat : Fin (PH k) → Fin (pw k) → Fin w → Bool,
      ∀ A : Finset α, A.card ≤ cap k → Perfect (linearHash word mat) A := by
  let ρ : α ↪ PerfectHash.Word w := ⟨fun a i => fromBool (word a i), by
    intro a a' e
    apply inj
    funext i
    have h := congrArg bit (congrFun e i)
    simpa using h⟩
  have hB : 4*(cap k)^2 ≤ 2^(pw k) := (PB_eq k).ge
  obtain ⟨fam,hfam⟩ := PerfectHash.exists_perfect_family ρ hB hw
  refine ⟨fun h j i => bit (fam h j i), ?_⟩
  intro A hc
  obtain ⟨h, hh⟩ := hfam A hc
  refine ⟨h, ?_⟩
  intro a ha a' ha' e
  apply hh ha' ha
  have hword := (PolyHash.bitsFin (pw k)).injective e
  have hbool (a : α) (i : Fin w) : bit (ρ a i) = word a i := bit_fromBool _
  funext j
  have ec := congrFun hword j
  apply bit_injective
  calc
    _ = affineWord (fun j i => bit (fam h j i)) (fun _ => false) (word a') j := by
      simpa only [PerfectHash.linear, hbool] using
        (affineWord_linear (fam h) (ρ a') j).symm
    _ = affineWord (fun j i => bit (fam h j i)) (fun _ => false) (word a) j := ec
    _ = _ := by
      simpa only [PerfectHash.linear, hbool] using
        (affineWord_linear (fam h) (ρ a) j)

theorem PH_large (k w : Nat) (hw : w ≤ 40*k) : (w+1)*cap k < PH k := by
  unfold PH
  apply Nat.mul_lt_mul_of_pos_right _ (by unfold cap; positivity)
  omega

section Existence
variable {K : Type} [Field K] [Algebra (ZMod 2) K] [Fintype K]
variable {k : Nat}
variable (basis : Module.Basis (Fin (width k)) (ZMod 2) K) (number : K ≃ Fin (q k))

include number in
theorem exists_poly_coeff (hk : 0 < k) (j : Nat) :
    ∃ coeff : Fin (H k) → Fin (coeffWidth k j) → K,
      ∀ A : Finset K, A.Nonempty → A.card ≤ coeffWidth k j →
        ∃ h, A.card ≤ 2*(PolyHash.isolated A (fun a =>
          (PolyHash.bucketEquiv (low_le k j hk) (codeEquiv basis) ((PolyHash.poly (coeff h)).eval a)).1)).card := by
  have hK : Fintype.card K ≤ 2^(20*k) := by
    calc
      Fintype.card K = Fintype.card (Fin (q k)) := Fintype.card_congr number
      _ = q k := Fintype.card_fin _
      _ ≤ 2^(20*k) := Nat.le_refl _
  have hd : coeffWidth k j < 2^(80*k+100) := by
    apply Nat.pow_lt_pow_right (by decide : 1 < 2)
    have hh := Nat.min_le_right j k
    omega
  exact PolyHash.exists_polynomial_family
    (PolyHash.bucketEquiv (low_le k j hk) (codeEquiv basis)) (20*k) (80*k+100) hK hd

theorem pairCode_injective : Function.Injective (pairCode basis) := by
  intro a b e
  apply Prod.ext <;> apply code_injective basis <;> funext j
  · have h := congrFun e (j.castAdd (width k))
    simpa only [pairCode,Fin.append_left] using h
  · have h := congrFun e (j.natAdd (width k))
    simpa only [pairCode,Fin.append_right] using h

include basis number in
theorem exists_design (hk : 0 < k) :
    ∃ D : Design K k, DesignSound D := by
  classical
  obtain ⟨lineMat,hL⟩ := exists_bool_perfect (k := k) (pairCode basis)
    (pairCode_injective basis) (PH_large k _ (by unfold width; omega))
  obtain ⟨addrMat,hA⟩ := exists_bool_perfect (k := k) (fun a => code basis (number.symm a))
    ((code_injective basis).comp number.symm.injective) (PH_large k _ (by unfold width; omega))
  choose coeff hCoe using exists_poly_coeff basis number hk
  let D : Design K k := ⟨hk,basis,number,lineMat,addrMat,coeff⟩
  refine ⟨D, ⟨hL,hA,?_⟩⟩
  intro j hj A hSmall hAcard
  let E : Fin (q k) ↪ K := number.symm.toEmbedding
  let B := A.map E
  have hBcard : B.card = A.card := Finset.card_map E
  have hBne : B.Nonempty := Finset.card_pos.mp <| by omega
  have hBd : B.card ≤ coeffWidth k j := by rwa [hBcard,coeffWidth_eq hj]
  obtain ⟨h,hIso⟩ := hCoe j B hBne hBd
  let H₁ : K → Fin (M k j) := fun a =>
    (PolyHash.bucketEquiv (low_le k j hk) (codeEquiv basis) ((PolyHash.poly (coeff j h)).eval a)).1
  let J := PolyHash.isolated B H₁
  have hHash (a : Fin (q k)) : stageHash D j h a = H₁ (E a) := stageHash_eq D j h a
  let I := A.filter (fun a => Bundle.isolated (stageHash D j) A h a)
  have hIE : I.map E = J := by
    ext x
    constructor
    · intro hmem
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hmem
      have ha' := Finset.mem_filter.mp ha
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_map.mpr ⟨a,ha'.1,rfl⟩, ?_⟩
      intro b hb he
      obtain ⟨b',hb',rfl⟩ := Finset.mem_map.mp hb
      apply congrArg E
      exact ha'.2 b' hb' (by simpa only [hHash] using he)
    · intro hx
      have hx' := Finset.mem_filter.mp hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hx'.1
      apply Finset.mem_map.mpr
      refine ⟨a,Finset.mem_filter.mpr ⟨ha,?_⟩,rfl⟩
      intro b hb he
      apply E.injective
      apply hx'.2 (E b) (Finset.mem_map.mpr ⟨b,hb,rfl⟩)
      simpa only [hHash] using he
  have hIcard : I.card = J.card := by rw [← hIE,Finset.card_map]
  refine ⟨I, Finset.filter_subset _ _, ?_, ?_⟩
  · rw [hIcard, ← hBcard]
    exact hIso
  · intro a ha
    exact ⟨h,(Finset.mem_filter.mp ha).2⟩

end Existence

theorem exists_binary_design (k : Nat) (hk : 0 < k) :
    ∃ D : Design (BinaryField (width k)) k, DesignSound D := by
  letI := binaryFintype (width k)
  have hw : width k ≠ 0 := by unfold width; omega
  let number : BinaryField (width k) ≃ Fin (q k) :=
    Fintype.equivFinOfCardEq (binaryCard (width k) hw)
  exact exists_design (binaryBasis (width k) hw) number hk

theorem group_conditional {K : Type} [Field K] [Algebra (ZMod 2) K] {k n : Nat}
    (D : Design K k) (sound : DesignSound D) (input : Fin n → Bool) {s : Machine n}
    (labels : List (K×K)) (A : Finset (K×K))
    (Y X : K×K → Signal) (YP XP : K×K → Prop)
    (hy : ∀ a, Truth s input (Y a) (YP a)) (hx : ∀ p, Truth s input (X p) (XP p))
    (hmem : ∀ a, a ∈ A ↔ a ∈ labels ∧ YP a) :
    Good (physicalSem input) s (group D labels Y X) (fun t o =>
      ∃ P : Prop, Truth t input o P ∧ (A.card ≤ cap k → (P ↔ ∃ ab ∈ A, ∃ u : K, XP (u,ab.1*u+ab.2)))) := by
  by_cases hc : A.card ≤ cap k
  · exact Good.post _ (group_correct D (physicalSem input) sound labels A Y X YP XP hy hx hmem hc)
      (fun t o h => ⟨_,h,fun _ => Iff.rfl⟩)
  · have h := group_valid D sound labels Y X (fun a => (hy a).1) (fun p => (hx p).1)
    exact ⟨h.1,⟨_,⟨h.2,Iff.rfl⟩,fun h' => (hc h').elim⟩⟩

end Refute2003.ConcreteGroup

namespace Refute2003.OuterConcrete

open BundleBuild
open scoped BigOperators
noncomputable section

theorem binsWidth_le (k : Nat) (hk : 8 ≤ k) : 19*k+6 ≤ 2^k+1 := by
  have h (j : Nat) : 19*(8+j)+6 ≤ 2^(8+j) := by
    induction j with
    | zero => decide
    | succ j ih =>
      have hp : 19 ≤ 2^(8+j) :=
        (by decide : 19 ≤ 2^8).trans (Nat.pow_le_pow_right (by decide) (by omega))
      rw [show 8+(j+1) = (8+j)+1 by omega, pow_succ]
      omega
  have hj := h (k-8)
  rw [Nat.add_sub_of_le hk] at hj
  omega

theorem exists_charts {α : Type} [DecidableEq α] [Fintype α]
    (k : Nat) (hk : 8 ≤ k) (hα : Fintype.card α ≤ (Refute2003.Budget.q k)^2) :
    ∃ h : Fin (Refute2003.Budget.charts k) → α → Fin (Refute2003.Budget.bins k),
      Outer.GoodFamily h (Refute2003.Budget.q k) (Refute2003.Budget.cap k) := by
  let q := Refute2003.Budget.q k
  let T := Refute2003.Budget.cap k
  have H : q ≤ (T+1)*2^((19*k+6)-6) := by
    rw [show 19*k+6-6=19*k by omega]
    have hmul : q = T*2^(19*k) := by
      dsimp [q,T,Refute2003.Budget.q,Refute2003.Budget.cap]
      rw [← pow_add]
      congr 1
      omega
    rw [hmul]
    exact Nat.mul_le_mul_right _ (by omega)
  have Hα : Fintype.card α ≤ 2^(40*k) := by
    apply hα.trans
    unfold Refute2003.Budget.q
    rw [←pow_mul, show 20*k*2 = 40*k by omega]
  have HQ : q < 2^(60*k+100) := by
    apply Nat.pow_lt_pow_right (by decide)
    omega
  obtain ⟨h,hh⟩ := OuterCharts.exists_good_charts (Line := α) q T (19*k+6) (40*k) (60*k+100)
    (by omega) (binsWidth_le k hk) H Hα HQ
  have hr : Refute2003.Budget.charts k = 40*k+(60*k+100) := by
    unfold Refute2003.Budget.charts
    omega
  let e := finCongr hr
  let H (j : Fin (Refute2003.Budget.charts k)) (a : α) : Fin (Refute2003.Budget.bins k) := h (e j) a
  refine ⟨H, ?_⟩
  intro A hA hSize
  obtain ⟨i,hi⟩ := hh A hA hSize
  refine ⟨e.symm i, ?_⟩
  have he (a : α) : H (e.symm i) a = h i a := by
    unfold H
    rw [e.apply_symm_apply]
  have hf : Outer.light H (Refute2003.Budget.cap k) (e.symm i) A =
      Outer.light h T i A := by
    unfold Outer.light
    apply Finset.filter_congr
    intro a ha
    have hb : Outer.bucket H (e.symm i) (H (e.symm i) a) A =
        Outer.bucket h i (h i a) A := by
      unfold Outer.bucket
      apply Finset.filter_congr
      intro a' ha'
      rw [he,he] <;> rfl
    rw [hb]
  rw [hf]
  exact hi

open Refute2003.Budget in
def groupCoef (k : Nat) : Nat := 10^24*(k+1)^8

open Refute2003.Budget in
def affineCharge (k : Nat) : Nat :=
  rounds k *
    (charts k * (bins k * (groupCoef k * ((q k)^2 + q k * (cap k)^8)) +
                      (q k)^2 * (groupCoef k * cap k)) +
          (q k)^2*(charts k+1)) + (q k)^2

open Refute2003.Budget in
theorem final_charge_le (k : Nat) :
    affineCharge k + specialCost (q k) + 2 ≤ totalUnits k (2*10^24) 8 := by
  let Q := q k
  let T := cap k
  let R := charts k
  let J := rounds k
  let G := bins k
  let C := groupCoef k
  let phase := phaseUnits k
  have hQ : 1 ≤ Q := Nat.one_le_pow _ _ (by decide)
  have hQ2 : Q ≤ Q^2 := by
    rw [pow_two]
    simpa using (Nat.mul_le_mul_right Q hQ)
  have hQ2pos : 1 ≤ Q^2 := hQ.trans hQ2
  have hR : 1 ≤ R := by dsimp [R,charts]; omega
  have hC : 16 ≤ C := by
    change 16 ≤ (10^24)*(k+1)^8
    have hP : 1 ≤ (k+1)^8 := Nat.one_le_pow _ _ (by omega)
    exact (by decide : 16 ≤ 10^24).trans (by
      simpa only [Nat.mul_one] using (Nat.mul_le_mul_left (10^24) hP))
  have hC1 : 1 ≤ C := by omega
  have hTerms : Q^2*(R+1) ≤ C*R*Q^2 := by
    calc
      _ ≤ Q^2*(R+R) := Nat.mul_le_mul_left _ (by omega)
      _ = 2*R*Q^2 := by ring
      _ ≤ C*R*Q^2 := by gcongr <;> omega
  have hRound : R*(G*(C*(Q^2+Q*T^8))+Q^2*(C*T))+Q^2*(R+1) ≤ C*R*phase := by
    calc
      _ ≤ R*(G*(C*(Q^2+Q*T^8))+Q^2*(C*T)) + C*R*Q^2 :=
        Nat.add_le_add_left hTerms _
      _ = _ := by dsimp [phase,phaseUnits,Q,T,G]; ring
  have hBase : Q^2 + specialCost Q + 2 ≤ C*Q^2 := by
    calc
      _ = 3*Q^2+6*Q+6 := by unfold specialCost; ring
      _ ≤ 3*Q^2+6*Q^2+6*Q^2 := by
        apply Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hQ2) _)
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left 6 hQ2pos
      _ ≤ C*Q^2 := by
        rw [show 3*Q^2+6*Q^2+6*Q^2=15*Q^2 by ring]
        exact Nat.mul_le_mul_right _ (by omega)
  change J*(R*(G*(C*(Q^2+Q*T^8))+Q^2*(C*T))+Q^2*(R+1))+Q^2+specialCost Q+2
     ≤ totalUnits k (2*10^24) 8
  calc
    _ ≤ J*(C*R*phase)+ C*Q^2 := by
      rw [show J*(R*(G*(C*(Q^2+Q*T^8))+Q^2*(C*T))+Q^2*(R+1))+Q^2+specialCost Q+2 =
        J*(R*(G*(C*(Q^2+Q*T^8))+Q^2*(C*T))+Q^2*(R+1))+(Q^2+specialCost Q+2) by ring]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ hRound) hBase
    _ = C*(R*J*phase+Q^2) := by ring
    _ ≤ _ := by
      change C*(R*J*phase+Q^2) ≤ (2*10^24)*(k+1)^8*(R*J*phase+Q^2)
      have hCl : (2*10^24)*(k+1)^8 = 2*C := by dsimp [C,groupCoef]; ring
      rw [hCl]
      exact Nat.mul_le_mul_right _ (by omega)

open Refute2003.Budget in
theorem exists_small_charge400 :
    ∃ k, 8 ≤ k ∧ 400 * (affineCharge k + specialCost (q k) + 2) < q k * nPlane k := by
  obtain ⟨k, hk, hs⟩ := exists_small_total (8 * 10^24) 8 8
  refine ⟨k, by simpa using hk, ?_⟩
  calc
    400 * (affineCharge k + specialCost (q k) + 2) ≤
      400 * totalUnits k (2 * 10^24) 8 := Nat.mul_le_mul_left _ (final_charge_le k)
    _ = 100 * totalUnits k (8 * 10^24) 8 := by
      unfold totalUnits
      ring
    _ < _ := hs

theorem q_ge_1000 (k : ℕ) (hk : 8 ≤ k) : 1000 ≤ Refute2003.Budget.q k := by
  change 1000 ≤ 2 ^ (20 * k)
  exact (by decide : 1000 ≤ 2 ^ 10).trans
    (Nat.pow_le_pow_right (by decide) (show 10 ≤ 20 * k by omega))

end
end Refute2003.OuterConcrete

namespace Refute2003.OuterConcrete
open BundleBuild
noncomputable section

section Plug
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K]
variable {k n : ℕ}
variable (D : ConcreteGroup.Design K k)
variable (lab : Label K ≃ Fin n)

abbrev affineScan : Fin ((Budget.q k)^2) ≃ K×K :=
  (finCongr (by unfold Budget.q ConcreteGroup.q ConcreteGroup.width; ring : (Budget.q k)^2 = ConcreteGroup.q k*ConcreteGroup.q k)).trans
    (finProdFinEquiv.symm.trans (Equiv.prodCongr D.number.symm D.number.symm))

include D in
theorem card_affine : Fintype.card (K×K) = (Budget.q k)^2 := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (affineScan D)).symm

variable (h : Fin (Budget.charts k) → K×K → Fin (Budget.bins k))

def labels (i : Fin (Budget.charts k)) (b : Fin (Budget.bins k)) : List (K×K) :=
  ((List.finRange ((Budget.q k)^2)).map (affineScan D)).filter (fun a => h i a == b)

theorem mem_labels (i : Fin (Budget.charts k)) (b : Fin (Budget.bins k)) (a : K×K) :
    a ∈ labels D h i b ↔ h i a = b := by
  have hm : a ∈ (List.finRange ((Budget.q k)^2)).map (affineScan D) :=
    List.mem_map.mpr ⟨(affineScan D).symm a, by simp, (affineScan D).apply_symm_apply a⟩
  unfold labels
  rw [List.mem_filter]
  simp only [hm, beq_iff_eq, true_and]

def detector : OuterCode.Detect (Code (n+n)) (K×K) Signal (Budget.charts k) (Budget.bins k) :=
  fun Y i b => ConcreteGroup.group D (labels D h i b) Y (pointWire lab ∘ Sum.inl)

def affineCode : Code (n+n) Signal :=
  OuterCode.accept (affineScan D) h (detector D lab h) (Budget.rounds k) (lineWire lab ∘ Sum.inl)

theorem affine_cost : BundleBuild.Budget.within (affineCode D lab h) (affineCharge k) := by
  let Q := Budget.q k
  let T := Budget.cap k
  let C := groupCoef k
  let base := C*(Q^2+Q*T^8)
  let per := C*T
  let charge i b := base + (labels D h i b).length*per
  have hc : ∀ Y i b, BundleBuild.Budget.within (detector D lab h Y i b) (charge i b) := by
    intro Y i b
    unfold detector charge
    exact BundleBuild.Budget.weaken (ConcreteGroup.group_budget D (labels D h i b) Y
      (pointWire lab ∘ Sum.inl)) (by
      change C*(Q^2+Q*T^8+(labels D h i b).length*T) ≤ base+(labels D h i b).length*per
      dsimp only [base,per]
      rw [Nat.mul_add]
      exact Nat.add_le_add_left (by ring_nf; rfl) _)
  have ht := OuterCode.accept_budget (affineScan D) h (detector D lab h) charge hc
    (Budget.rounds k) (lineWire lab ∘ Sum.inl)
  unfold charge labels at ht
  rw [OuterCode.roundCharge_partition] at ht
  exact ht

def pointHas (X : Finset (Fin n)) (a : K×K) : Prop :=
  ∃ u : K, lab (.inl (u,a.1*u+a.2)) ∈ X

theorem detector_ok (sound : ConcreteGroup.DesignSound D) (X Y : Finset (Fin n)) :
    OuterCode.DetectorOK (physicalSem (input X Y)) h (pointHas lab X) (Budget.cap k) (detector D lab h) := by
  intro s z A hz i b
  let A' := Outer.bucket h i b A
  have hmem (a : K×K) : a ∈ A' ↔ a ∈ labels D h i b ∧ a ∈ A := by
    simp only [A',Outer.bucket,Finset.mem_filter,mem_labels,and_comm]
  have hp (p : K×K) : Truth s (input X Y) ((pointWire lab ∘ Sum.inl) p) (lab (.inl p) ∈ X) :=
    pointRep lab s X Y _
  by_cases hk : A'.card ≤ Budget.cap k
  · apply Good.post (physicalSem (input X Y)) (ConcreteGroup.group_correct D
      (physicalSem (input X Y)) sound (labels D h i b) A' z (pointWire lab ∘ Sum.inl)
      (fun a => a ∈ A) (fun p => lab (.inl p) ∈ X) hz hp hmem hk)
    intro t a ha
    exact ⟨OuterCode.hit A' (pointHas lab X),ha,fun _ => Iff.rfl⟩
  · have hv := ConcreteGroup.group_valid D sound (labels D h i b) z (pointWire lab ∘ Sum.inl)
      (fun a => (hz a).1) (fun a => (hp a).1)
    unfold Good
    exact ⟨hv.1, _, ⟨hv.2,Iff.rfl⟩, fun hh => False.elim (hk hh)⟩

def candidates (Y : Finset (Fin n)) : Finset (K×K) :=
  Finset.univ.filter (fun a => lab (.inl a) ∈ Y)

theorem candidates_mem (Y : Finset (Fin n)) (a : K×K) :
    a ∈ candidates lab Y ↔ lab (.inl a) ∈ Y := by simp [candidates]

theorem candidates_card (Y : Finset (Fin n)) : (candidates lab Y).card ≤ Y.card := by
  apply Finset.card_le_card_of_injOn (fun a : K×K => lab (.inl a))
  · intro a ha
    exact (candidates_mem lab Y a).mp ha
  · intro a ha b hb he
    exact Sum.inl_injective (lab.injective he)

theorem hit_affine (X Y : Finset (Fin n)) :
    OuterCode.hit (candidates lab Y) (pointHas lab X) ↔
      affineHit (fun p => lab p ∈ X) (fun ℓ => lab ℓ ∈ Y) := by
  simp only [OuterCode.hit,candidates_mem,pointHas,affineHit]

theorem affine_correct (sound : ConcreteGroup.DesignSound D)
    (charts_good : Outer.GoodFamily h (Budget.q k) (Budget.cap k))
    (X Y : Finset (Fin n)) (hSize : Y.card ≤ Budget.q k)
    (hProm : Y.card ≤ Budget.cap k ∨ ¬ affineHit (fun p => lab p ∈ X) (fun ℓ => lab ℓ ∈ Y))
    (s : Machine (n+n)) :
    Good (physicalSem (input X Y)) s (affineCode D lab h)
      (fun t a => Truth t (input X Y) a (affineHit (fun p => lab p ∈ X) (fun ℓ => lab ℓ ∈ Y))) := by
  let v := physicalSem (input X Y)
  have hy : OuterCode.VecRep v s (lineWire lab ∘ Sum.inl) (candidates lab Y) := by
    intro a
    exact (lineRep lab s X Y (.inl a)).congr (candidates_mem lab Y a).symm
  have hh : (candidates lab Y).card ≤ Budget.cap k ∨
      ¬ OuterCode.hit (candidates lab Y) (pointHas lab X) :=
    hProm.imp ((candidates_card lab Y).trans) (fun hn hy => hn ((hit_affine lab X Y).mp hy))
  have ht := OuterCode.accept_promised v (affineScan D) h (detector_ok D lab h sound X Y)
    charts_good (Budget.q_lt_round_power k) ((candidates_card lab Y).trans hSize) hh hy
  exact Good.post v ht (fun _ _ ha => ha.congr (hit_affine lab X Y))

end Plug
end
end Refute2003.OuterConcrete

namespace Refute2003.OuterConcrete

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open BundleBuild PEqualNP.GenericRejection

theorem promisedCircuit :
    ∃ q n s : Nat, ∃ S : Fin n → Finset (Fin n),
      ∃ P : Program (n+n) s, ∃ w : Fin (n+n+s),
        1000 ≤ q ∧ n = q^2+q+1 ∧
        (∀ l, (S l).card = q+1) ∧
        (∀ p r : Fin n, p ≠ r → ∃! l : Fin n, p ∈ S l ∧ r ∈ S l) ∧
        (∀ X Y : Finset (Fin n), Y.card ≤ q →
          P.read (input X Y) w = incidenceFun S X Y) ∧
        400*(s+1) < n*q := by
  classical
  obtain ⟨k,hk,small⟩ := exists_small_charge400
  let K := WordAlgebra.BinaryField (ConcreteGroup.width k)
  letI : Fintype K := WordAlgebra.binaryFintype (ConcreteGroup.width k)
  obtain ⟨D,hD⟩ := ConcreteGroup.exists_binary_design k (by omega)
  obtain ⟨h,hh⟩ := exists_charts k hk (card_affine D).le
  let q := ConcreteGroup.q k
  let n := Budget.nPlane k
  have hK : Fintype.card K = q := by
    have hc : Fintype.card K = Fintype.card (Fin q) :=
      Fintype.card_congr (show K ≃ Fin q from D.number)
    rw [hc,Fintype.card_fin]
  have hn : Fintype.card (Label K) = n := by
    rw [label_card, hK]
    rfl
  have npos : 0 < n := by
    change 0 < q^2+q+1
    omega
  let lab := Fintype.equivFinOfCardEq hn
  have hq : 1000 ≤ q := q_ge_1000 k hk
  let aff := affineCode D lab h
  let r := (planeCode D.number lab aff).run (Machine.empty (n+n))
  have deg : ∀ l, ((plane lab) l).card = q+1 := fun l => by
    simpa [hK] using plane_card lab l
  have cost := budget_size _ _ (planeCode_budget D.number lab aff (affineCharge k) (affine_cost D lab h))
    (Machine.empty (n+n))
  have charge : 400*(r.2.1+1) < n*q := by
    have bound : r.2.1 ≤ affineCharge k + specialCost q + 1 := by
      simpa only [r, Machine.empty, Nat.zero_add] using cost
    have room : 400*(affineCharge k + specialCost q + 2) < q*n := by
      exact small
    rw [Nat.mul_comm q n] at room
    omega
  have valid (X Y : Finset (Fin n)) (hy : Y.card ≤ q) :
      Ref.read r.2.2 (input X Y) (r.1.asRef r.2) = incidenceFun (plane lab) X Y := by
    rw [Signal.read_asRef]
    apply code_correct D.number lab X Y _ aff
    apply affineGoodForAll lab aff q (by omega) _ X Y hy
    intro X' Y' hy' hyp
    have hT : 1 ≤ Budget.cap k := Nat.one_le_pow _ _ (by decide)
    exact affine_correct D lab h hD hh X' Y' hy' (hyp.imp (fun h => h.trans hT) id) _
  cases out : r.1.asRef r.2 with
  | const b =>
    cases b with
    | false =>
      let l : Fin n := ⟨0,npos⟩
      have nonempty : 0 < ((plane lab) l).card := by rw [deg]; omega
      obtain ⟨p,hp⟩ := Finset.card_pos.mp nonempty
      have yes := valid {p} {l} (by simp; omega)
      rw [out, incidenceFun_pair_true hp] at yes
      cases yes
    | true =>
      have no := valid ∅ ∅ (by simp)
      rw [out, incidenceFun_false (show IsFalseInput (plane lab) ∅ ∅ by simp [IsFalseInput])] at no
      cases no
  | wire w =>
    refine ⟨q,n,r.2.1,plane lab,r.2.2,w,hq,rfl,deg,plane_join lab,?_,charge⟩
    intro X Y hy
    have res := valid X Y hy
    rw [out] at res
    exact res

end Refute2003.OuterConcrete

namespace Refute2003


def Program.Ordered {m s : ℕ} (P : Program m s) : Prop :=
  ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), P.gates[j]? = some g →
    ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < m+j

theorem Program.ordered_push {m s : ℕ} (P : Program m s) (h : P.Ordered)
    (op : AOOp) (a b : Fin (m+s)) (hab : a.val < b.val) : (P.push op a b).Ordered := by
  intro j g lookup
  change (P.gates ++ [mkGate op a b])[j]? = some g at lookup
  by_cases old : j < s
  · rw [List.getElem?_append_left (by simpa using old)] at lookup
    exact h j g lookup
  · have inRange : j < s+1 := by
      by_contra! outside
      have miss : (P.gates ++ [mkGate op a b]).length ≤ j := by simpa using outside
      rw [List.getElem?_eq_none miss] at lookup
      cases lookup
    have index : j = s := by omega
    subst j
    rw [List.getElem?_append_right (by simp), Program.gates_length, Nat.sub_self] at lookup
    change some (mkGate op a b) = some g at lookup
    have gateEq := Option.some.inj lookup
    subst g
    exact ⟨a.val, b.val, rfl, hab, b.isLt⟩

private theorem AOOp.ordered_idem (op : AOOp) (a : Bool) : op.eval a a = a := by
  cases op <;> cases a <;> rfl

private theorem AOOp.ordered_swap (op : AOOp) (a b : Bool) : op.eval a b = op.eval b a := by
  cases op <;> cases a <;> cases b <;> rfl

/-- Sort the parents of every gate and replace gates with repeated parents by their common wire. -/
theorem Program.normalize_ordered {m s : ℕ} (P : Program m s) :
    ∃ t ≤ s, ∃ (Q : Program m t) (f : Fin (m+s) → Fin (m+t)),
      Q.Ordered ∧ ∀ x i, Q.read x (f i) = P.read x i := by
  induction P with
  | nil =>
    refine ⟨0, le_rfl, .nil, id, ?_, fun _ _ => rfl⟩
    intro j g lookup
    simp [Program.gates] at lookup
  | @push s P op l r ih =>
    obtain ⟨t, within, Q, f, ordered, values⟩ := ih
    let a := f l
    let b := f r
    have source (x : Fin m → Bool) :
        (P.push op l r).read x (Fin.last (m+s)) = op.eval (Q.read x a) (Q.read x b) := by
      rw [Program.read_new]
      simp only [a, b, values]
    by_cases same : a = b
    · let map : Fin (m+(s+1)) → Fin (m+t) := Fin.lastCases a f
      refine ⟨t, within.trans (Nat.le_succ s), Q, map, ordered, ?_⟩
      intro x i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · change Q.read x (Fin.lastCases a f (Fin.last (m+s))) =
          (P.push op l r).read x (Fin.last (m+s))
        rw [Fin.lastCases_last, source, ← same, AOOp.ordered_idem]
      · change Q.read x (Fin.lastCases a f k.castSucc) = (P.push op l r).read x k.castSucc
        rw [Fin.lastCases_castSucc, Program.read_old, values]
    · let lo := if a < b then a else b
      let hi := if a < b then b else a
      have ascending : lo.val < hi.val := by
        change lo < hi
        by_cases order : a < b
        · simp [lo, hi, order]
        · have reverse : b < a := lt_of_le_of_ne (le_of_not_gt order) (Ne.symm same)
          simpa [lo, hi, order] using reverse
      have reorder (x : Fin m → Bool) :
          op.eval (Q.read x lo) (Q.read x hi) = op.eval (Q.read x a) (Q.read x b) := by
        by_cases order : a < b
        · simp [lo, hi, order]
        · simpa [lo, hi, order] using AOOp.ordered_swap op (Q.read x b) (Q.read x a)
      let map : Fin (m+(s+1)) → Fin (m+(t+1)) :=
        Fin.lastCases (Fin.last (m+t)) (fun k => (f k).castSucc)
      refine ⟨t+1, Nat.succ_le_succ within, Q.push op lo hi, map,
        Q.ordered_push ordered op lo hi ascending, ?_⟩
      intro x i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · change (Q.push op lo hi).read x
            (Fin.lastCases (Fin.last (m+t)) (fun k : Fin (m+s) => (f k).castSucc) (Fin.last (m+s))) =
          (P.push op l r).read x (Fin.last (m+s))
        rw [Fin.lastCases_last, Program.read_new, source, reorder]
      · change (Q.push op lo hi).read x
            (Fin.lastCases (Fin.last (m+t)) (fun j : Fin (m+s) => (f j).castSucc) k.castSucc) =
          (P.push op l r).read x k.castSucc
        rw [Fin.lastCases_castSucc, Program.read_old, Program.read_old, values]

end Refute2003


def Claim : Prop :=
  ¬ (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → ∀ (x15 : Finset ℕ), (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x16]? = Option.some x17 → x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x16 ∉ x15 → ¬((∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.false)).getD x21 Bool.false ≠ (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.true)).getD x21 Bool.false) ∨ ∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x23)).getD x21 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x23)).getD x21 Bool.false)) → (100 : ℕ) * x15.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size)

open Refute2003 PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection
open PEqualNP.MetaComplexity

theorem solveOrderedClaim : Claim := by
  classical
  intro wouldBound
  obtain ⟨q,n,s,S,P,w,hq,hn,degree,joins,promised,small⟩ :=
    Refute2003.OuterConcrete.promisedCircuit
  obtain ⟨t,ht,Q,wireMap,ordered,unchanged⟩ := P.normalize_ordered
  let v := wireMap w
  let C := Q.toCircuit v
  let I : Fin n → Fin n → Prop := fun p l => p ∈ S l
  let di : DecidableRel I := inferInstance
  have degreeI (l : Fin n) : Fintype.card {p // I p l} = q+1 := by
    rw [Fintype.card_subtype]
    have fiber : Finset.univ.filter (fun p => I p l) = S l := by
      ext p
      simp [I]
    rw [fiber, degree l]
  have mono : Monotone2 C := by
    intro g hg
    have kind := Q.gate_ops g hg
    refine ⟨?_,kind.2.le⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using kind.1
  have correct (X Y : Finset (Fin n)) (hy : Y.card ≤ q) :
      circuitFun (n+n) C (input X Y) = incidenceFun S X Y := by
    change (Q.toCircuit v).eval (List.ofFn (input X Y)) = _
    rw [Q.toCircuit_eval]
    exact (unchanged (input X Y) w).trans (promised X Y hy)
  have accepts (p l : Fin n) (hit : I p l) :
      circuitFun (n+n) C (fun j => decide (j = Fin.castAdd n p ∨ j = Fin.natAdd n l)) = true := by
    have few : ({l} : Finset (Fin n)).card ≤ q := by simpa using (show 1 ≤ q by omega)
    rw [← input_pair p l, correct {p} {l} few, incidenceFun_pair_true hit]
  have rejects (z : Fin (n+n) → Bool)
      (few : Fintype.card {l : Fin n // z (Fin.natAdd n l) = true} ≤ q)
      (no : ¬ ∃ p l : Fin n, I p l ∧ z (Fin.castAdd n p) = true ∧
        z (Fin.natAdd n l) = true) : circuitFun (n+n) C z = false := by
    let X := Finset.univ.filter (fun p : Fin n => z (Fin.castAdd n p) = true)
    let Y := Finset.univ.filter (fun l : Fin n => z (Fin.natAdd n l) = true)
    have hz : input X Y = z := by
      funext k
      refine Fin.addCases ?_ ?_ k
      · intro p
        rw [input, Fin.append_left]
        apply Bool.eq_iff_iff.mpr
        simp [X]
      · intro l
        rw [input, Fin.append_right]
        apply Bool.eq_iff_iff.mpr
        simp [Y]
    have hy : Y.card ≤ q := by rw [Fintype.card_subtype] at few; exact few
    rw [← hz, correct X Y hy, incidenceFun_false]
    intro l hl
    apply Finset.disjoint_left.mpr
    intro p hp hx
    exact no ⟨p,l,hp,(Finset.mem_filter.mp hx).2,(Finset.mem_filter.mp hl).2⟩
  let excluded := Finset.range C.size
  have size : C.size = t := Q.size_toCircuit v
  have margin : 100*C.size < n*q := by rw [size]; omega
  have lower : n*q ≤ 100*C.size := by
    apply @wouldBound q n I di C (by omega) hn degreeI joins mono (Q.valid_output v)
      ordered accepts rejects excluded
    · intro j g listed _ outside
      have valid : j < C.size := (List.getElem?_eq_some_iff.mp listed).1
      exact (outside (Finset.mem_range.mpr valid)).elim
    · simpa [excluded] using margin
  omega

end PEqualNP.Outside.L_meta_2009

theorem PEqualNP.Outside.L_meta_2009 :
  ¬ (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → ∀ (x15 : Finset ℕ), (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x16]? = Option.some x17 → x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x16 ∉ x15 → ¬((∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.false)).getD x21 Bool.false ≠ (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.true)).getD x21 Bool.false) ∨ ∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x23)).getD x21 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x23)).getD x21 Bool.false)) → (100 : ℕ) * x15.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size) :=
  PEqualNP.Outside.L_meta_2009.solveOrderedClaim
