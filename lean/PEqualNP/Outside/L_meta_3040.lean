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
namespace PEqualNP.Outside.L_meta_3040

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

-- The survivor estimate is from the accepted proof of L-meta-1625.
namespace SurvivorBound3040

section Sec1622

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace P1622

theorem getD_app_lt {α : Type} (l l' : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_len {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def dflt : Gate := Gate.mk GateOp.or []

-- generic gate-list fold
def run {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) w

theorem run_snoc {α : Type} (f : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    run f (gs ++ [g]) w = run f gs w ++ [f (run f gs w) g] := by
  simp [run]

theorem run_append {α : Type} (f : List α → Gate → α) (g1 g2 : List Gate) (w : List α) :
    run f (g1 ++ g2) w = run f g2 (run f g1 w) := by
  simp [run]

theorem run_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) :
    (run f gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem run_lt {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) (d : α) (i : ℕ)
    (h : i < w.length) : (run f gs w).getD i d = w.getD i d := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [run_snoc, getD_app_lt _ _ _ _ (by rw [run_length]; omega), ih]

theorem run_gate {α : Type} (f : List α → Gate → α) (d : α)
    (hf : ∀ (g : Gate) (w w' : List α), (∀ i ∈ g.inputs, w.getD i d = w'.getD i d) → f w g = f w' g)
    (gs : List Gate) (w : List α) (L : ℕ) (hL : w.length = L) (k : ℕ) (hk : k < gs.length)
    (hr : ∀ i ∈ (gs.getD k dflt).inputs, i < L + k) :
    (run f gs w).getD (L + k) d = f (run f gs w) (gs.getD k dflt) := by
  subst hL
  induction gs using List.reverseRecOn with
  | nil => simp at hk
  | append_singleton gs g ih =>
    rw [run_snoc]
    rcases Nat.lt_or_ge k gs.length with h | h
    · have e : (gs ++ [g]).getD k dflt = gs.getD k dflt := getD_app_lt _ _ _ _ h
      rw [e] at hr ⊢
      rw [getD_app_lt _ _ _ _ (by rw [run_length]; omega), ih h hr]
      apply hf
      intro i hi
      symm
      exact getD_app_lt _ _ _ _ (by rw [run_length]; have := hr i hi; omega)
    · have hk' : k = gs.length := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      subst hk'
      have e : (gs ++ [g]).getD gs.length dflt = g := getD_app_len _ _ _
      rw [e] at hr ⊢
      have e2 : w.length + gs.length = (run f gs w).length := (run_length f gs w).symm
      rw [e2, getD_app_len]
      apply hf
      intro i hi
      symm
      exact getD_app_lt _ _ _ _ (by rw [run_length]; have := hr i hi; omega)

def evf (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def ldf (d : List ℕ) (g : Gate) : ℕ := g.lineDegree d

theorem evf_congr (g : Gate) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = w'.getD i false) : evf w g = evf w' g := by
  unfold evf
  rw [List.map_congr_left h]

theorem ldf_congr (g : Gate) (w w' : List ℕ)
    (h : ∀ i ∈ g.inputs, w.getD i 0 = w'.getD i 0) : ldf w g = ldf w' g := by
  unfold ldf Gate.lineDegree
  rw [List.map_congr_left h]

-- reads-back for bare lists
def RBL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j dflt).inputs, i < n + j

theorem RBL_append (n : ℕ) (g1 g2 : List Gate) (h1 : RBL n g1) (h2 : RBL (n + g1.length) g2) :
    RBL n (g1 ++ g2) := by
  intro j hj i hi
  rcases Nat.lt_or_ge j g1.length with h | h
  · rw [getD_app_lt _ _ _ _ h] at hi
    exact h1 j h i hi
  · rw [List.getD_append_right _ _ _ _ h] at hi
    simp only [List.length_append] at hj
    have := h2 (j - g1.length) (by omega) i hi
    omega

theorem RBL_empty (n : ℕ) (gs : List Gate) (h : ∀ g ∈ gs, g.inputs = []) : RBL n gs := by
  intro j hj i hi
  have hm : gs.getD j dflt ∈ gs := by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  rw [h _ hm] at hi
  simp at hi

theorem RBL_snoc (n : ℕ) (gs : List Gate) (g : Gate) (h1 : RBL n gs)
    (h2 : ∀ i ∈ g.inputs, i < n + gs.length) : RBL n (gs ++ [g]) := by
  apply RBL_append _ _ _ h1
  intro j hj i hi
  simp only [List.length_singleton] at hj
  have hj0 : j = 0 := by omega
  subst hj0
  have := h2 i (by simpa using hi)
  omega

-- the state of the reverse pass: accumulator wire per wire, and the appended gates
def Good (B : ℕ) (st : (ℕ → ℕ) × List Gate) : Prop :=
  (∀ w, st.1 w < B + st.2.length) ∧
  (∀ g ∈ st.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  RBL B st.2

def link (B : ℕ) (st : (ℕ → ℕ) × List Gate) (a src : ℕ) : (ℕ → ℕ) × List Gate :=
  (Function.update st.1 a (B + st.2.length), st.2 ++ [Gate.mk GateOp.or [st.1 a, src]])

def andl (B : ℕ) (st : (ℕ → ℕ) × List Gate) (W tgt side : ℕ) : (ℕ → ℕ) × List Gate :=
  link B (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) tgt (B + st.2.length)

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def proc (B : ℕ) (deg : List ℕ) (op : GateOp) (l : List ℕ) (W : ℕ)
    (st : (ℕ → ℕ) × List Gate) : (ℕ → ℕ) × List Gate :=
  if 0 < deg.getD W 0 then
    if isAnd op = true ∧ l.length = 2 then
      if 0 < deg.getD (l.getD 0 0) 0 then andl B st W (l.getD 0 0) (l.getD 1 0)
      else andl B st W (l.getD 1 0) (l.getD 0 0)
    else l.foldl (fun s a => link B s a (st.1 W)) st
  else st

def aval (base : List Bool) (st : (ℕ → ℕ) × List Gate) (w : ℕ) : Bool :=
  (run evf st.2 base).getD (st.1 w) false

theorem link_spec (B : ℕ) (base : List Bool) (st : (ℕ → ℕ) × List Gate) (a src : ℕ)
    (hB : base.length = B) (hg : Good B st) (hs : src < B + st.2.length) :
    Good B (link B st a src) ∧ (link B st a src).2.length = st.2.length + 1 ∧
    (∀ i < B + st.2.length,
      (run evf (link B st a src).2 base).getD i false = (run evf st.2 base).getD i false) ∧
    ∀ w, aval base (link B st a src) w =
      (aval base st w || (decide (w = a) && (run evf st.2 base).getD src false)) := by
  obtain ⟨g1, g2, g3⟩ := hg
  have hlen : (run evf st.2 base).length = B + st.2.length := by rw [run_length, hB]
  have hrun : run evf (link B st a src).2 base = run evf st.2 base ++
      [((run evf st.2 base).getD (st.1 a) false || (run evf st.2 base).getD src false)] := by
    simp [link, run_snoc, evf, GateOp.eval]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro w
    simp only [link, List.length_append, List.length_singleton, Function.update_apply]
    split_ifs
    · omega
    · have := g1 w
      omega
  · intro g hg
    simp only [link, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact g2 g hg
    · exact ⟨Or.inr rfl, by simp⟩
  · apply RBL_snoc _ _ _ g3
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact g1 a
    · exact hs
  · simp [link]
  · intro i hi
    rw [hrun]
    exact getD_app_lt _ _ _ _ (by omega)
  · intro w
    unfold aval
    rw [hrun]
    by_cases hw : w = a
    · subst hw
      have e : (link B st w src).1 w = (run evf st.2 base).length := by simp [link, hlen]
      rw [e, getD_app_len]
      simp
    · have e : (link B st a src).1 w = st.1 w := by simp [link, hw]
      rw [e, getD_app_lt _ _ _ _ (by have := g1 w; omega)]
      simp [hw]

theorem ite_p {α : Type} (c : Prop) [Decidable c] (a b : α) (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_n {α : Type} (c : Prop) [Decidable c] (a b : α) (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem bool_aux (p q r s : Bool) : ((p || (q && s)) || (r && s)) = (p || ((q || r) && s)) := by
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

theorem fold_spec (B : ℕ) (base : List Bool) (src : ℕ) (hB : base.length = B) (l : List ℕ) :
    ∀ (st : (ℕ → ℕ) × List Gate), Good B st → src < B + st.2.length →
    Good B (l.foldl (fun s a => link B s a src) st) ∧
    (l.foldl (fun s a => link B s a src) st).2.length = st.2.length + l.length ∧
    (∀ i < B + st.2.length,
      (run evf (l.foldl (fun s a => link B s a src) st).2 base).getD i false =
        (run evf st.2 base).getD i false) ∧
    ∀ w, aval base (l.foldl (fun s a => link B s a src) st) w =
      (aval base st w || (decide (w ∈ l) && (run evf st.2 base).getD src false)) := by
  induction l with
  | nil =>
    intro st hg _
    simp [hg]
  | cons a l ih =>
    intro st hg hs
    obtain ⟨k1, k2, k3, k4⟩ := link_spec B base st a src hB hg hs
    obtain ⟨j1, j2, j3, j4⟩ := ih (link B st a src) k1 (by omega)
    rw [List.foldl_cons]
    refine ⟨j1, ?_, ?_, ?_⟩
    · rw [j2, k2, List.length_cons]
      omega
    · intro i hi
      rw [j3 i (by omega), k3 i hi]
    · intro w
      rw [j4 w, k4 w, k3 src hs, bool_aux]
      congr 2
      simp [Bool.decide_or]

theorem andl_spec (B : ℕ) (base : List Bool) (st : (ℕ → ℕ) × List Gate) (W tgt side : ℕ)
    (hB : base.length = B) (hg : Good B st) (hs : side < B) :
    Good B (andl B st W tgt side) ∧ (andl B st W tgt side).2.length = st.2.length + 2 ∧
    ∀ w, aval base (andl B st W tgt side) w =
      (aval base st w || (decide (w = tgt) && (aval base st W && base.getD side false))) := by
  have hg' := hg
  obtain ⟨g1, g2, g3⟩ := hg
  have hlen : (run evf st.2 base).length = B + st.2.length := by rw [run_length, hB]
  have hrun : run evf (st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) base = run evf st.2 base ++
      [((run evf st.2 base).getD (st.1 W) false && (run evf st.2 base).getD side false)] := by
    simp [run_snoc, evf, GateOp.eval]
  have hg1 : Good B (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w
      have := g1 w
      show st.1 w < B + (st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]).length
      simp only [List.length_append, List.length_singleton]
      omega
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact g2 g hg
      · exact ⟨Or.inl rfl, by simp⟩
    · apply RBL_snoc _ _ _ g3
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h
      · rw [h]; exact g1 W
      · rw [h]; omega
  obtain ⟨k1, k2, _, k4⟩ := link_spec B base (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]])
    tgt (B + st.2.length) hB hg1 (by simp)
  refine ⟨k1, ?_, ?_⟩
  · unfold andl
    rw [k2]
    simp
  · intro w
    unfold andl
    rw [k4 w]
    have e1 : aval base (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) w = aval base st w := by
      unfold aval
      show (run evf (st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) base).getD (st.1 w) false = _
      rw [hrun]
      exact getD_app_lt _ _ _ _ (by have := g1 w; omega)
    have e2 : (run evf (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]).2 base).getD
        (B + st.2.length) false = (aval base st W && base.getD side false) := by
      show (run evf (st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) base).getD _ _ = _
      rw [hrun, ← hlen, getD_app_len]
      unfold aval
      rw [run_lt evf st.2 base false side (by omega)]
    rw [e1, e2]

-- the logical invariant of the reverse pass
def Tinv (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (bound : ℕ) (A : ℕ → Bool) : Prop :=
  (∀ w < bound, Dp w → A w = true → u w = true → uo = true) ∧
  (∀ w < bound, Dp w → A w = true → v w = true → vo = true) ∧
  (uo = true → vo = true ∨ ∃ w < bound, Dp w ∧ A w = true ∧ u w = true)

theorem tinv_skip (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (W : ℕ) (A : ℕ → Bool)
    (hD : ¬ Dp W) (hI : Tinv Dp u v uo vo (W + 1) A) : Tinv Dp u v uo vo W A := by
  obtain ⟨h1, h2, h3⟩ := hI
  refine ⟨fun w hw => h1 w (by omega), fun w hw => h2 w (by omega), ?_⟩
  intro huo
  rcases h3 huo with h | ⟨w, hw, hd, ha, hz⟩
  · left; exact h
  · right
    refine ⟨w, ?_, hd, ha, hz⟩
    rcases Nat.lt_or_ge w W with hlt | hge
    · exact hlt
    · have e : w = W := by omega
      subst e
      exact absurd hd hD

theorem tinv_or (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (W : ℕ) (l : List ℕ)
    (A A' : ℕ → Bool) (hr : ∀ i ∈ l, i < W) (hD : Dp W)
    (hA : ∀ w, A' w = (A w || (decide (w ∈ l) && A W)))
    (hx : ∀ w, ¬ Dp w → u w = v w)
    (p1u : ∀ i ∈ l, u i = true → u W = true) (p1v : ∀ i ∈ l, v i = true → v W = true)
    (p2 : u W = true → v W = true ∨ ∃ i ∈ l, u i = true)
    (hI : Tinv Dp u v uo vo (W + 1) A) : Tinv Dp u v uo vo W A' := by
  obtain ⟨h1, h2, h3⟩ := hI
  refine ⟨?_, ?_, ?_⟩
  · intro w hw hd ha hz
    rw [hA] at ha
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
    rcases ha with ha | ⟨hm, haW⟩
    · exact h1 w (by omega) hd ha hz
    · exact h1 W (by omega) hD haW (p1u w hm hz)
  · intro w hw hd ha hz
    rw [hA] at ha
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
    rcases ha with ha | ⟨hm, haW⟩
    · exact h2 w (by omega) hd ha hz
    · exact h2 W (by omega) hD haW (p1v w hm hz)
  · intro huo
    rcases h3 huo with h | ⟨w, hw, hd, ha, hz⟩
    · left; exact h
    · rcases Nat.lt_or_ge w W with hlt | hge
      · right
        exact ⟨w, hlt, hd, by rw [hA, ha]; rfl, hz⟩
      · have e : w = W := by omega
        subst e
        rcases p2 hz with hvW | ⟨i, hi, hui⟩
        · left; exact h2 w (by omega) hd ha hvW
        · by_cases hdi : Dp i
          · right
            exact ⟨i, hr i hi, hdi, by simp [hA, hi, ha], hui⟩
          · left
            have e := hx i hdi
            exact h2 w (by omega) hd ha (p1v i hi (by rw [← e]; exact hui))

theorem tinv_and (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (W tgt side : ℕ)
    (A A' : ℕ → Bool) (ht : tgt < W) (hD : Dp W) (hs : ¬ Dp side)
    (hA : ∀ w, A' w = (A w || (decide (w = tgt) && (A W && v side))))
    (hx : ∀ w, ¬ Dp w → u w = v w)
    (hu : u W = (u tgt && u side)) (hv : v W = (v tgt && v side))
    (hI : Tinv Dp u v uo vo (W + 1) A) : Tinv Dp u v uo vo W A' := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hsd := hx side hs
  refine ⟨?_, ?_, ?_⟩
  · intro w hw hd ha hz
    rw [hA] at ha
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
    rcases ha with ha | ⟨hm, haW, hvs⟩
    · exact h1 w (by omega) hd ha hz
    · subst hm
      exact h1 W (by omega) hD haW (by rw [hu, hz, hsd, hvs]; rfl)
  · intro w hw hd ha hz
    rw [hA] at ha
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
    rcases ha with ha | ⟨hm, haW, hvs⟩
    · exact h2 w (by omega) hd ha hz
    · subst hm
      exact h2 W (by omega) hD haW (by rw [hv, hz, hvs]; rfl)
  · intro huo
    rcases h3 huo with h | ⟨w, hw, hd, ha, hz⟩
    · left; exact h
    · rcases Nat.lt_or_ge w W with hlt | hge
      · right
        exact ⟨w, hlt, hd, by rw [hA, ha]; rfl, hz⟩
      · have e : w = W := by omega
        subst e
        rw [hu] at hz
        simp only [Bool.and_eq_true] at hz
        have hvs : v side = true := by rw [← hsd]; exact hz.2
        by_cases hdt : Dp tgt
        · right
          exact ⟨tgt, ht, hdt, by simp [hA, ha, hvs], hz.1⟩
        · left
          have e := hx tgt hdt
          exact h2 w (by omega) hd ha (by rw [hv, ← e, hz.1, hvs]; rfl)

theorem fold_case (B : ℕ) (deg : List ℕ) (base : List Bool) (l : List ℕ) (W : ℕ)
    (st : (ℕ → ℕ) × List Gate) (hB : base.length = B) (hl : l.length ≤ 2)
    (hr : ∀ i ∈ l, i < W) (hg : Good B st) (hD : 0 < deg.getD W 0) :
    Good B (l.foldl (fun s a => link B s a (st.1 W)) st) ∧
    (l.foldl (fun s a => link B s a (st.1 W)) st).2.length ≤ st.2.length + 2 ∧
    ∀ (u v : ℕ → Bool) (uo vo : Bool), (∀ w, ¬ 0 < deg.getD w 0 → u w = v w) →
      (∀ i ∈ l, u i = true → u W = true) → (∀ i ∈ l, v i = true → v W = true) →
      (u W = true → v W = true ∨ ∃ i ∈ l, u i = true) →
      Tinv (fun w => 0 < deg.getD w 0) u v uo vo (W + 1) (aval base st) →
      Tinv (fun w => 0 < deg.getD w 0) u v uo vo W
        (aval base (l.foldl (fun s a => link B s a (st.1 W)) st)) := by
  obtain ⟨j1, j2, _, j4⟩ := fold_spec B base (st.1 W) hB l st hg (hg.1 W)
  refine ⟨j1, by omega, ?_⟩
  intro u v uo vo hx p1u p1v p2 hI
  exact tinv_or _ u v uo vo W l _ _ hr hD j4 hx p1u p1v p2 hI

theorem proc_spec (B : ℕ) (deg : List ℕ) (base : List Bool) (op : GateOp) (l : List ℕ) (W : ℕ)
    (st : (ℕ → ℕ) × List Gate) (hB : base.length = B) (hW : W < B)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hl : l.length ≤ 2) (hr : ∀ i ∈ l, i < W)
    (hc : op = GateOp.and → l.length = 2 → ∃ i ∈ l, deg.getD i 0 = 0)
    (hg : Good B st) :
    Good B (proc B deg op l W st) ∧
    (proc B deg op l W st).2.length ≤ st.2.length + (if 0 < deg.getD W 0 then 2 else 0) ∧
    ∀ (u v : ℕ → Bool) (uo vo : Bool),
      (∀ i < W, ¬ 0 < deg.getD i 0 → base.getD i false = v i) →
      u W = op.eval (l.map u) → v W = op.eval (l.map v) →
      (∀ w, ¬ 0 < deg.getD w 0 → u w = v w) →
      Tinv (fun w => 0 < deg.getD w 0) u v uo vo (W + 1) (aval base st) →
      Tinv (fun w => 0 < deg.getD w 0) u v uo vo W (aval base (proc B deg op l W st)) := by
  by_cases hD : 0 < deg.getD W 0
  · rcases hop with rfl | rfl
    · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · have e : proc B deg GateOp.and [] W st
            = ([] : List ℕ).foldl (fun s a => link B s a (st.1 W)) st := by
          unfold proc
          rw [ite_p _ _ _ hD, ite_n _ _ _ (by simp)]
        rw [e]
        obtain ⟨f1, f2, f3⟩ := fold_case B deg base [] W st hB hl hr hg hD
        refine ⟨f1, by simp only [hD, ↓reduceIte]; exact f2, ?_⟩
        intro u v uo vo _ hu hv hx hI
        refine f3 u v uo vo hx (by simp) (by simp) ?_ hI
        intro _
        left
        simpa [GateOp.eval] using hv
      · have e : proc B deg GateOp.and [a] W st
            = [a].foldl (fun s a => link B s a (st.1 W)) st := by
          unfold proc
          rw [ite_p _ _ _ hD, ite_n _ _ _ (by simp)]
        rw [e]
        obtain ⟨f1, f2, f3⟩ := fold_case B deg base [a] W st hB hl hr hg hD
        refine ⟨f1, by simp only [hD, ↓reduceIte]; exact f2, ?_⟩
        intro u v uo vo _ hu hv hx hI
        have hu' : u W = u a := by simpa [GateOp.eval] using hu
        have hv' : v W = v a := by simpa [GateOp.eval] using hv
        refine f3 u v uo vo hx ?_ ?_ ?_ hI
        · intro i hi h
          simp only [List.mem_singleton] at hi
          subst hi
          rw [hu']; exact h
        · intro i hi h
          simp only [List.mem_singleton] at hi
          subst hi
          rw [hv']; exact h
        · intro h
          right
          exact ⟨a, by simp, by rw [← hu']; exact h⟩
      · have e : proc B deg GateOp.and [a, b] W st
            = if 0 < deg.getD a 0 then andl B st W a b else andl B st W b a := by
          unfold proc
          rw [ite_p _ _ _ hD, ite_p _ _ _ (by simp [isAnd])]
          rfl
        have ha : a < W := hr a (by simp)
        have hb : b < W := hr b (by simp)
        obtain ⟨i, hi, hi0⟩ := hc rfl rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rw [e]
        by_cases hda : 0 < deg.getD a 0
        · simp only [hda, ↓reduceIte]
          have hdb : ¬ 0 < deg.getD b 0 := by
            rcases hi with h | h
            · rw [h] at hi0; omega
            · rw [h] at hi0; omega
          obtain ⟨k1, k2, k3⟩ := andl_spec B base st W a b hB hg (by omega)
          refine ⟨k1, by simp only [hD, ↓reduceIte]; omega, ?_⟩
          intro u v uo vo hbv hu hv hx hI
          have hu' : u W = (u a && u b) := by simpa [GateOp.eval] using hu
          have hv' : v W = (v a && v b) := by simpa [GateOp.eval] using hv
          refine tinv_and _ u v uo vo W a b _ _ ha hD hdb ?_ hx hu' hv' hI
          intro w
          rw [k3 w, hbv b hb hdb]
        · simp only [hda, ↓reduceIte]
          obtain ⟨k1, k2, k3⟩ := andl_spec B base st W b a hB hg (by omega)
          refine ⟨k1, by simp only [hD, ↓reduceIte]; omega, ?_⟩
          intro u v uo vo hbv hu hv hx hI
          have hu' : u W = (u b && u a) := by
            rw [Bool.and_comm]; simpa [GateOp.eval] using hu
          have hv' : v W = (v b && v a) := by
            rw [Bool.and_comm]; simpa [GateOp.eval] using hv
          refine tinv_and _ u v uo vo W b a _ _ hb hD hda ?_ hx hu' hv' hI
          intro w
          rw [k3 w, hbv a ha hda]
      · simp at hl
    · have e : proc B deg GateOp.or l W st
          = l.foldl (fun s a => link B s a (st.1 W)) st := by
        unfold proc
        rw [ite_p _ _ _ hD, ite_n _ _ _ (by simp [isAnd])]
      rw [e]
      obtain ⟨f1, f2, f3⟩ := fold_case B deg base l W st hB hl hr hg hD
      refine ⟨f1, by simp only [hD, ↓reduceIte]; exact f2, ?_⟩
      intro u v uo vo _ hu hv hx hI
      have hu' : u W = true ↔ ∃ i ∈ l, u i = true := by
        rw [hu]; simp [GateOp.eval]
      have hv' : v W = true ↔ ∃ i ∈ l, v i = true := by
        rw [hv]; simp [GateOp.eval]
      refine f3 u v uo vo hx ?_ ?_ ?_ hI
      · intro i hi h
        exact hu'.2 ⟨i, hi, h⟩
      · intro i hi h
        exact hv'.2 ⟨i, hi, h⟩
      · intro h
        right
        exact hu'.1 h
  · have e : proc B deg op l W st = st := by
      unfold proc
      rw [ite_n _ _ _ hD]
    rw [e]
    refine ⟨hg, by simp, ?_⟩
    intro u v uo vo _ _ _ _ hI
    exact tinv_skip _ u v uo vo W _ hD hI

-- the reverse pass over the gate list, last gate first
def stAt (B N : ℕ) (deg : List ℕ) (gs : List Gate) (st0 : (ℕ → ℕ) × List Gate) :
    ℕ → (ℕ → ℕ) × List Gate
  | 0 => st0
  | d + 1 => proc B deg (gs.getD (gs.length - 1 - d) dflt).op
      (gs.getD (gs.length - 1 - d) dflt).inputs (N + (gs.length - 1 - d)) (stAt B N deg gs st0 d)

def cnt (N : ℕ) (deg : List ℕ) (b : ℕ) : ℕ :=
  ((Finset.range b).filter (fun k => 0 < deg.getD (N + k) 0)).card

theorem cnt_succ (N : ℕ) (deg : List ℕ) (b : ℕ) :
    cnt N deg (b + 1) = cnt N deg b + (if 0 < deg.getD (N + b) 0 then 1 else 0) := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

def GateHyp (N : ℕ) (deg : List ℕ) (gs : List Gate) : Prop :=
  ∀ k < gs.length, ((gs.getD k dflt).op = GateOp.and ∨ (gs.getD k dflt).op = GateOp.or) ∧
    (gs.getD k dflt).inputs.length ≤ 2 ∧ (∀ i ∈ (gs.getD k dflt).inputs, i < N + k) ∧
    ((gs.getD k dflt).op = GateOp.and → (gs.getD k dflt).inputs.length = 2 →
      ∃ i ∈ (gs.getD k dflt).inputs, deg.getD i 0 = 0)

theorem iter_good (B N : ℕ) (deg : List ℕ) (gs : List Gate) (st0 : (ℕ → ℕ) × List Gate)
    (hNB : N + gs.length ≤ B) (hgs : GateHyp N deg gs) (hg0 : Good B st0) :
    ∀ d ≤ gs.length, Good B (stAt B N deg gs st0 d) ∧
      (stAt B N deg gs st0 d).2.length + 2 * cnt N deg (gs.length - d)
        ≤ st0.2.length + 2 * cnt N deg gs.length := by
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨hg0, by simp [stAt]⟩
  | succ d ih =>
    intro hd
    obtain ⟨i1, i2⟩ := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, k = gs.length - 1 - d := ⟨_, rfl⟩
    have hks : k < gs.length := by omega
    obtain ⟨a1, a2, a3, a4⟩ := hgs k hks
    have e : stAt B N deg gs st0 (d + 1) = proc B deg (gs.getD k dflt).op
        (gs.getD k dflt).inputs (N + k) (stAt B N deg gs st0 d) := by
      rw [hk]; rfl
    obtain ⟨p1, p2, _⟩ := proc_spec B deg (List.replicate B false) (gs.getD k dflt).op
      (gs.getD k dflt).inputs (N + k) (stAt B N deg gs st0 d) List.length_replicate
      (by omega) a1 a2 a3 a4 i1
    rw [e]
    refine ⟨p1, ?_⟩
    have e1 : gs.length - d = k + 1 := by omega
    have e2 : gs.length - (d + 1) = k := by omega
    rw [e1, cnt_succ] at i2
    rw [e2]
    split_ifs at p2 i2 <;> omega

theorem iter_inv (B N : ℕ) (deg : List ℕ) (gs : List Gate) (st0 : (ℕ → ℕ) × List Gate)
    (base : List Bool) (u v : ℕ → Bool) (uo vo : Bool)
    (hB : base.length = B) (hNB : N + gs.length ≤ B) (hgs : GateHyp N deg gs) (hg0 : Good B st0)
    (hv : ∀ i < N + gs.length, ¬ 0 < deg.getD i 0 → base.getD i false = v i)
    (hu : ∀ k < gs.length, u (N + k) = (gs.getD k dflt).op.eval ((gs.getD k dflt).inputs.map u))
    (hvv : ∀ k < gs.length, v (N + k) = (gs.getD k dflt).op.eval ((gs.getD k dflt).inputs.map v))
    (hx : ∀ w, ¬ 0 < deg.getD w 0 → u w = v w)
    (hI : Tinv (fun w => 0 < deg.getD w 0) u v uo vo (N + gs.length) (aval base st0)) :
    ∀ d ≤ gs.length, Tinv (fun w => 0 < deg.getD w 0) u v uo vo (N + (gs.length - d))
      (aval base (stAt B N deg gs st0 d)) := by
  intro d
  induction d with
  | zero =>
    intro _
    simpa [stAt] using hI
  | succ d ih =>
    intro hd
    have i1 := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, k = gs.length - 1 - d := ⟨_, rfl⟩
    have hks : k < gs.length := by omega
    obtain ⟨a1, a2, a3, a4⟩ := hgs k hks
    have e : stAt B N deg gs st0 (d + 1) = proc B deg (gs.getD k dflt).op
        (gs.getD k dflt).inputs (N + k) (stAt B N deg gs st0 d) := by
      rw [hk]; rfl
    obtain ⟨_, _, p3⟩ := proc_spec B deg base (gs.getD k dflt).op
      (gs.getD k dflt).inputs (N + k) (stAt B N deg gs st0 d) hB
      (by omega) a1 a2 a3 a4 (iter_good B N deg gs st0 hNB hgs hg0 d (by omega)).1
    have e1 : gs.length - d = k + 1 := by omega
    have e2 : gs.length - (d + 1) = k := by omega
    rw [e1] at i1
    rw [e, e2]
    exact p3 u v uo vo (fun i hi => hv i (by omega)) (hu k hks) (hvv k hks) hx i1

-- wire values and degrees of the given circuit
def wv (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn z)).getD w false

theorem wires_run (C : Circuit) (inp : List Bool) : C.wires inp = run evf C.gates inp := rfl

theorem wv_input (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) (h : w < N) :
    wv C N z w = z ⟨w, h⟩ := by
  unfold wv
  rw [wires_run, run_lt _ _ _ _ _ (by simpa using h),
    List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem wv_ge (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) (h : N + C.gates.length ≤ w) :
    wv C N z w = false := by
  unfold wv
  rw [wires_run]
  exact getD_ge _ _ _ (by rw [run_length]; simpa using h)

theorem wv_gate (C : Circuit) (N : ℕ) (z : Fin N → Bool) (hR : ReadsBack N C) (k : ℕ)
    (hk : k < C.gates.length) :
    wv C N z (N + k) = (C.gates.getD k dflt).op.eval ((C.gates.getD k dflt).inputs.map (wv C N z)) := by
  unfold wv
  rw [wires_run]
  exact run_gate evf false evf_congr C.gates _ N (by simp) k hk (hR k hk)

theorem deg_run (C : Circuit) (N : ℕ) (M : Finset ℕ) : C.lineDegrees N M =
    run ldf C.gates ((List.range N).map fun i => if i ∈ M then 1 else 0) := rfl

theorem deg_input (C : Circuit) (N : ℕ) (M : Finset ℕ) (w : ℕ) (h : w < N) :
    (C.lineDegrees N M).getD w 0 = if w ∈ M then 1 else 0 := by
  rw [deg_run, run_lt _ _ _ _ _ (by simpa using h),
    List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem deg_ge (C : Circuit) (N : ℕ) (M : Finset ℕ) (w : ℕ) (h : N + C.gates.length ≤ w) :
    (C.lineDegrees N M).getD w 0 = 0 := by
  rw [deg_run]
  exact getD_ge _ _ _ (by rw [run_length]; simpa using h)

theorem deg_gate (C : Circuit) (N : ℕ) (M : Finset ℕ) (hR : ReadsBack N C) (k : ℕ)
    (hk : k < C.gates.length) :
    (C.lineDegrees N M).getD (N + k) 0 = (C.gates.getD k dflt).lineDegree (C.lineDegrees N M) := by
  rw [deg_run]
  exact run_gate ldf 0 ldf_congr C.gates _ N (by simp) k hk (hR k hk)

theorem app_lt {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) (h : w < n + m)
    (hw : w < n) : Fin.append x y ⟨w, h⟩ = x ⟨w, hw⟩ :=
  Fin.append_left x y ⟨w, hw⟩

theorem app_ge {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) (h : w < n + m)
    (hw : n ≤ w) : Fin.append x y ⟨w, h⟩ = y ⟨w - n, by omega⟩ := by
  have e : (⟨w, h⟩ : Fin (n + m)) = Fin.natAdd n ⟨w - n, by omega⟩ := by
    ext
    simp only [Fin.natAdd_mk]
    omega
  rw [e, Fin.append_right]

theorem gate_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : C.gates.getD k dflt ∈ C.gates := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem _

theorem gate_ops (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
    ((C.gates.getD k dflt).op = GateOp.and ∨ (C.gates.getD k dflt).op = GateOp.or) ∧
    (C.gates.getD k dflt).inputs.length ≤ 2 := by
  obtain ⟨h1, h2⟩ := hM _ (gate_mem C k hk)
  refine ⟨?_, h2⟩
  simpa using h1

-- forward pass: wires of degree zero ignore the line inputs, and all wires are monotone in them
theorem fwd (n m : ℕ) (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack (n + m) C)
    (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) :
    ((C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0 = 0 →
      wv C (n + m) (Fin.append x y) w = wv C (n + m) (Fin.append x (fun _ => false)) w) ∧
    (wv C (n + m) (Fin.append x (fun _ => false)) w = true →
      wv C (n + m) (Fin.append x y) w = true) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w (n + m) with h | h
    · rw [wv_input _ _ _ _ h, wv_input _ _ _ _ h, deg_input _ _ _ _ h]
      rcases Nat.lt_or_ge w n with hw | hw
      · rw [app_lt _ _ _ _ hw, app_lt _ _ _ _ hw]
        exact ⟨fun _ => rfl, fun h => h⟩
      · rw [app_ge _ (fun _ => false) _ _ hw]
        have : w ∈ Finset.Ico n (n + m) := by simp; omega
        simp [this]
    · rcases Nat.lt_or_ge (w - (n + m)) C.gates.length with hk | hk
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + m + k := ⟨w - (n + m), by omega⟩
        have hk' : k < C.gates.length := by omega
        have hu := wv_gate C (n + m) (Fin.append x y) hR k hk'
        have hv := wv_gate C (n + m) (Fin.append x (fun _ => false)) hR k hk'
        have hd := deg_gate C (n + m) (Finset.Ico n (n + m)) hR k hk'
        have hr : ∀ i ∈ (C.gates.getD k dflt).inputs, i < n + m + k := hR k hk'
        obtain ⟨hop, hl⟩ := gate_ops C hM k hk'
        generalize C.gates.getD k dflt = g at hu hv hd hr hop hl
        obtain ⟨op, l⟩ := g
        simp only at hop hl hr
        rw [hu, hv, hd]
        rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · rcases hop with rfl | rfl <;> simp [GateOp.eval]
        · obtain ⟨a1, a2⟩ := ih a (hr a (by simp))
          rcases hop with rfl | rfl
          · simp only [Gate.lineDegree, GateOp.eval]
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.all_cons,
              List.all_nil, id, Bool.and_true, ↓reduceIte, add_zero]
            exact ⟨a1, a2⟩
          · simp only [Gate.lineDegree, GateOp.eval]
            simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, List.any_cons,
              List.any_nil, id, Bool.or_false, reduceCtorEq, ↓reduceIte, Nat.max_zero]
            exact ⟨a1, a2⟩
        · obtain ⟨a1, a2⟩ := ih a (hr a (by simp))
          obtain ⟨b1, b2⟩ := ih b (hr b (by simp))
          rcases hop with rfl | rfl
          · simp only [Gate.lineDegree, GateOp.eval]
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.all_cons,
              List.all_nil, id, Bool.and_true, ↓reduceIte, add_zero]
            constructor
            · intro h0
              rw [a1 (by omega), b1 (by omega)]
            · intro hh
              simp only [Bool.and_eq_true] at hh ⊢
              exact ⟨a2 hh.1, b2 hh.2⟩
          · simp only [Gate.lineDegree, GateOp.eval]
            simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, List.any_cons,
              List.any_nil, id, Bool.or_false, reduceCtorEq, ↓reduceIte, Nat.max_zero]
            constructor
            · intro h0
              rw [a1 (by omega), b1 (by omega)]
            · intro hh
              simp only [Bool.or_eq_true] at hh ⊢
              exact hh.imp a2 b2
        · simp at hl
      · rw [wv_ge _ _ _ _ (by omega), wv_ge _ _ _ _ (by omega)]
        exact ⟨fun _ => rfl, fun h => h⟩

theorem run_false (m : ℕ) (w : List Bool) :
    run evf (List.replicate m (Gate.mk GateOp.or [])) w = w ++ List.replicate m false := by
  induction m with
  | zero => simp [run]
  | succ m ih =>
    rw [List.replicate_succ', run_snoc, ih, List.replicate_succ', ← List.append_assoc]
    simp [evf, GateOp.eval]

theorem ofFn_app {n m : ℕ} (x : Fin n → Bool) :
    List.ofFn (Fin.append x (fun _ : Fin m => false)) = List.ofFn x ++ List.replicate m false := by
  rw [List.ofFn_fin_append, List.ofFn_const]

theorem ncard_cnt (N s : ℕ) (deg : List ℕ) :
    Set.ncard {j : ℕ | j < s ∧ 0 < deg.getD (N + j) 0} = cnt N deg s := by
  unfold cnt
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp

theorem gate_hyp (n m : ℕ) (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack (n + m) C)
    (hX : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → (gateAt C j).inputs.length = 2 →
      ∃ i ∈ (gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) :
    GateHyp (n + m) (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates := by
  intro k hk
  obtain ⟨h1, h2⟩ := gate_ops C hM k hk
  exact ⟨h1, h2, hR k hk, hX k hk⟩

theorem tinv_init (Dp : ℕ → Prop) (u v : ℕ → Bool) (r bound : ℕ) (A : ℕ → Bool)
    (hA : ∀ w, A w = decide (w = r)) (hx : ∀ w, ¬ Dp w → u w = v w)
    (hb : u r = true → r < bound) :
    Tinv Dp u v (u r) (v r) bound A := by
  refine ⟨?_, ?_, ?_⟩
  · intro w _ _ ha hz
    rw [hA] at ha
    simp only [decide_eq_true_eq] at ha
    subst ha
    exact hz
  · intro w _ _ ha hz
    rw [hA] at ha
    simp only [decide_eq_true_eq] at ha
    subst ha
    exact hz
  · intro h
    by_cases hd : Dp r
    · right
      exact ⟨r, hb h, hd, by simp [hA], h⟩
    · left
      rw [← hx r hd]
      exact h

theorem main (n m : ℕ) (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack (n + m) C)
    (hX : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → (gateAt C j).inputs.length = 2 →
      ∃ i ∈ (gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) :
    ∃ (D : Circuit) (o : Fin m → ℕ), Monotone2 D ∧ ReadsBack n D ∧
      D.size ≤ C.size + 3 * Set.ncard {j : ℕ | j < C.gates.length ∧
        0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} + m ∧
      ∀ (x : Fin n → Bool) (j : Fin m),
        circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) =
          (circuitFun (n + m) C (Fin.append x (fun _ => false)) ||
            (D.wires (List.ofFn x)).getD (o j) false) := by
  have hF := fun (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) => fwd n m C hM hR x y w
  have hcf : ∀ z : Fin (n + m) → Bool, circuitFun (n + m) C z = wv C (n + m) z C.output :=
    fun _ => rfl
  rw [ncard_cnt]
  by_cases hout : 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD C.output 0
  · rcases Nat.lt_or_ge C.output (n + m) with hlt | hge
    · -- the output is a line input
      have hdi := deg_input C (n + m) (Finset.Ico n (n + m)) C.output hlt
      have hn : n ≤ C.output := by
        by_contra hcon
        have : C.output ∉ Finset.Ico n (n + m) := by simp; omega
        rw [hdi] at hout
        simp [this] at hout
      refine ⟨Circuit.mk [Gate.mk GateOp.and []] 0,
        fun j => if n + j.val = C.output then n else n + 1, ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_singleton] at hg
        subst hg
        simp
      · show RBL n [Gate.mk GateOp.and []]
        exact RBL_empty _ _ (by simp)
      · simp only [Circuit.size, List.length_singleton]
        omega
      · intro x j
        rw [hcf, hcf, wv_input _ _ _ _ hlt, wv_input _ _ _ _ hlt, app_ge _ _ _ _ hn,
          app_ge _ _ _ _ hn]
        have hw : (Circuit.mk [Gate.mk GateOp.and []] 0).wires (List.ofFn x)
            = List.ofFn x ++ [true] := by
          simp [Circuit.wires, GateOp.eval]
        rw [hw]
        have hlen : (List.ofFn x).length = n := by simp
        by_cases hj : n + j.val = C.output
        · have e1 : (⟨C.output - n, by omega⟩ : Fin m) = j := by
            ext
            simp only
            omega
          have e2 : (List.ofFn x ++ [true]).getD n false = true := by
            have h2 := getD_app_len (List.ofFn x) true false
            rw [hlen] at h2
            exact h2
          simp only [hj, ↓reduceIte, e1]
          rw [e2]
          simp
        · have e1 : (⟨C.output - n, by omega⟩ : Fin m) ≠ j := by
            intro hcon
            apply hj
            rw [← hcon]
            simp only
            omega
          simp only [hj, ↓reduceIte, e1, decide_false]
          rw [getD_ge _ _ _ (by simp)]
          rfl
    · -- the output is a line-dependent gate: the reverse pass
      have hks : C.output - (n + m) < C.gates.length := by
        by_contra hcon
        rw [deg_ge _ _ _ _ (by omega)] at hout
        omega
      have hcpos : 1 ≤ cnt (n + m) (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates.length := by
        unfold cnt
        apply Finset.card_pos.mpr
        refine ⟨C.output - (n + m), ?_⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨hks, ?_⟩
        have e : n + m + (C.output - (n + m)) = C.output := by omega
        rw [e]
        exact hout
      have hgs := gate_hyp n m C hM hR hX
      have hg0 : Good (n + m + C.gates.length + 1)
          ((fun w => if w = C.output then n + m + C.gates.length else n), ([] : List Gate)) := by
        refine ⟨?_, ?_, ?_⟩
        · intro w
          simp only [List.length_nil]
          split_ifs <;> omega
        · intro g hg
          simp at hg
        · intro j hj
          simp at hj
      obtain ⟨q1, q2⟩ := iter_good (n + m + C.gates.length + 1) (n + m)
        (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates _ (by omega) hgs hg0
        C.gates.length (le_refl _)
      obtain ⟨q11, q12, q13⟩ := q1
      refine ⟨Circuit.mk (List.replicate m (Gate.mk GateOp.or []) ++ (C.gates ++
        ([Gate.mk GateOp.and []] ++ (stAt (n + m + C.gates.length + 1) (n + m)
          (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates
          ((fun w => if w = C.output then n + m + C.gates.length else n), ([] : List Gate))
          C.gates.length).2))) 0,
        fun j => (stAt (n + m + C.gates.length + 1) (n + m)
          (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates
          ((fun w => if w = C.output then n + m + C.gates.length else n), ([] : List Gate))
          C.gates.length).1 (n + j.val), ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hg
        rcases hg with ⟨_, rfl⟩ | hg | rfl | hg
        · simp
        · exact hM g hg
        · simp
        · obtain ⟨h1, h2⟩ := q12 g hg
          refine ⟨?_, h2⟩
          rcases h1 with h1 | h1 <;> simp [h1]
      · show RBL n _
        apply RBL_append
        · exact RBL_empty _ _ (by
            intro g hg
            simp only [List.mem_replicate] at hg
            rw [hg.2])
        · rw [List.length_replicate]
          apply RBL_append _ _ _ hR
          apply RBL_append
          · exact RBL_empty _ _ (by simp)
          · exact q13
      · simp only [Circuit.size, List.length_append, List.length_replicate, List.length_singleton]
        simp only [List.length_nil] at q2
        omega
      · intro x j
        obtain ⟨st, hst⟩ : ∃ st, st = stAt (n + m + C.gates.length + 1) (n + m)
          (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates
          ((fun w => if w = C.output then n + m + C.gates.length else n), ([] : List Gate))
          C.gates.length := ⟨_, rfl⟩
        rw [← hst]
        obtain ⟨base, hbase⟩ : ∃ base, base =
          C.wires (List.ofFn (Fin.append x (fun _ : Fin m => false))) ++ [true] := ⟨_, rfl⟩
        have hvl : (C.wires (List.ofFn (Fin.append x (fun _ : Fin m => false)))).length
            = n + m + C.gates.length := by
          rw [wires_run, run_length]
          simp
        have hBl : base.length = n + m + C.gates.length + 1 := by
          rw [hbase, List.length_append, hvl]
          rfl
        have hw : (Circuit.mk (List.replicate m (Gate.mk GateOp.or []) ++ (C.gates ++
            ([Gate.mk GateOp.and []] ++ st.2))) 0).wires (List.ofFn x) = run evf st.2 base := by
          rw [wires_run]
          simp only []
          rw [run_append, run_append, run_append, run_false, ← ofFn_app, hbase, wires_run]
          congr 1
        rw [hw, hcf, hcf]
        have hv : ∀ i < n + m + C.gates.length,
            base.getD i false = wv C (n + m) (Fin.append x (fun _ => false)) i := by
          intro i hi
          rw [hbase, getD_app_lt _ _ _ _ (by omega)]
          rfl
        have hT : base.getD (n + m + C.gates.length) false = true := by
          rw [hbase, ← hvl, getD_app_len]
        have hFl : base.getD n false = false := by
          rw [hv n (by have := j.isLt; omega), wv_input _ _ _ _ (by have := j.isLt; omega),
            app_ge _ _ _ _ (le_refl _)]
        have hx : ∀ w, ¬ 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0 →
            wv C (n + m) (Fin.append x (fun l => decide (l = j))) w
              = wv C (n + m) (Fin.append x (fun _ => false)) w := by
          intro w hw0
          exact (hF x _ w).1 (by omega)
        have hI0 := tinv_init (fun w => 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0)
          (wv C (n + m) (Fin.append x (fun l => decide (l = j))))
          (wv C (n + m) (Fin.append x (fun _ => false))) C.output (n + m + C.gates.length)
          (aval base ((fun w => if w = C.output then n + m + C.gates.length else n), ([] : List Gate)))
          (by
            intro w
            unfold aval
            show (base).getD (if w = C.output then n + m + C.gates.length else n) false = _
            by_cases hwo : w = C.output
            · rw [ite_p _ _ _ hwo, hT]; simp [hwo]
            · rw [ite_n _ _ _ hwo, hFl]; simp [hwo])
          hx
          (by
            intro hu
            by_contra hcon
            rw [wv_ge _ _ _ _ (by omega)] at hu
            exact Bool.false_ne_true hu)
        have hfin := iter_inv (n + m + C.gates.length + 1) (n + m)
          (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates _ base _ _ _ _ hBl (by omega)
          hgs hg0 (fun i hi _ => hv i hi)
          (fun k hk => wv_gate C (n + m) _ hR k hk) (fun k hk => wv_gate C (n + m) _ hR k hk)
          hx hI0 C.gates.length (le_refl _)
        rw [← hst] at hfin
        obtain ⟨f1, _, f3⟩ := hfin
        have hjlt : n + j.val < n + m := by have := j.isLt; omega
        have hdj : 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + j.val) 0 := by
          rw [deg_input _ _ _ _ hjlt]
          have : n + j.val ∈ Finset.Ico n (n + m) := by simp
          simp [this]
        have huj : wv C (n + m) (Fin.append x (fun l => decide (l = j))) (n + j.val) = true := by
          rw [wv_input _ _ _ _ hjlt, app_ge _ _ _ _ (by omega)]
          simp only [decide_eq_true_eq]
          ext
          simp
        show _ = (_ || aval base st (n + j.val))
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true]
        constructor
        · intro huo
          rcases f3 huo with h | ⟨w, hw, hd, ha, hz⟩
          · left; exact h
          · right
            have hwN : w < n + m := by omega
            have hwn : n ≤ w := by
              by_contra hcon
              have hd' : 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0 := hd
              rw [deg_input _ _ _ _ hwN] at hd'
              have : w ∉ Finset.Ico n (n + m) := by simp; omega
              simp [this] at hd'
            rw [wv_input _ _ _ _ hwN, app_ge _ _ _ _ hwn] at hz
            simp only [decide_eq_true_eq] at hz
            have e : w = n + j.val := by
              rw [← hz]
              simp only
              omega
            rw [← e]
            exact ha
        · rintro (h | h)
          · exact (hF x _ C.output).2 h
          · exact f1 (n + j.val) (by omega) hdj h huj
  · -- the output does not depend on the lines
    refine ⟨Circuit.mk [] 0, fun _ => n, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp at hg
    · intro j hj
      simp at hj
    · simp [Circuit.size]
    · intro x j
      rw [hcf, hcf, (hF x _ C.output).1 (by omega)]
      have : ((Circuit.mk [] 0).wires (List.ofFn x)).getD n false = false := by
        apply getD_ge
        simp [Circuit.wires]
      rw [this]
      simp

end P1622

theorem P1622_main : ∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧ D.size ≤ C.size + 3 * Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} + m ∧ ∀ (x : Fin n → Bool) (j : Fin m), PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || (D.wires (List.ofFn x)).getD (o j) false) :=
  fun n m C hM hR hX => PEqualNP.Outside.L_meta_3040.SurvivorBound3040.P1622.main n m C hM hR hX

end Sec1622

section Sec1623

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace P1623

theorem aj_getD_app_lt {α : Type} (l l' : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem aj_getD_app_len {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem aj_getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def aj_dflt : Gate := Gate.mk GateOp.or []

-- generic gate-list fold
def aj_run {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) w

theorem aj_run_snoc {α : Type} (f : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    aj_run f (gs ++ [g]) w = aj_run f gs w ++ [f (aj_run f gs w) g] := by
  simp [aj_run]

theorem aj_run_append {α : Type} (f : List α → Gate → α) (g1 g2 : List Gate) (w : List α) :
    aj_run f (g1 ++ g2) w = aj_run f g2 (aj_run f g1 w) := by
  simp [aj_run]

theorem aj_run_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) :
    (aj_run f gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [aj_run]
  | append_singleton gs g ih => rw [aj_run_snoc]; simp [ih]; omega

theorem aj_run_lt {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) (d : α) (i : ℕ)
    (h : i < w.length) : (aj_run f gs w).getD i d = w.getD i d := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [aj_run_snoc, aj_getD_app_lt _ _ _ _ (by rw [aj_run_length]; omega), ih]

theorem aj_run_gate {α : Type} (f : List α → Gate → α) (d : α)
    (hf : ∀ (g : Gate) (w w' : List α), (∀ i ∈ g.inputs, w.getD i d = w'.getD i d) → f w g = f w' g)
    (gs : List Gate) (w : List α) (L : ℕ) (hL : w.length = L) (k : ℕ) (hk : k < gs.length)
    (hr : ∀ i ∈ (gs.getD k aj_dflt).inputs, i < L + k) :
    (aj_run f gs w).getD (L + k) d = f (aj_run f gs w) (gs.getD k aj_dflt) := by
  subst hL
  induction gs using List.reverseRecOn with
  | nil => simp at hk
  | append_singleton gs g ih =>
    rw [aj_run_snoc]
    rcases Nat.lt_or_ge k gs.length with h | h
    · have e : (gs ++ [g]).getD k aj_dflt = gs.getD k aj_dflt := aj_getD_app_lt _ _ _ _ h
      rw [e] at hr ⊢
      rw [aj_getD_app_lt _ _ _ _ (by rw [aj_run_length]; omega), ih h hr]
      apply hf
      intro i hi
      symm
      exact aj_getD_app_lt _ _ _ _ (by rw [aj_run_length]; have := hr i hi; omega)
    · have hk' : k = gs.length := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      subst hk'
      have e : (gs ++ [g]).getD gs.length aj_dflt = g := aj_getD_app_len _ _ _
      rw [e] at hr ⊢
      have e2 : w.length + gs.length = (aj_run f gs w).length := (aj_run_length f gs w).symm
      rw [e2, aj_getD_app_len]
      apply hf
      intro i hi
      symm
      exact aj_getD_app_lt _ _ _ _ (by rw [aj_run_length]; have := hr i hi; omega)

def aj_evf (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def aj_ldf (d : List ℕ) (g : Gate) : ℕ := g.lineDegree d

theorem aj_evf_congr (g : Gate) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = w'.getD i false) : aj_evf w g = aj_evf w' g := by
  unfold aj_evf
  rw [List.map_congr_left h]

theorem aj_ldf_congr (g : Gate) (w w' : List ℕ)
    (h : ∀ i ∈ g.inputs, w.getD i 0 = w'.getD i 0) : aj_ldf w g = aj_ldf w' g := by
  unfold aj_ldf Gate.lineDegree
  rw [List.map_congr_left h]

-- reads-back for bare lists
def aj_RBL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j aj_dflt).inputs, i < n + j

theorem aj_RBL_append (n : ℕ) (g1 g2 : List Gate) (h1 : aj_RBL n g1) (h2 : aj_RBL (n + g1.length) g2) :
    aj_RBL n (g1 ++ g2) := by
  intro j hj i hi
  rcases Nat.lt_or_ge j g1.length with h | h
  · rw [aj_getD_app_lt _ _ _ _ h] at hi
    exact h1 j h i hi
  · rw [List.getD_append_right _ _ _ _ h] at hi
    simp only [List.length_append] at hj
    have := h2 (j - g1.length) (by omega) i hi
    omega

theorem aj_RBL_empty (n : ℕ) (gs : List Gate) (h : ∀ g ∈ gs, g.inputs = []) : aj_RBL n gs := by
  intro j hj i hi
  have hm : gs.getD j aj_dflt ∈ gs := by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  rw [h _ hm] at hi
  simp at hi

theorem aj_RBL_snoc (n : ℕ) (gs : List Gate) (g : Gate) (h1 : aj_RBL n gs)
    (h2 : ∀ i ∈ g.inputs, i < n + gs.length) : aj_RBL n (gs ++ [g]) := by
  apply aj_RBL_append _ _ _ h1
  intro j hj i hi
  simp only [List.length_singleton] at hj
  have hj0 : j = 0 := by omega
  subst hj0
  have := h2 i (by simpa using hi)
  omega

-- the state of the reverse pass: accumulator wire per wire, and the appended gates
def aj_Good (B : ℕ) (st : (ℕ → ℕ) × List Gate) : Prop :=
  (∀ w, st.1 w < B + st.2.length) ∧
  (∀ g ∈ st.2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  aj_RBL B st.2

def aj_link (B : ℕ) (st : (ℕ → ℕ) × List Gate) (a src : ℕ) : (ℕ → ℕ) × List Gate :=
  (Function.update st.1 a (B + st.2.length), st.2 ++ [Gate.mk GateOp.or [st.1 a, src]])

def aj_andl (B : ℕ) (st : (ℕ → ℕ) × List Gate) (W tgt side : ℕ) : (ℕ → ℕ) × List Gate :=
  aj_link B (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) tgt (B + st.2.length)

def aj_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def aj_proc (B : ℕ) (deg : List ℕ) (op : GateOp) (l : List ℕ) (W : ℕ)
    (st : (ℕ → ℕ) × List Gate) : (ℕ → ℕ) × List Gate :=
  if 0 < deg.getD W 0 then
    if aj_isAnd op = true ∧ l.length = 2 then
      if 0 < deg.getD (l.getD 0 0) 0 then aj_andl B st W (l.getD 0 0) (l.getD 1 0)
      else aj_andl B st W (l.getD 1 0) (l.getD 0 0)
    else l.foldl (fun s a => aj_link B s a (st.1 W)) st
  else st

def aj_aval (base : List Bool) (st : (ℕ → ℕ) × List Gate) (w : ℕ) : Bool :=
  (aj_run aj_evf st.2 base).getD (st.1 w) false

theorem aj_link_spec (B : ℕ) (base : List Bool) (st : (ℕ → ℕ) × List Gate) (a src : ℕ)
    (hB : base.length = B) (hg : aj_Good B st) (hs : src < B + st.2.length) :
    aj_Good B (aj_link B st a src) ∧ (aj_link B st a src).2.length = st.2.length + 1 ∧
    (∀ i < B + st.2.length,
      (aj_run aj_evf (aj_link B st a src).2 base).getD i false = (aj_run aj_evf st.2 base).getD i false) ∧
    ∀ w, aj_aval base (aj_link B st a src) w =
      (aj_aval base st w || (decide (w = a) && (aj_run aj_evf st.2 base).getD src false)) := by
  obtain ⟨g1, g2, g3⟩ := hg
  have hlen : (aj_run aj_evf st.2 base).length = B + st.2.length := by rw [aj_run_length, hB]
  have hrun : aj_run aj_evf (aj_link B st a src).2 base = aj_run aj_evf st.2 base ++
      [((aj_run aj_evf st.2 base).getD (st.1 a) false || (aj_run aj_evf st.2 base).getD src false)] := by
    simp [aj_link, aj_run_snoc, aj_evf, GateOp.eval]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro w
    simp only [aj_link, List.length_append, List.length_singleton, Function.update_apply]
    split_ifs
    · omega
    · have := g1 w
      omega
  · intro g hg
    simp only [aj_link, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact g2 g hg
    · exact ⟨Or.inr rfl, by simp⟩
  · apply aj_RBL_snoc _ _ _ g3
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact g1 a
    · exact hs
  · simp [aj_link]
  · intro i hi
    rw [hrun]
    exact aj_getD_app_lt _ _ _ _ (by omega)
  · intro w
    unfold aj_aval
    rw [hrun]
    by_cases hw : w = a
    · subst hw
      have e : (aj_link B st w src).1 w = (aj_run aj_evf st.2 base).length := by simp [aj_link, hlen]
      rw [e, aj_getD_app_len]
      simp
    · have e : (aj_link B st a src).1 w = st.1 w := by simp [aj_link, hw]
      rw [e, aj_getD_app_lt _ _ _ _ (by have := g1 w; omega)]
      simp [hw]

theorem aj_ite_p {α : Type} (c : Prop) [Decidable c] (a b : α) (h : c) : (if c then a else b) = a := by
  simp [h]

theorem aj_ite_n {α : Type} (c : Prop) [Decidable c] (a b : α) (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem aj_bool_aux (p q r s : Bool) : ((p || (q && s)) || (r && s)) = (p || ((q || r) && s)) := by
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

theorem aj_fold_spec (B : ℕ) (base : List Bool) (src : ℕ) (hB : base.length = B) (l : List ℕ) :
    ∀ (st : (ℕ → ℕ) × List Gate), aj_Good B st → src < B + st.2.length →
    aj_Good B (l.foldl (fun s a => aj_link B s a src) st) ∧
    (l.foldl (fun s a => aj_link B s a src) st).2.length = st.2.length + l.length ∧
    (∀ i < B + st.2.length,
      (aj_run aj_evf (l.foldl (fun s a => aj_link B s a src) st).2 base).getD i false =
        (aj_run aj_evf st.2 base).getD i false) ∧
    ∀ w, aj_aval base (l.foldl (fun s a => aj_link B s a src) st) w =
      (aj_aval base st w || (decide (w ∈ l) && (aj_run aj_evf st.2 base).getD src false)) := by
  induction l with
  | nil =>
    intro st hg _
    simp [hg]
  | cons a l ih =>
    intro st hg hs
    obtain ⟨k1, k2, k3, k4⟩ := aj_link_spec B base st a src hB hg hs
    obtain ⟨j1, j2, j3, j4⟩ := ih (aj_link B st a src) k1 (by omega)
    rw [List.foldl_cons]
    refine ⟨j1, ?_, ?_, ?_⟩
    · rw [j2, k2, List.length_cons]
      omega
    · intro i hi
      rw [j3 i (by omega), k3 i hi]
    · intro w
      rw [j4 w, k4 w, k3 src hs, aj_bool_aux]
      congr 2
      simp [Bool.decide_or]

theorem aj_andl_spec (B : ℕ) (base : List Bool) (st : (ℕ → ℕ) × List Gate) (W tgt side : ℕ)
    (hB : base.length = B) (hg : aj_Good B st) (hs : side < B) :
    aj_Good B (aj_andl B st W tgt side) ∧ (aj_andl B st W tgt side).2.length = st.2.length + 2 ∧
    ∀ w, aj_aval base (aj_andl B st W tgt side) w =
      (aj_aval base st w || (decide (w = tgt) && (aj_aval base st W && base.getD side false))) := by
  have hg' := hg
  obtain ⟨g1, g2, g3⟩ := hg
  have hlen : (aj_run aj_evf st.2 base).length = B + st.2.length := by rw [aj_run_length, hB]
  have hrun : aj_run aj_evf (st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) base = aj_run aj_evf st.2 base ++
      [((aj_run aj_evf st.2 base).getD (st.1 W) false && (aj_run aj_evf st.2 base).getD side false)] := by
    simp [aj_run_snoc, aj_evf, GateOp.eval]
  have hg1 : aj_Good B (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w
      have := g1 w
      show st.1 w < B + (st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]).length
      simp only [List.length_append, List.length_singleton]
      omega
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact g2 g hg
      · exact ⟨Or.inl rfl, by simp⟩
    · apply aj_RBL_snoc _ _ _ g3
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h
      · rw [h]; exact g1 W
      · rw [h]; omega
  obtain ⟨k1, k2, _, k4⟩ := aj_link_spec B base (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]])
    tgt (B + st.2.length) hB hg1 (by simp)
  refine ⟨k1, ?_, ?_⟩
  · unfold aj_andl
    rw [k2]
    simp
  · intro w
    unfold aj_andl
    rw [k4 w]
    have e1 : aj_aval base (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) w = aj_aval base st w := by
      unfold aj_aval
      show (aj_run aj_evf (st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) base).getD (st.1 w) false = _
      rw [hrun]
      exact aj_getD_app_lt _ _ _ _ (by have := g1 w; omega)
    have e2 : (aj_run aj_evf (st.1, st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]).2 base).getD
        (B + st.2.length) false = (aj_aval base st W && base.getD side false) := by
      show (aj_run aj_evf (st.2 ++ [Gate.mk GateOp.and [st.1 W, side]]) base).getD _ _ = _
      rw [hrun, ← hlen, aj_getD_app_len]
      unfold aj_aval
      rw [aj_run_lt aj_evf st.2 base false side (by omega)]
    rw [e1, e2]

-- the logical invariant of the reverse pass
def aj_Tinv (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (bound : ℕ) (A : ℕ → Bool) : Prop :=
  (∀ w < bound, Dp w → A w = true → u w = true → uo = true) ∧
  (∀ w < bound, Dp w → A w = true → v w = true → vo = true) ∧
  (uo = true → vo = true ∨ ∃ w < bound, Dp w ∧ A w = true ∧ u w = true)

theorem aj_tinv_skip (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (W : ℕ) (A : ℕ → Bool)
    (hD : ¬ Dp W) (hI : aj_Tinv Dp u v uo vo (W + 1) A) : aj_Tinv Dp u v uo vo W A := by
  obtain ⟨h1, h2, h3⟩ := hI
  refine ⟨fun w hw => h1 w (by omega), fun w hw => h2 w (by omega), ?_⟩
  intro huo
  rcases h3 huo with h | ⟨w, hw, hd, ha, hz⟩
  · left; exact h
  · right
    refine ⟨w, ?_, hd, ha, hz⟩
    rcases Nat.lt_or_ge w W with hlt | hge
    · exact hlt
    · have e : w = W := by omega
      subst e
      exact absurd hd hD

theorem aj_tinv_or (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (W : ℕ) (l : List ℕ)
    (A A' : ℕ → Bool) (hr : ∀ i ∈ l, i < W) (hD : Dp W)
    (hA : ∀ w, A' w = (A w || (decide (w ∈ l) && A W)))
    (hx : ∀ w, ¬ Dp w → u w = v w)
    (p1u : ∀ i ∈ l, u i = true → u W = true) (p1v : ∀ i ∈ l, v i = true → v W = true)
    (p2 : u W = true → v W = true ∨ ∃ i ∈ l, u i = true)
    (hI : aj_Tinv Dp u v uo vo (W + 1) A) : aj_Tinv Dp u v uo vo W A' := by
  obtain ⟨h1, h2, h3⟩ := hI
  refine ⟨?_, ?_, ?_⟩
  · intro w hw hd ha hz
    rw [hA] at ha
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
    rcases ha with ha | ⟨hm, haW⟩
    · exact h1 w (by omega) hd ha hz
    · exact h1 W (by omega) hD haW (p1u w hm hz)
  · intro w hw hd ha hz
    rw [hA] at ha
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
    rcases ha with ha | ⟨hm, haW⟩
    · exact h2 w (by omega) hd ha hz
    · exact h2 W (by omega) hD haW (p1v w hm hz)
  · intro huo
    rcases h3 huo with h | ⟨w, hw, hd, ha, hz⟩
    · left; exact h
    · rcases Nat.lt_or_ge w W with hlt | hge
      · right
        exact ⟨w, hlt, hd, by rw [hA, ha]; rfl, hz⟩
      · have e : w = W := by omega
        subst e
        rcases p2 hz with hvW | ⟨i, hi, hui⟩
        · left; exact h2 w (by omega) hd ha hvW
        · by_cases hdi : Dp i
          · right
            exact ⟨i, hr i hi, hdi, by simp [hA, hi, ha], hui⟩
          · left
            have e := hx i hdi
            exact h2 w (by omega) hd ha (p1v i hi (by rw [← e]; exact hui))

theorem aj_tinv_and (Dp : ℕ → Prop) (u v : ℕ → Bool) (uo vo : Bool) (W tgt side : ℕ)
    (A A' : ℕ → Bool) (ht : tgt < W) (hD : Dp W) (hs : ¬ Dp side)
    (hA : ∀ w, A' w = (A w || (decide (w = tgt) && (A W && v side))))
    (hx : ∀ w, ¬ Dp w → u w = v w)
    (hu : u W = (u tgt && u side)) (hv : v W = (v tgt && v side))
    (hI : aj_Tinv Dp u v uo vo (W + 1) A) : aj_Tinv Dp u v uo vo W A' := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hsd := hx side hs
  refine ⟨?_, ?_, ?_⟩
  · intro w hw hd ha hz
    rw [hA] at ha
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
    rcases ha with ha | ⟨hm, haW, hvs⟩
    · exact h1 w (by omega) hd ha hz
    · subst hm
      exact h1 W (by omega) hD haW (by rw [hu, hz, hsd, hvs]; rfl)
  · intro w hw hd ha hz
    rw [hA] at ha
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
    rcases ha with ha | ⟨hm, haW, hvs⟩
    · exact h2 w (by omega) hd ha hz
    · subst hm
      exact h2 W (by omega) hD haW (by rw [hv, hz, hvs]; rfl)
  · intro huo
    rcases h3 huo with h | ⟨w, hw, hd, ha, hz⟩
    · left; exact h
    · rcases Nat.lt_or_ge w W with hlt | hge
      · right
        exact ⟨w, hlt, hd, by rw [hA, ha]; rfl, hz⟩
      · have e : w = W := by omega
        subst e
        rw [hu] at hz
        simp only [Bool.and_eq_true] at hz
        have hvs : v side = true := by rw [← hsd]; exact hz.2
        by_cases hdt : Dp tgt
        · right
          exact ⟨tgt, ht, hdt, by simp [hA, ha, hvs], hz.1⟩
        · left
          have e := hx tgt hdt
          exact h2 w (by omega) hd ha (by rw [hv, ← e, hz.1, hvs]; rfl)

theorem aj_fold_case (B : ℕ) (deg : List ℕ) (base : List Bool) (l : List ℕ) (W : ℕ)
    (st : (ℕ → ℕ) × List Gate) (hB : base.length = B) (hl : l.length ≤ 2)
    (hr : ∀ i ∈ l, i < W) (hg : aj_Good B st) (hD : 0 < deg.getD W 0) :
    aj_Good B (l.foldl (fun s a => aj_link B s a (st.1 W)) st) ∧
    (l.foldl (fun s a => aj_link B s a (st.1 W)) st).2.length ≤ st.2.length + 2 ∧
    ∀ (u v : ℕ → Bool) (uo vo : Bool), (∀ w, ¬ 0 < deg.getD w 0 → u w = v w) →
      (∀ i ∈ l, u i = true → u W = true) → (∀ i ∈ l, v i = true → v W = true) →
      (u W = true → v W = true ∨ ∃ i ∈ l, u i = true) →
      aj_Tinv (fun w => 0 < deg.getD w 0) u v uo vo (W + 1) (aj_aval base st) →
      aj_Tinv (fun w => 0 < deg.getD w 0) u v uo vo W
        (aj_aval base (l.foldl (fun s a => aj_link B s a (st.1 W)) st)) := by
  obtain ⟨j1, j2, _, j4⟩ := aj_fold_spec B base (st.1 W) hB l st hg (hg.1 W)
  refine ⟨j1, by omega, ?_⟩
  intro u v uo vo hx p1u p1v p2 hI
  exact aj_tinv_or _ u v uo vo W l _ _ hr hD j4 hx p1u p1v p2 hI

theorem aj_proc_spec (B : ℕ) (deg : List ℕ) (base : List Bool) (op : GateOp) (l : List ℕ) (W : ℕ)
    (st : (ℕ → ℕ) × List Gate) (hB : base.length = B) (hW : W < B)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hl : l.length ≤ 2) (hr : ∀ i ∈ l, i < W)
    (hc : op = GateOp.and → l.length = 2 → ∃ i ∈ l, deg.getD i 0 = 0)
    (hg : aj_Good B st) :
    aj_Good B (aj_proc B deg op l W st) ∧
    (aj_proc B deg op l W st).2.length ≤ st.2.length + (if 0 < deg.getD W 0 then 2 else 0) ∧
    ∀ (u v : ℕ → Bool) (uo vo : Bool),
      (∀ i < W, ¬ 0 < deg.getD i 0 → base.getD i false = v i) →
      u W = op.eval (l.map u) → v W = op.eval (l.map v) →
      (∀ w, ¬ 0 < deg.getD w 0 → u w = v w) →
      aj_Tinv (fun w => 0 < deg.getD w 0) u v uo vo (W + 1) (aj_aval base st) →
      aj_Tinv (fun w => 0 < deg.getD w 0) u v uo vo W (aj_aval base (aj_proc B deg op l W st)) := by
  by_cases hD : 0 < deg.getD W 0
  · rcases hop with rfl | rfl
    · rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · have e : aj_proc B deg GateOp.and [] W st
            = ([] : List ℕ).foldl (fun s a => aj_link B s a (st.1 W)) st := by
          unfold aj_proc
          rw [aj_ite_p _ _ _ hD, aj_ite_n _ _ _ (by simp)]
        rw [e]
        obtain ⟨f1, f2, f3⟩ := aj_fold_case B deg base [] W st hB hl hr hg hD
        refine ⟨f1, by simp only [hD, ↓reduceIte]; exact f2, ?_⟩
        intro u v uo vo _ hu hv hx hI
        refine f3 u v uo vo hx (by simp) (by simp) ?_ hI
        intro _
        left
        simpa [GateOp.eval] using hv
      · have e : aj_proc B deg GateOp.and [a] W st
            = [a].foldl (fun s a => aj_link B s a (st.1 W)) st := by
          unfold aj_proc
          rw [aj_ite_p _ _ _ hD, aj_ite_n _ _ _ (by simp)]
        rw [e]
        obtain ⟨f1, f2, f3⟩ := aj_fold_case B deg base [a] W st hB hl hr hg hD
        refine ⟨f1, by simp only [hD, ↓reduceIte]; exact f2, ?_⟩
        intro u v uo vo _ hu hv hx hI
        have hu' : u W = u a := by simpa [GateOp.eval] using hu
        have hv' : v W = v a := by simpa [GateOp.eval] using hv
        refine f3 u v uo vo hx ?_ ?_ ?_ hI
        · intro i hi h
          simp only [List.mem_singleton] at hi
          subst hi
          rw [hu']; exact h
        · intro i hi h
          simp only [List.mem_singleton] at hi
          subst hi
          rw [hv']; exact h
        · intro h
          right
          exact ⟨a, by simp, by rw [← hu']; exact h⟩
      · have e : aj_proc B deg GateOp.and [a, b] W st
            = if 0 < deg.getD a 0 then aj_andl B st W a b else aj_andl B st W b a := by
          unfold aj_proc
          rw [aj_ite_p _ _ _ hD, aj_ite_p _ _ _ (by simp [aj_isAnd])]
          rfl
        have ha : a < W := hr a (by simp)
        have hb : b < W := hr b (by simp)
        obtain ⟨i, hi, hi0⟩ := hc rfl rfl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rw [e]
        by_cases hda : 0 < deg.getD a 0
        · simp only [hda, ↓reduceIte]
          have hdb : ¬ 0 < deg.getD b 0 := by
            rcases hi with h | h
            · rw [h] at hi0; omega
            · rw [h] at hi0; omega
          obtain ⟨k1, k2, k3⟩ := aj_andl_spec B base st W a b hB hg (by omega)
          refine ⟨k1, by simp only [hD, ↓reduceIte]; omega, ?_⟩
          intro u v uo vo hbv hu hv hx hI
          have hu' : u W = (u a && u b) := by simpa [GateOp.eval] using hu
          have hv' : v W = (v a && v b) := by simpa [GateOp.eval] using hv
          refine aj_tinv_and _ u v uo vo W a b _ _ ha hD hdb ?_ hx hu' hv' hI
          intro w
          rw [k3 w, hbv b hb hdb]
        · simp only [hda, ↓reduceIte]
          obtain ⟨k1, k2, k3⟩ := aj_andl_spec B base st W b a hB hg (by omega)
          refine ⟨k1, by simp only [hD, ↓reduceIte]; omega, ?_⟩
          intro u v uo vo hbv hu hv hx hI
          have hu' : u W = (u b && u a) := by
            rw [Bool.and_comm]; simpa [GateOp.eval] using hu
          have hv' : v W = (v b && v a) := by
            rw [Bool.and_comm]; simpa [GateOp.eval] using hv
          refine aj_tinv_and _ u v uo vo W b a _ _ hb hD hda ?_ hx hu' hv' hI
          intro w
          rw [k3 w, hbv a ha hda]
      · simp at hl
    · have e : aj_proc B deg GateOp.or l W st
          = l.foldl (fun s a => aj_link B s a (st.1 W)) st := by
        unfold aj_proc
        rw [aj_ite_p _ _ _ hD, aj_ite_n _ _ _ (by simp [aj_isAnd])]
      rw [e]
      obtain ⟨f1, f2, f3⟩ := aj_fold_case B deg base l W st hB hl hr hg hD
      refine ⟨f1, by simp only [hD, ↓reduceIte]; exact f2, ?_⟩
      intro u v uo vo _ hu hv hx hI
      have hu' : u W = true ↔ ∃ i ∈ l, u i = true := by
        rw [hu]; simp [GateOp.eval]
      have hv' : v W = true ↔ ∃ i ∈ l, v i = true := by
        rw [hv]; simp [GateOp.eval]
      refine f3 u v uo vo hx ?_ ?_ ?_ hI
      · intro i hi h
        exact hu'.2 ⟨i, hi, h⟩
      · intro i hi h
        exact hv'.2 ⟨i, hi, h⟩
      · intro h
        right
        exact hu'.1 h
  · have e : aj_proc B deg op l W st = st := by
      unfold aj_proc
      rw [aj_ite_n _ _ _ hD]
    rw [e]
    refine ⟨hg, by simp, ?_⟩
    intro u v uo vo _ _ _ _ hI
    exact aj_tinv_skip _ u v uo vo W _ hD hI

-- the reverse pass over the gate list, last gate first
def aj_stAt (B N : ℕ) (deg : List ℕ) (gs : List Gate) (st0 : (ℕ → ℕ) × List Gate) :
    ℕ → (ℕ → ℕ) × List Gate
  | 0 => st0
  | d + 1 => aj_proc B deg (gs.getD (gs.length - 1 - d) aj_dflt).op
      (gs.getD (gs.length - 1 - d) aj_dflt).inputs (N + (gs.length - 1 - d)) (aj_stAt B N deg gs st0 d)

def aj_cnt (N : ℕ) (deg : List ℕ) (b : ℕ) : ℕ :=
  ((Finset.range b).filter (fun k => 0 < deg.getD (N + k) 0)).card

theorem aj_cnt_succ (N : ℕ) (deg : List ℕ) (b : ℕ) :
    aj_cnt N deg (b + 1) = aj_cnt N deg b + (if 0 < deg.getD (N + b) 0 then 1 else 0) := by
  unfold aj_cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

def aj_GateHyp (N : ℕ) (deg : List ℕ) (gs : List Gate) : Prop :=
  ∀ k < gs.length, ((gs.getD k aj_dflt).op = GateOp.and ∨ (gs.getD k aj_dflt).op = GateOp.or) ∧
    (gs.getD k aj_dflt).inputs.length ≤ 2 ∧ (∀ i ∈ (gs.getD k aj_dflt).inputs, i < N + k) ∧
    ((gs.getD k aj_dflt).op = GateOp.and → (gs.getD k aj_dflt).inputs.length = 2 →
      ∃ i ∈ (gs.getD k aj_dflt).inputs, deg.getD i 0 = 0)

theorem aj_iter_good (B N : ℕ) (deg : List ℕ) (gs : List Gate) (st0 : (ℕ → ℕ) × List Gate)
    (hNB : N + gs.length ≤ B) (hgs : aj_GateHyp N deg gs) (hg0 : aj_Good B st0) :
    ∀ d ≤ gs.length, aj_Good B (aj_stAt B N deg gs st0 d) ∧
      (aj_stAt B N deg gs st0 d).2.length + 2 * aj_cnt N deg (gs.length - d)
        ≤ st0.2.length + 2 * aj_cnt N deg gs.length := by
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨hg0, by simp [aj_stAt]⟩
  | succ d ih =>
    intro hd
    obtain ⟨i1, i2⟩ := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, k = gs.length - 1 - d := ⟨_, rfl⟩
    have hks : k < gs.length := by omega
    obtain ⟨a1, a2, a3, a4⟩ := hgs k hks
    have e : aj_stAt B N deg gs st0 (d + 1) = aj_proc B deg (gs.getD k aj_dflt).op
        (gs.getD k aj_dflt).inputs (N + k) (aj_stAt B N deg gs st0 d) := by
      rw [hk]; rfl
    obtain ⟨p1, p2, _⟩ := aj_proc_spec B deg (List.replicate B false) (gs.getD k aj_dflt).op
      (gs.getD k aj_dflt).inputs (N + k) (aj_stAt B N deg gs st0 d) List.length_replicate
      (by omega) a1 a2 a3 a4 i1
    rw [e]
    refine ⟨p1, ?_⟩
    have e1 : gs.length - d = k + 1 := by omega
    have e2 : gs.length - (d + 1) = k := by omega
    rw [e1, aj_cnt_succ] at i2
    rw [e2]
    split_ifs at p2 i2 <;> omega

theorem aj_iter_inv (B N : ℕ) (deg : List ℕ) (gs : List Gate) (st0 : (ℕ → ℕ) × List Gate)
    (base : List Bool) (u v : ℕ → Bool) (uo vo : Bool)
    (hB : base.length = B) (hNB : N + gs.length ≤ B) (hgs : aj_GateHyp N deg gs) (hg0 : aj_Good B st0)
    (hv : ∀ i < N + gs.length, ¬ 0 < deg.getD i 0 → base.getD i false = v i)
    (hu : ∀ k < gs.length, u (N + k) = (gs.getD k aj_dflt).op.eval ((gs.getD k aj_dflt).inputs.map u))
    (hvv : ∀ k < gs.length, v (N + k) = (gs.getD k aj_dflt).op.eval ((gs.getD k aj_dflt).inputs.map v))
    (hx : ∀ w, ¬ 0 < deg.getD w 0 → u w = v w)
    (hI : aj_Tinv (fun w => 0 < deg.getD w 0) u v uo vo (N + gs.length) (aj_aval base st0)) :
    ∀ d ≤ gs.length, aj_Tinv (fun w => 0 < deg.getD w 0) u v uo vo (N + (gs.length - d))
      (aj_aval base (aj_stAt B N deg gs st0 d)) := by
  intro d
  induction d with
  | zero =>
    intro _
    simpa [aj_stAt] using hI
  | succ d ih =>
    intro hd
    have i1 := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, k = gs.length - 1 - d := ⟨_, rfl⟩
    have hks : k < gs.length := by omega
    obtain ⟨a1, a2, a3, a4⟩ := hgs k hks
    have e : aj_stAt B N deg gs st0 (d + 1) = aj_proc B deg (gs.getD k aj_dflt).op
        (gs.getD k aj_dflt).inputs (N + k) (aj_stAt B N deg gs st0 d) := by
      rw [hk]; rfl
    obtain ⟨_, _, p3⟩ := aj_proc_spec B deg base (gs.getD k aj_dflt).op
      (gs.getD k aj_dflt).inputs (N + k) (aj_stAt B N deg gs st0 d) hB
      (by omega) a1 a2 a3 a4 (aj_iter_good B N deg gs st0 hNB hgs hg0 d (by omega)).1
    have e1 : gs.length - d = k + 1 := by omega
    have e2 : gs.length - (d + 1) = k := by omega
    rw [e1] at i1
    rw [e, e2]
    exact p3 u v uo vo (fun i hi => hv i (by omega)) (hu k hks) (hvv k hks) hx i1

-- wire values and degrees of the given circuit
def aj_wv (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn z)).getD w false

theorem aj_wires_run (C : Circuit) (inp : List Bool) : C.wires inp = aj_run aj_evf C.gates inp := rfl

theorem aj_wv_input (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) (h : w < N) :
    aj_wv C N z w = z ⟨w, h⟩ := by
  unfold aj_wv
  rw [aj_wires_run, aj_run_lt _ _ _ _ _ (by simpa using h),
    List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem aj_wv_ge (C : Circuit) (N : ℕ) (z : Fin N → Bool) (w : ℕ) (h : N + C.gates.length ≤ w) :
    aj_wv C N z w = false := by
  unfold aj_wv
  rw [aj_wires_run]
  exact aj_getD_ge _ _ _ (by rw [aj_run_length]; simpa using h)

theorem aj_wv_gate (C : Circuit) (N : ℕ) (z : Fin N → Bool) (hR : ReadsBack N C) (k : ℕ)
    (hk : k < C.gates.length) :
    aj_wv C N z (N + k) = (C.gates.getD k aj_dflt).op.eval ((C.gates.getD k aj_dflt).inputs.map (aj_wv C N z)) := by
  unfold aj_wv
  rw [aj_wires_run]
  exact aj_run_gate aj_evf false aj_evf_congr C.gates _ N (by simp) k hk (hR k hk)

theorem aj_deg_run (C : Circuit) (N : ℕ) (M : Finset ℕ) : C.lineDegrees N M =
    aj_run aj_ldf C.gates ((List.range N).map fun i => if i ∈ M then 1 else 0) := rfl

theorem aj_deg_input (C : Circuit) (N : ℕ) (M : Finset ℕ) (w : ℕ) (h : w < N) :
    (C.lineDegrees N M).getD w 0 = if w ∈ M then 1 else 0 := by
  rw [aj_deg_run, aj_run_lt _ _ _ _ _ (by simpa using h),
    List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem aj_deg_ge (C : Circuit) (N : ℕ) (M : Finset ℕ) (w : ℕ) (h : N + C.gates.length ≤ w) :
    (C.lineDegrees N M).getD w 0 = 0 := by
  rw [aj_deg_run]
  exact aj_getD_ge _ _ _ (by rw [aj_run_length]; simpa using h)

theorem aj_deg_gate (C : Circuit) (N : ℕ) (M : Finset ℕ) (hR : ReadsBack N C) (k : ℕ)
    (hk : k < C.gates.length) :
    (C.lineDegrees N M).getD (N + k) 0 = (C.gates.getD k aj_dflt).lineDegree (C.lineDegrees N M) := by
  rw [aj_deg_run]
  exact aj_run_gate aj_ldf 0 aj_ldf_congr C.gates _ N (by simp) k hk (hR k hk)

theorem aj_app_lt {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) (h : w < n + m)
    (hw : w < n) : Fin.append x y ⟨w, h⟩ = x ⟨w, hw⟩ :=
  Fin.append_left x y ⟨w, hw⟩

theorem aj_app_ge {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) (h : w < n + m)
    (hw : n ≤ w) : Fin.append x y ⟨w, h⟩ = y ⟨w - n, by omega⟩ := by
  have e : (⟨w, h⟩ : Fin (n + m)) = Fin.natAdd n ⟨w - n, by omega⟩ := by
    ext
    simp only [Fin.natAdd_mk]
    omega
  rw [e, Fin.append_right]

theorem aj_gate_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : C.gates.getD k aj_dflt ∈ C.gates := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem _

theorem aj_gate_ops (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
    ((C.gates.getD k aj_dflt).op = GateOp.and ∨ (C.gates.getD k aj_dflt).op = GateOp.or) ∧
    (C.gates.getD k aj_dflt).inputs.length ≤ 2 := by
  obtain ⟨h1, h2⟩ := hM _ (aj_gate_mem C k hk)
  refine ⟨?_, h2⟩
  simpa using h1

-- forward pass: wires of degree zero ignore the line inputs, and all wires are monotone in them
theorem aj_fwd (n m : ℕ) (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack (n + m) C)
    (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) :
    ((C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0 = 0 →
      aj_wv C (n + m) (Fin.append x y) w = aj_wv C (n + m) (Fin.append x (fun _ => false)) w) ∧
    (aj_wv C (n + m) (Fin.append x (fun _ => false)) w = true →
      aj_wv C (n + m) (Fin.append x y) w = true) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.lt_or_ge w (n + m) with h | h
    · rw [aj_wv_input _ _ _ _ h, aj_wv_input _ _ _ _ h, aj_deg_input _ _ _ _ h]
      rcases Nat.lt_or_ge w n with hw | hw
      · rw [aj_app_lt _ _ _ _ hw, aj_app_lt _ _ _ _ hw]
        exact ⟨fun _ => rfl, fun h => h⟩
      · rw [aj_app_ge _ (fun _ => false) _ _ hw]
        have : w ∈ Finset.Ico n (n + m) := by simp; omega
        simp [this]
    · rcases Nat.lt_or_ge (w - (n + m)) C.gates.length with hk | hk
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + m + k := ⟨w - (n + m), by omega⟩
        have hk' : k < C.gates.length := by omega
        have hu := aj_wv_gate C (n + m) (Fin.append x y) hR k hk'
        have hv := aj_wv_gate C (n + m) (Fin.append x (fun _ => false)) hR k hk'
        have hd := aj_deg_gate C (n + m) (Finset.Ico n (n + m)) hR k hk'
        have hr : ∀ i ∈ (C.gates.getD k aj_dflt).inputs, i < n + m + k := hR k hk'
        obtain ⟨hop, hl⟩ := aj_gate_ops C hM k hk'
        generalize C.gates.getD k aj_dflt = g at hu hv hd hr hop hl
        obtain ⟨op, l⟩ := g
        simp only at hop hl hr
        rw [hu, hv, hd]
        rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
        · rcases hop with rfl | rfl <;> simp [GateOp.eval]
        · obtain ⟨a1, a2⟩ := ih a (hr a (by simp))
          rcases hop with rfl | rfl
          · simp only [Gate.lineDegree, GateOp.eval]
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.all_cons,
              List.all_nil, id, Bool.and_true, ↓reduceIte, add_zero]
            exact ⟨a1, a2⟩
          · simp only [Gate.lineDegree, GateOp.eval]
            simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, List.any_cons,
              List.any_nil, id, Bool.or_false, reduceCtorEq, ↓reduceIte, Nat.max_zero]
            exact ⟨a1, a2⟩
        · obtain ⟨a1, a2⟩ := ih a (hr a (by simp))
          obtain ⟨b1, b2⟩ := ih b (hr b (by simp))
          rcases hop with rfl | rfl
          · simp only [Gate.lineDegree, GateOp.eval]
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.all_cons,
              List.all_nil, id, Bool.and_true, ↓reduceIte, add_zero]
            constructor
            · intro h0
              rw [a1 (by omega), b1 (by omega)]
            · intro hh
              simp only [Bool.and_eq_true] at hh ⊢
              exact ⟨a2 hh.1, b2 hh.2⟩
          · simp only [Gate.lineDegree, GateOp.eval]
            simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, List.any_cons,
              List.any_nil, id, Bool.or_false, reduceCtorEq, ↓reduceIte, Nat.max_zero]
            constructor
            · intro h0
              rw [a1 (by omega), b1 (by omega)]
            · intro hh
              simp only [Bool.or_eq_true] at hh ⊢
              exact hh.imp a2 b2
        · simp at hl
      · rw [aj_wv_ge _ _ _ _ (by omega), aj_wv_ge _ _ _ _ (by omega)]
        exact ⟨fun _ => rfl, fun h => h⟩

theorem aj_run_false (m : ℕ) (w : List Bool) :
    aj_run aj_evf (List.replicate m (Gate.mk GateOp.or [])) w = w ++ List.replicate m false := by
  induction m with
  | zero => simp [aj_run]
  | succ m ih =>
    rw [List.replicate_succ', aj_run_snoc, ih, List.replicate_succ', ← List.append_assoc]
    simp [aj_evf, GateOp.eval]

theorem aj_ofFn_app {n m : ℕ} (x : Fin n → Bool) :
    List.ofFn (Fin.append x (fun _ : Fin m => false)) = List.ofFn x ++ List.replicate m false := by
  rw [List.ofFn_fin_append, List.ofFn_const]

theorem aj_ncard_cnt (N s : ℕ) (deg : List ℕ) :
    Set.ncard {j : ℕ | j < s ∧ 0 < deg.getD (N + j) 0} = aj_cnt N deg s := by
  unfold aj_cnt
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp

theorem aj_gate_hyp (n m : ℕ) (C : Circuit) (hM : Monotone2 C) (hR : ReadsBack (n + m) C)
    (hX : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → (gateAt C j).inputs.length = 2 →
      ∃ i ∈ (gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) :
    aj_GateHyp (n + m) (C.lineDegrees (n + m) (Finset.Ico n (n + m))) C.gates := by
  intro k hk
  obtain ⟨h1, h2⟩ := aj_gate_ops C hM k hk
  exact ⟨h1, h2, hR k hk, hX k hk⟩

theorem aj_tinv_init (Dp : ℕ → Prop) (u v : ℕ → Bool) (r bound : ℕ) (A : ℕ → Bool)
    (hA : ∀ w, A w = decide (w = r)) (hx : ∀ w, ¬ Dp w → u w = v w)
    (hb : u r = true → r < bound) :
    aj_Tinv Dp u v (u r) (v r) bound A := by
  refine ⟨?_, ?_, ?_⟩
  · intro w _ _ ha hz
    rw [hA] at ha
    simp only [decide_eq_true_eq] at ha
    subst ha
    exact hz
  · intro w _ _ ha hz
    rw [hA] at ha
    simp only [decide_eq_true_eq] at ha
    subst ha
    exact hz
  · intro h
    by_cases hd : Dp r
    · right
      exact ⟨r, hb h, hd, by simp [hA], h⟩
    · left
      rw [← hx r hd]
      exact h

theorem aj_ld_zero (g : Gate) (d : List ℕ) (h : ∀ i ∈ g.inputs, d.getD i 0 = 0) : aj_ldf d g = 0 := by
  have key : ∀ l : List ℕ, (∀ i ∈ l, d.getD i 0 = 0) →
      (l.map fun i => d.getD i 0).sum = 0 ∧ (l.map fun i => d.getD i 0).foldr max 0 = 0 := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a l ih =>
      intro hl
      obtain ⟨i1, i2⟩ := ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      have ha := hl a (by simp)
      simp only [List.map_cons, List.sum_cons, List.foldr_cons]
      rw [i1, i2, ha]
      simp
  unfold aj_ldf Gate.lineDegree
  split_ifs
  · exact (key _ h).1
  · exact (key _ h).2

theorem aj_deg_zero (K : ℕ) (gs : List Gate) (w0 : List ℕ) (hK : w0.length = K)
    (h : ∀ g ∈ gs, ∀ i ∈ g.inputs, K ≤ i ∨ w0.getD i 0 = 0) :
    ∀ i, K ≤ i → (aj_run aj_ldf gs w0).getD i 0 = 0 := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    show w0.getD i 0 = 0
    exact aj_getD_ge _ _ _ (by omega)
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => h g' (List.mem_append_left _ hg'))
    intro i hi
    rw [aj_run_snoc]
    have hlen := aj_run_length aj_ldf gs w0
    rcases Nat.lt_trichotomy i (aj_run aj_ldf gs w0).length with hlt | heq | hgt
    · rw [aj_getD_app_lt _ _ _ _ hlt]
      exact ih' i hi
    · rw [heq, aj_getD_app_len]
      apply aj_ld_zero
      intro j hj
      rcases Nat.lt_or_ge j K with hjK | hjK
      · rw [aj_run_lt _ _ _ _ _ (by omega)]
        rcases h g (by simp) j hj with h1 | h1
        · omega
        · exact h1
      · exact ih' j hjK
    · exact aj_getD_ge _ _ _ (by simp only [List.length_append, List.length_singleton]; omega)

def aj_Syn (K : ℕ) (deg : List ℕ) (st : (ℕ → ℕ) × List Gate) : Prop :=
  (∀ w, K ≤ st.1 w) ∧ ∀ g ∈ st.2, ∀ i ∈ g.inputs, K ≤ i ∨ deg.getD i 0 = 0

theorem aj_link_syn (K B : ℕ) (deg : List ℕ) (st : (ℕ → ℕ) × List Gate) (a src : ℕ) (hKB : K ≤ B)
    (h : aj_Syn K deg st) (hs : K ≤ src) : aj_Syn K deg (aj_link B st a src) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro w
    simp only [aj_link, Function.update_apply]
    split_ifs
    · omega
    · exact h1 w
  · intro g hg i hi
    simp only [aj_link, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact h2 g hg i hi
    · rw [hg] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with e | e
      · left; rw [e]; exact h1 a
      · left; rw [e]; exact hs

theorem aj_fold_syn (K B : ℕ) (deg : List ℕ) (src : ℕ) (hKB : K ≤ B) (hs : K ≤ src) (l : List ℕ) :
    ∀ st : (ℕ → ℕ) × List Gate, aj_Syn K deg st →
      aj_Syn K deg (l.foldl (fun s a => aj_link B s a src) st) := by
  induction l with
  | nil => intro st h; exact h
  | cons a l ih =>
    intro st h
    rw [List.foldl_cons]
    exact ih _ (aj_link_syn K B deg st a src hKB h hs)

theorem aj_andl_syn (K B : ℕ) (deg : List ℕ) (st : (ℕ → ℕ) × List Gate) (W tgt side : ℕ)
    (hKB : K ≤ B) (h : aj_Syn K deg st) (hd : deg.getD side 0 = 0) :
    aj_Syn K deg (aj_andl B st W tgt side) := by
  unfold aj_andl
  obtain ⟨h1, h2⟩ := h
  apply aj_link_syn K B deg _ _ _ hKB _ (by omega)
  refine ⟨h1, ?_⟩
  intro g hg i hi
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | hg
  · exact h2 g hg i hi
  · rw [hg] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with e | e
    · left; rw [e]; exact h1 W
    · right; rw [e]; exact hd

theorem aj_proc_syn (K B : ℕ) (deg : List ℕ) (op : GateOp) (l : List ℕ) (W : ℕ)
    (st : (ℕ → ℕ) × List Gate) (hKB : K ≤ B)
    (hc : op = GateOp.and → l.length = 2 → ∃ i ∈ l, deg.getD i 0 = 0)
    (h : aj_Syn K deg st) : aj_Syn K deg (aj_proc B deg op l W st) := by
  unfold aj_proc
  by_cases hD : 0 < deg.getD W 0
  · rw [aj_ite_p _ _ _ hD]
    by_cases hA : aj_isAnd op = true ∧ l.length = 2
    · rw [aj_ite_p _ _ _ hA]
      have hop : op = GateOp.and := by
        obtain ⟨hA1, _⟩ := hA
        cases op <;> first | rfl | (simp [aj_isAnd] at hA1)
      obtain ⟨i, hi, hi0⟩ := hc hop hA.2
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hA.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      by_cases hda : 0 < deg.getD a 0
      · have e : (if 0 < deg.getD ([a, b].getD 0 0) 0
            then aj_andl B st W ([a, b].getD 0 0) ([a, b].getD 1 0)
            else aj_andl B st W ([a, b].getD 1 0) ([a, b].getD 0 0)) = aj_andl B st W a b :=
          aj_ite_p _ _ _ hda
        rw [e]
        apply aj_andl_syn K B deg st W a b hKB h
        rcases hi with e | e
        · rw [e] at hi0; omega
        · rw [e] at hi0; exact hi0
      · have e : (if 0 < deg.getD ([a, b].getD 0 0) 0
            then aj_andl B st W ([a, b].getD 0 0) ([a, b].getD 1 0)
            else aj_andl B st W ([a, b].getD 1 0) ([a, b].getD 0 0)) = aj_andl B st W b a :=
          aj_ite_n _ _ _ hda
        rw [e]
        apply aj_andl_syn K B deg st W b a hKB h
        omega
    · rw [aj_ite_n _ _ _ hA]
      exact aj_fold_syn K B deg (st.1 W) hKB (h.1 W) l st h
  · rw [aj_ite_n _ _ _ hD]
    exact h

theorem aj_iter_syn (K B N : ℕ) (deg : List ℕ) (gs : List Gate) (st0 : (ℕ → ℕ) × List Gate)
    (hKB : K ≤ B) (hgs : aj_GateHyp N deg gs) (h0 : aj_Syn K deg st0) :
    ∀ d ≤ gs.length, aj_Syn K deg (aj_stAt B N deg gs st0 d) := by
  intro d
  induction d with
  | zero => intro _; exact h0
  | succ d ih =>
    intro hd
    show aj_Syn K deg (aj_proc B deg _ _ _ (aj_stAt B N deg gs st0 d))
    exact aj_proc_syn K B deg _ _ _ _ hKB (hgs _ (by omega)).2.2.2 (ih (by omega))

theorem aj_deg_app (n m : ℕ) (G A : List Gate)
    (hA : ∀ g ∈ A, ∀ i ∈ g.inputs, n + m + G.length ≤ i ∨
      ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) :
    ∀ i, n + m + G.length ≤ i →
      ((Circuit.mk (G ++ A) 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0 := by
  intro i hi
  rw [aj_deg_run]
  show (aj_run aj_ldf (G ++ A) _).getD i 0 = 0
  rw [aj_run_append]
  exact aj_deg_zero _ A _ (by show (aj_run aj_ldf G _).length = _; rw [aj_run_length]; simp) hA i hi

theorem aj_snoc_val (w : List Bool) (K : ℕ) (hK : w.length = K) (b : Bool) :
    (w ++ [b]).getD K false = b := by
  subst hK
  exact aj_getD_app_len _ _ _

theorem aj_single (n m : ℕ) (G : List Gate) (g : Gate) (hg : g.inputs = [])
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (∀ g' ∈ [g], g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
    (∀ k < [g].length, ∀ i ∈ ([g].getD k (Gate.mk GateOp.or [])).inputs, i < n + m + G.length + k) ∧
    (∀ k < [g].length,
      ((Circuit.mk (G ++ [g]) 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD
        (n + m + G.length + k) 0 = 0) ∧
    (n + m + G.length < n + m + G.length + [g].length ∧
      ((Circuit.mk (G ++ [g]) 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD
        (n + m + G.length) 0 = 0) ∧
    ∀ (z : Fin (n + m) → Bool), ((Circuit.mk (G ++ [g]) 0).wires (List.ofFn z)).getD
      (n + m + G.length) false = g.op.eval [] := by
  have hd := aj_deg_app n m G [g] (by
    intro g' hg' i hi
    simp only [List.mem_singleton] at hg'
    rw [hg', hg] at hi
    simp at hi)
  refine ⟨?_, ?_, ?_, ⟨by simp, hd _ (le_refl _)⟩, ?_⟩
  · intro g' hg'
    simp only [List.mem_singleton] at hg'
    rw [hg', hg]
    refine ⟨?_, by simp⟩
    rcases hop with h | h <;> simp [h]
  · exact aj_RBL_empty _ _ (by
      intro g' hg'
      simp only [List.mem_singleton] at hg'
      rw [hg', hg])
  · intro k _
    exact hd _ (by omega)
  · intro z
    rw [aj_wires_run]
    show (aj_run aj_evf (G ++ [g]) _).getD _ _ = _
    rw [aj_run_snoc]
    have e : aj_evf (aj_run aj_evf G (List.ofFn z)) g = g.op.eval [] := by
      unfold aj_evf
      rw [hg]
      rfl
    rw [e]
    exact aj_snoc_val _ _ (by rw [aj_run_length]; simp) _

def AdjointSpec (n m : ℕ) (G : List Gate) (r : ℕ) : Prop :=
  Monotone2 (Circuit.mk G 0) →
  ReadsBack (n + m) (Circuit.mk G 0) →
  (∀ j < G.length, (gateAt (Circuit.mk G 0) j).op = GateOp.and →
    (gateAt (Circuit.mk G 0) j).inputs.length = 2 →
    ∃ i ∈ (gateAt (Circuit.mk G 0) j).inputs,
      ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) →
  r < n + m + G.length →
  ∃ (A : List Gate) (o : Fin m → ℕ),
    (∀ g ∈ A, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
    (∀ k < A.length, ∀ i ∈ (A.getD k (Gate.mk GateOp.or [])).inputs, i < n + m + G.length + k) ∧
    A.length ≤ 3 * Set.ncard {j : ℕ | j < G.length ∧
      0 < ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} + m ∧
    (∀ k < A.length,
      ((Circuit.mk (G ++ A) 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD
        (n + m + G.length + k) 0 = 0) ∧
    (∀ j : Fin m, o j < n + m + G.length + A.length ∧
      ((Circuit.mk (G ++ A) 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD (o j) 0 = 0) ∧
    ∀ (x : Fin n → Bool) (y : Fin m → Bool) (j : Fin m),
      ((Circuit.mk G 0).wires (List.ofFn (Fin.append x (fun l => decide (l = j))))).getD r false =
        (((Circuit.mk G 0).wires (List.ofFn (Fin.append x (fun _ : Fin m => false)))).getD r false ||
         ((Circuit.mk (G ++ A) 0).wires (List.ofFn (Fin.append x y))).getD (o j) false)

theorem aj_adjoint (n m : ℕ) (G : List Gate) (r : ℕ) : AdjointSpec n m G r := by
  intro hM hR hX hr
  have hF := fun (x : Fin n → Bool) (y : Fin m → Bool) (w : ℕ) =>
    aj_fwd n m (Circuit.mk G 0) hM hR x y w
  rw [aj_ncard_cnt]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨[], fun j => j.elim0, by simp, by simp, by simp, by simp, fun j => j.elim0,
      fun x y j => j.elim0⟩
  by_cases hout : 0 < ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD r 0
  · by_cases hbig : 2 ≤ aj_cnt (n + m) ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m)))
        G.length + m
    · -- the reverse pass, after a true and a false constant
      have hgs : aj_GateHyp (n + m) ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))) G :=
        aj_gate_hyp n m (Circuit.mk G 0) hM hR hX
      have hg0 : aj_Good (n + m + G.length + 2)
          ((fun w => if w = r then n + m + G.length else n + m + G.length + 1),
            ([] : List Gate)) := by
        refine ⟨?_, ?_, ?_⟩
        · intro w
          simp only [List.length_nil]
          split_ifs <;> omega
        · intro g hg
          simp at hg
        · intro j hj
          simp at hj
      have hs0 : aj_Syn (n + m + G.length)
          ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m)))
          ((fun w => if w = r then n + m + G.length else n + m + G.length + 1),
            ([] : List Gate)) := by
        refine ⟨?_, ?_⟩
        · intro w
          show n + m + G.length ≤ (if w = r then n + m + G.length else n + m + G.length + 1)
          split_ifs <;> omega
        · intro g hg
          simp at hg
      obtain ⟨q1, q2⟩ := aj_iter_good (n + m + G.length + 2) (n + m)
        ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))) G _ (by omega) hgs hg0
        G.length (le_refl _)
      have q3 := aj_iter_syn (n + m + G.length) (n + m + G.length + 2) (n + m)
        ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))) G _ (by omega) hgs hs0
        G.length (le_refl _)
      obtain ⟨st, hst⟩ : ∃ st, st = aj_stAt (n + m + G.length + 2) (n + m)
        ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))) G
        ((fun w => if w = r then n + m + G.length else n + m + G.length + 1), ([] : List Gate))
        G.length := ⟨_, rfl⟩
      rw [← hst] at q1 q2 q3
      obtain ⟨q11, q12, q13⟩ := q1
      obtain ⟨q31, q32⟩ := q3
      have hsyn : ∀ g ∈ [Gate.mk GateOp.and [], Gate.mk GateOp.or []] ++ st.2, ∀ i ∈ g.inputs,
          n + m + G.length ≤ i ∨
          ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0 := by
        intro g hg i hi
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with (hg | hg) | hg
        · rw [hg] at hi; simp at hi
        · rw [hg] at hi; simp at hi
        · exact q32 g hg i hi
      have hd := aj_deg_app n m G _ hsyn
      refine ⟨[Gate.mk GateOp.and [], Gate.mk GateOp.or []] ++ st.2,
        fun j => st.1 (n + j.val), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with (hg | hg) | hg
        · rw [hg]; simp
        · rw [hg]; simp
        · obtain ⟨h1, h2⟩ := q12 g hg
          refine ⟨?_, h2⟩
          rcases h1 with h1 | h1 <;> simp [h1]
      · show aj_RBL (n + m + G.length) _
        apply aj_RBL_append
        · exact aj_RBL_empty _ _ (by
            intro g hg
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
            rcases hg with hg | hg <;> rw [hg])
        · exact q13
      · simp only [List.length_append, List.length_cons, List.length_nil]
        simp only [List.length_nil] at q2
        omega
      · intro k _
        exact hd _ (by omega)
      · intro j
        refine ⟨?_, hd _ (q31 _)⟩
        have := q11 (n + j.val)
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · intro x y j
        obtain ⟨base, hbase⟩ : ∃ base, base =
          (Circuit.mk G 0).wires (List.ofFn (Fin.append x y)) ++ [true, false] := ⟨_, rfl⟩
        have hvl : ((Circuit.mk G 0).wires (List.ofFn (Fin.append x y))).length
            = n + m + G.length := by
          rw [aj_wires_run, aj_run_length]
          simp
        have hBl : base.length = n + m + G.length + 2 := by
          rw [hbase, List.length_append, hvl]
          rfl
        have hw : (Circuit.mk (G ++ ([Gate.mk GateOp.and [], Gate.mk GateOp.or []] ++ st.2)) 0).wires
            (List.ofFn (Fin.append x y)) = aj_run aj_evf st.2 base := by
          rw [aj_wires_run]
          show aj_run aj_evf (G ++ ([Gate.mk GateOp.and [], Gate.mk GateOp.or []] ++ st.2)) _ = _
          rw [aj_run_append, aj_run_append, hbase, aj_wires_run]
          congr 1
          show aj_run aj_evf [Gate.mk GateOp.and [], Gate.mk GateOp.or []] (aj_run aj_evf G _) =
            aj_run aj_evf G _ ++ [true, false]
          simp [aj_run, aj_evf, GateOp.eval]
        rw [hw]
        have hv : ∀ i < n + m + G.length,
            ¬ 0 < ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 →
            base.getD i false = aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun _ => false)) i := by
          intro i hi hi0
          rw [hbase, aj_getD_app_lt _ _ _ _ (by omega)]
          exact (hF x y i).1 (by omega)
        have hT : base.getD (n + m + G.length) false = true := by
          rw [hbase, List.getD_append_right _ _ _ _ (by omega), hvl, Nat.sub_self]
          rfl
        have hFl : base.getD (n + m + G.length + 1) false = false := by
          rw [hbase, List.getD_append_right _ _ _ _ (by omega), hvl, Nat.add_sub_cancel_left]
          rfl
        have hx : ∀ w, ¬ 0 < ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0 →
            aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun l => decide (l = j))) w
              = aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun _ => false)) w := by
          intro w hw0
          exact (hF x _ w).1 (by omega)
        have hI0 := aj_tinv_init
          (fun w => 0 < ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD w 0)
          (aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun l => decide (l = j))))
          (aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun _ => false))) r (n + m + G.length)
          (aj_aval base ((fun w => if w = r then n + m + G.length else n + m + G.length + 1),
            ([] : List Gate)))
          (by
            intro w
            unfold aj_aval
            show (base).getD (if w = r then n + m + G.length else n + m + G.length + 1) false = _
            by_cases hwo : w = r
            · rw [aj_ite_p _ _ _ hwo, hT]; simp [hwo]
            · rw [aj_ite_n _ _ _ hwo, hFl]; simp [hwo])
          hx (fun _ => hr)
        have hfin := aj_iter_inv (n + m + G.length + 2) (n + m)
          ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))) G _ base _ _ _ _ hBl
          (by omega) hgs hg0 hv
          (fun k hk => aj_wv_gate (Circuit.mk G 0) (n + m) _ hR k hk)
          (fun k hk => aj_wv_gate (Circuit.mk G 0) (n + m) _ hR k hk)
          hx hI0 G.length (le_refl _)
        rw [← hst] at hfin
        obtain ⟨f1, _, f3⟩ := hfin
        have hjlt : n + j.val < n + m := by have := j.isLt; omega
        have hdj : 0 < ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m))).getD
            (n + j.val) 0 := by
          rw [aj_deg_input _ _ _ _ hjlt]
          have : n + j.val ∈ Finset.Ico n (n + m) := by simp
          simp [this]
        have huj : aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun l => decide (l = j)))
            (n + j.val) = true := by
          rw [aj_wv_input _ _ _ _ hjlt, aj_app_ge _ _ _ _ (by omega)]
          simp only [decide_eq_true_eq]
          ext
          simp
        show aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun l => decide (l = j))) r =
          (aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun _ => false)) r ||
            aj_aval base st (n + j.val))
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true]
        constructor
        · intro huo
          rcases f3 huo with h | ⟨w, hw, hd, ha, hz⟩
          · left; exact h
          · right
            have hwN : w < n + m := by omega
            have hwn : n ≤ w := by
              by_contra hcon
              have hd' : 0 < ((Circuit.mk G 0).lineDegrees (n + m)
                (Finset.Ico n (n + m))).getD w 0 := hd
              rw [aj_deg_input _ _ _ _ hwN] at hd'
              have : w ∉ Finset.Ico n (n + m) := by simp; omega
              simp [this] at hd'
            rw [aj_wv_input _ _ _ _ hwN, aj_app_ge _ _ _ _ hwn] at hz
            simp only [decide_eq_true_eq] at hz
            have e : w = n + j.val := by
              rw [← hz]
              simp only
              omega
            rw [← e]
            exact ha
        · rintro (h | h)
          · exact (hF x _ r).2 h
          · exact f1 (n + j.val) (by omega) hdj h huj
    · -- one line and no line-dependent gate: the target is the line input
      have hrN : r < n + m := by
        by_contra hcon
        apply hbig
        have : 1 ≤ aj_cnt (n + m) ((Circuit.mk G 0).lineDegrees (n + m) (Finset.Ico n (n + m)))
            G.length := by
          unfold aj_cnt
          apply Finset.card_pos.mpr
          refine ⟨r - (n + m), ?_⟩
          simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, ?_⟩
          have e : n + m + (r - (n + m)) = r := by omega
          rw [e]
          exact hout
        omega
      have hn : n ≤ r := by
        by_contra hcon
        have : r ∉ Finset.Ico n (n + m) := by simp; omega
        rw [aj_deg_input _ _ _ _ hrN] at hout
        simp [this] at hout
      obtain ⟨s1, s2, s3, s4, s5⟩ := aj_single n m G (Gate.mk GateOp.and []) rfl (Or.inl rfl)
      refine ⟨[Gate.mk GateOp.and []], fun _ => n + m + G.length, s1, s2, ?_, s3,
        fun _ => s4, ?_⟩
      · simp only [List.length_singleton]
        omega
      · intro x y j
        rw [s5]
        show aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun l => decide (l = j))) r =
          (aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun _ => false)) r || _)
        rw [aj_wv_input _ _ _ _ hrN, aj_wv_input _ _ _ _ hrN, aj_app_ge _ _ _ _ hn, aj_app_ge _ _ _ _ hn]
        have e1 : (⟨r - n, by omega⟩ : Fin m) = j := by
          ext
          have := j.isLt
          simp only
          omega
        simp [e1, GateOp.eval]
  · obtain ⟨s1, s2, s3, s4, s5⟩ := aj_single n m G (Gate.mk GateOp.or []) rfl (Or.inr rfl)
    refine ⟨[Gate.mk GateOp.or []], fun _ => n + m + G.length, s1, s2, ?_, s3,
      fun _ => s4, ?_⟩
    · simp only [List.length_singleton]
      omega
    · intro x y j
      rw [s5]
      show aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun l => decide (l = j))) r =
        (aj_wv (Circuit.mk G 0) (n + m) (Fin.append x (fun _ => false)) r || _)
      rw [(hF x _ r).1 (by omega)]
      simp [GateOp.eval]


def dflt : Gate := Gate.mk GateOp.or []

def W (G : List Gate) (x : List Bool) : List Bool :=
  G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def val (G : List Gate) (x : List Bool) (i : ℕ) : Bool := (W G x).getD i false

def d0 (n m : ℕ) : List ℕ :=
  (List.range (n + m)).map fun i => if i ∈ Finset.Ico n (n + m) then 1 else 0

def Dg (G : List Gate) (d : List ℕ) : List ℕ :=
  G.foldl (fun d g => d ++ [g.lineDegree d]) d

def dg (n m : ℕ) (G : List Gate) (i : ℕ) : ℕ := (Dg G (d0 n m)).getD i 0

def RB (N : ℕ) (G : List Gate) : Prop :=
  ∀ j < G.length, ∀ i ∈ (G.getD j dflt).inputs, i < N + j

def Mono (G : List Gate) : Prop :=
  ∀ g ∈ G, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def NC (n m : ℕ) (G : List Gate) : Prop :=
  ∀ j < G.length, (G.getD j dflt).op = GateOp.and → (G.getD j dflt).inputs.length = 2 →
    ∃ i ∈ (G.getD j dflt).inputs, dg n m G i = 0

theorem W_snoc (G : List Gate) (g : Gate) (x : List Bool) :
    W (G ++ [g]) x = W G x ++ [g.op.eval (g.inputs.map (val G x))] := by
  unfold W
  rw [List.foldl_append]
  rfl

theorem W_length (G : List Gate) (x : List Bool) : (W G x).length = x.length + G.length := by
  induction G using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton G g ih => rw [W_snoc]; simp [ih]; omega

theorem val_prefix (G A : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + G.length) :
    val (G ++ A) x i = val G x i := by
  induction A using List.reverseRecOn with
  | nil => simp
  | append_singleton A a ih =>
    rw [← List.append_assoc]
    unfold val at *
    rw [W_snoc, List.getD_append _ _ _ _ (by rw [W_length]; simp; omega)]
    exact ih

theorem val_input (G : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    val G x i = x.getD i false := by
  have := val_prefix [] G x i (by simpa using hi)
  simpa [val, W] using this

theorem val_new (G : List Gate) (g : Gate) (x : List Bool) :
    val (G ++ [g]) x (x.length + G.length) = g.op.eval (g.inputs.map (val G x)) := by
  unfold val
  rw [W_snoc, List.getD_append_right _ _ _ _ (by rw [W_length])]
  simp [W_length]
  rfl

theorem RB_of_snoc (N : ℕ) (G : List Gate) (g : Gate) (h : RB N (G ++ [g])) : RB N G := by
  intro j hj i hi
  have := h j (by simp; omega) i
  rw [List.getD_append _ _ _ _ hj] at this
  exact this hi

theorem getD_app (G A : List Gate) (k : ℕ) :
    (G ++ A).getD (G.length + k) dflt = A.getD k dflt := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem val_gate (G : List Gate) (x : List Bool) (j : ℕ) (hrb : RB x.length G)
    (hj : j < G.length) :
    val G x (x.length + j) =
      (G.getD j dflt).op.eval ((G.getD j dflt).inputs.map (val G x)) := by
  induction G using List.reverseRecOn with
  | nil => simp at hj
  | append_singleton G g ih =>
    by_cases hlt : j < G.length
    · rw [val_prefix _ _ _ _ (by omega), ih (RB_of_snoc _ _ _ hrb) hlt,
        List.getD_append _ _ _ _ hlt]
      congr 1
      apply List.map_congr_left
      intro i hi
      have := hrb j hj i (by rw [List.getD_append _ _ _ _ hlt]; exact hi)
      exact (val_prefix _ _ _ _ (by omega)).symm
    · have hje : j = G.length := by simp at hj; omega
      subst hje
      have hg : (G ++ [g]).getD G.length dflt = g := by
        simp
      rw [val_new, hg]
      congr 1
      apply List.map_congr_left
      intro i hi
      have := hrb G.length hj i (by rw [hg]; exact hi)
      exact (val_prefix _ _ _ _ (by omega)).symm

theorem Dg_snoc (G : List Gate) (g : Gate) (d : List ℕ) :
    Dg (G ++ [g]) d = Dg G d ++ [g.lineDegree (Dg G d)] := by
  simp [Dg, List.foldl_append]

theorem Dg_length (G : List Gate) (d : List ℕ) : (Dg G d).length = d.length + G.length := by
  induction G using List.reverseRecOn with
  | nil => simp [Dg]
  | append_singleton G g ih => rw [Dg_snoc]; simp [ih]; omega

theorem d0_length (n m : ℕ) : (d0 n m).length = n + m := by simp [d0]

theorem dg_prefix (n m : ℕ) (G A : List Gate) (i : ℕ) (hi : i < n + m + G.length) :
    dg n m (G ++ A) i = dg n m G i := by
  induction A using List.reverseRecOn with
  | nil => simp
  | append_singleton A a ih =>
    rw [← List.append_assoc]
    unfold dg at *
    rw [Dg_snoc, List.getD_append _ _ _ _ (by rw [Dg_length, d0_length]; simp; omega)]
    exact ih

theorem dg_input (n m : ℕ) (G : List Gate) (i : ℕ) (hi : i < n + m) :
    dg n m G i = if n ≤ i then 1 else 0 := by
  have := dg_prefix n m [] G i (by simpa using hi)
  simp only [List.nil_append] at this
  rw [this]
  simp [dg, Dg, d0, hi]

theorem lineDegree_congr (g : Gate) (d d' : List ℕ)
    (h : ∀ i ∈ g.inputs, d.getD i 0 = d'.getD i 0) : g.lineDegree d = g.lineDegree d' := by
  have : g.inputs.map (fun i => d.getD i 0) = g.inputs.map (fun i => d'.getD i 0) :=
    List.map_congr_left h
  unfold Gate.lineDegree
  rw [this]

theorem dg_new (n m : ℕ) (G : List Gate) (g : Gate) :
    dg n m (G ++ [g]) (n + m + G.length) = g.lineDegree (Dg G (d0 n m)) := by
  unfold dg
  rw [Dg_snoc, List.getD_append_right _ _ _ _ (by rw [Dg_length, d0_length])]
  simp [Dg_length, d0_length]

theorem dg_gate (n m : ℕ) (G : List Gate) (j : ℕ) (hrb : RB (n + m) G) (hj : j < G.length) :
    dg n m G (n + m + j) = (G.getD j dflt).lineDegree (Dg G (d0 n m)) := by
  induction G using List.reverseRecOn with
  | nil => simp at hj
  | append_singleton G g ih =>
    by_cases hlt : j < G.length
    · rw [dg_prefix _ _ _ _ _ (by omega), ih (RB_of_snoc _ _ _ hrb) hlt,
        List.getD_append _ _ _ _ hlt]
      apply lineDegree_congr
      intro i hi
      have := hrb j hj i (by rw [List.getD_append _ _ _ _ hlt]; exact hi)
      exact (dg_prefix n m G [g] i (by omega)).symm
    · have hje : j = G.length := by simp at hj; omega
      subst hje
      have hg : (G ++ [g]).getD G.length dflt = g := by
        simp
      rw [dg_new, hg]
      apply lineDegree_congr
      intro i hi
      have := hrb G.length hj i (by rw [hg]; exact hi)
      exact (dg_prefix n m G [g] i (by omega)).symm

theorem lineDegree_and (g : Gate) (d : List ℕ) (h : g.op = GateOp.and) :
    g.lineDegree d = (g.inputs.map fun i => d.getD i 0).sum := by
  unfold Gate.lineDegree
  simp [h]

theorem lineDegree_or (g : Gate) (d : List ℕ) (h : g.op = GateOp.or) :
    g.lineDegree d = (g.inputs.map fun i => d.getD i 0).foldr max 0 := by
  unfold Gate.lineDegree
  simp [h]


def xy {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) : List Bool := List.ofFn (Fin.append x y)

theorem xy_length {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) : (xy x y).length = n + m := by
  simp [xy]

theorem xy_left {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (i : ℕ) (hi : i < n) :
    (xy x y).getD i false = x ⟨i, hi⟩ := by
  unfold xy
  have hl : i < (List.ofFn (Fin.append x y)).length := by simp; omega
  rw [List.getD_eq_getElem _ _ hl, List.getElem_ofFn]
  exact Fin.append_left x y ⟨i, hi⟩

theorem xy_right {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (l : Fin m) :
    (xy x y).getD (n + l) false = y l := by
  unfold xy
  have hl : n + (l : ℕ) < (List.ofFn (Fin.append x y)).length := by simp
  rw [List.getD_eq_getElem _ _ hl, List.getElem_ofFn]
  exact Fin.append_right x y l

theorem val_x {n m : ℕ} (G : List Gate) (x : Fin n → Bool) (y : Fin m → Bool) (i : ℕ)
    (hi : i < n) : val G (xy x y) i = x ⟨i, hi⟩ := by
  rw [val_input _ _ _ (by rw [xy_length]; omega), xy_left]

theorem val_y {n m : ℕ} (G : List Gate) (x : Fin n → Bool) (y : Fin m → Bool) (l : Fin m) :
    val G (xy x y) (n + l) = y l := by
  rw [val_input _ _ _ (by rw [xy_length]; omega), xy_right]

theorem val_out (G : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + G.length ≤ i) :
    val G x i = false := by
  unfold val
  exact List.getD_eq_default _ _ (by rw [W_length]; exact hi)

theorem val_g {n m : ℕ} (G : List Gate) (x : Fin n → Bool) (y : Fin m → Bool) (j : ℕ)
    (hrb : RB (n + m) G) (hj : j < G.length) :
    val G (xy x y) (n + m + j) =
      (G.getD j dflt).op.eval ((G.getD j dflt).inputs.map (val G (xy x y))) := by
  have := val_gate G (xy x y) j (by rw [xy_length]; exact hrb) hj
  rw [xy_length] at this
  exact this

theorem dg_out (n m : ℕ) (G : List Gate) (i : ℕ) (hi : n + m + G.length ≤ i) :
    dg n m G i = 0 := by
  unfold dg
  exact List.getD_eq_default _ _ (by rw [Dg_length, d0_length]; exact hi)

theorem shape (l : List ℕ) (h : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
  match l, h with
  | [], _ => exact Or.inl rfl
  | [a], _ => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | [a, b], _ => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
  | _ :: _ :: _ :: _, h => simp at h

theorem getD_mem (G : List Gate) (j : ℕ) (hj : j < G.length) : G.getD j dflt ∈ G := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem opcase (G : List Gate) (hm : Mono G) (j : ℕ) (hj : j < G.length) :
    ((G.getD j dflt).op = GateOp.and ∨ (G.getD j dflt).op = GateOp.or) ∧
      (G.getD j dflt).inputs.length ≤ 2 := by
  have := hm _ (getD_mem G j hj)
  refine ⟨?_, this.2⟩
  have h1 := this.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact h1

theorem le_foldr_max (l : List ℕ) (a : ℕ) (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem lineDegree_zero (g : Gate) (d : List ℕ) (h : g.lineDegree d = 0) :
    ∀ a ∈ g.inputs, d.getD a 0 = 0 := by
  intro a ha
  have hmem : d.getD a 0 ∈ g.inputs.map (fun i => d.getD i 0) := List.mem_map.mpr ⟨a, ha, rfl⟩
  unfold Gate.lineDegree at h
  split_ifs at h
  · exact List.sum_eq_zero_iff.mp h _ hmem
  · have := le_foldr_max _ _ hmem
    omega

theorem indep (n m : ℕ) (G : List Gate) (hrb : RB (n + m) G) (x : Fin n → Bool)
    (y y' : Fin m → Bool) :
    ∀ i, dg n m G i = 0 → val G (xy x y) i = val G (xy x y') i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hd
    by_cases h1 : i < n
    · rw [val_x _ _ _ _ h1, val_x _ _ _ _ h1]
    by_cases h2 : i < n + m
    · rw [dg_input _ _ _ _ h2] at hd
      simp [show n ≤ i by omega] at hd
    by_cases h3 : i < n + m + G.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + m + j := ⟨i - (n + m), by omega⟩
      have hj : j < G.length := by omega
      rw [val_g G x y j hrb hj, val_g G x y' j hrb hj]
      congr 1
      apply List.map_congr_left
      intro a ha
      have ha' := hrb j hj a ha
      apply ih a (by omega)
      rw [dg_gate n m G j hrb hj] at hd
      exact lineDegree_zero _ _ hd a ha
    · rw [val_out _ _ _ (by rw [xy_length]; omega), val_out _ _ _ (by rw [xy_length]; omega)]

theorem ex_or {m : ℕ} (Y : Finset (Fin m)) (f g : Fin m → Bool) :
    decide (∃ j ∈ Y, (f j || g j) = true) =
      (decide (∃ j ∈ Y, f j = true) || decide (∃ j ∈ Y, g j = true)) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨j, hj, h | h⟩
    · exact Or.inl ⟨j, hj, h⟩
    · exact Or.inr ⟨j, hj, h⟩
  · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩)
    · exact ⟨j, hj, Or.inl h⟩
    · exact ⟨j, hj, Or.inr h⟩

theorem ex_and {m : ℕ} (Y : Finset (Fin m)) (c : Bool) (g : Fin m → Bool) :
    decide (∃ j ∈ Y, (c && g j) = true) = (c && decide (∃ j ∈ Y, g j = true)) := by
  cases c <;> simp

theorem ex_and' {m : ℕ} (Y : Finset (Fin m)) (c : Bool) (g : Fin m → Bool) :
    decide (∃ j ∈ Y, (g j && c) = true) = (decide (∃ j ∈ Y, g j = true) && c) := by
  cases c <;> simp

theorem and_lin {m : ℕ} (Y : Finset (Fin m)) (c bY b0 : Bool) (bj : Fin m → Bool)
    (h : bY = (b0 || decide (∃ j ∈ Y, bj j = true))) :
    (c && bY) = ((c && b0) || decide (∃ j ∈ Y, (c && bj j) = true)) := by
  rw [ex_and, h]
  cases c <;> simp

theorem and_lin' {m : ℕ} (Y : Finset (Fin m)) (c bY b0 : Bool) (bj : Fin m → Bool)
    (h : bY = (b0 || decide (∃ j ∈ Y, bj j = true))) :
    (bY && c) = ((b0 && c) || decide (∃ j ∈ Y, (bj j && c) = true)) := by
  rw [ex_and', h]
  cases c <;> simp

theorem or_lin {m : ℕ} (Y : Finset (Fin m)) (fY f0 : ℕ → Bool) (fj : Fin m → ℕ → Bool)
    (l : List ℕ)
    (h : ∀ a ∈ l, fY a = (f0 a || decide (∃ j ∈ Y, fj j a = true))) :
    (l.map fY).any id =
      ((l.map f0).any id || decide (∃ j ∈ Y, (l.map (fj j)).any id = true)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id_eq]
    rw [ih (fun b hb => h b (List.mem_cons_of_mem _ hb)), h a List.mem_cons_self, ex_or]
    generalize decide (∃ j ∈ Y, fj j a = true) = p
    generalize decide (∃ j ∈ Y, (List.map (fj j) l).any id = true) = q
    cases f0 a <;> cases p <;> cases q <;> simp

theorem linear (n m : ℕ) (G : List Gate) (hm : Mono G) (hrb : RB (n + m) G) (hnc : NC n m G)
    (x : Fin n → Bool) (Y : Finset (Fin m)) :
    ∀ i, val G (xy x (fun l => decide (l ∈ Y))) i =
      (val G (xy x (fun _ : Fin m => false)) i ||
        decide (∃ j ∈ Y, val G (xy x (fun l => decide (l = j))) i = true)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h1 : i < n
    · simp only [val_x _ _ _ _ h1]
      cases x ⟨i, h1⟩ <;> simp
    by_cases h2 : i < n + m
    · obtain ⟨l, rfl⟩ : ∃ l : Fin m, i = n + (l : ℕ) := ⟨⟨i - n, by omega⟩, by simp; omega⟩
      simp only [val_y]
      simp
    by_cases h3 : i < n + m + G.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + m + j := ⟨i - (n + m), by omega⟩
      have hj : j < G.length := by omega
      have e : ∀ y : Fin m → Bool, val G (xy x y) (n + m + j) =
          (G.getD j dflt).op.eval ((G.getD j dflt).inputs.map (val G (xy x y))) :=
        fun y => val_g G x y j hrb hj
      simp only [e]
      have hr := hrb j hj
      have hc := hnc j hj
      obtain ⟨ho, hlen⟩ := opcase G hm j hj
      generalize G.getD j dflt = g at hr hc ho hlen ⊢
      rcases ho with ho | ho
      · rcases shape _ hlen with h | ⟨a, h⟩ | ⟨a, b, h⟩
        · simp [ho, h, GateOp.eval]
        · simp only [ho, h, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, Bool.and_true, id_eq]
          exact ih a (hr a (by simp [h]))
        · simp only [ho, h, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, Bool.and_true, id_eq]
          have ha := hr a (by simp [h])
          have hb := hr b (by simp [h])
          obtain ⟨i, hi, hz⟩ := hc ho (by simp [h])
          rw [h] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · obtain ⟨c, hc0⟩ : ∃ c, val G (xy x (fun _ : Fin m => false)) i = c := ⟨_, rfl⟩
            have hcY : val G (xy x (fun l => decide (l ∈ Y))) i = c := by
              rw [← hc0]; exact indep n m G hrb x _ _ i hz
            have hcj : ∀ j : Fin m, val G (xy x (fun l => decide (l = j))) i = c := by
              intro j; rw [← hc0]; exact indep n m G hrb x _ _ i hz
            simp only [hc0, hcY, hcj]
            exact and_lin Y c _ _ _ (ih b hb)
          · obtain ⟨c, hc0⟩ : ∃ c, val G (xy x (fun _ : Fin m => false)) i = c := ⟨_, rfl⟩
            have hcY : val G (xy x (fun l => decide (l ∈ Y))) i = c := by
              rw [← hc0]; exact indep n m G hrb x _ _ i hz
            have hcj : ∀ j : Fin m, val G (xy x (fun l => decide (l = j))) i = c := by
              intro j; rw [← hc0]; exact indep n m G hrb x _ _ i hz
            simp only [hc0, hcY, hcj]
            exact and_lin' Y c _ _ _ (ih a ha)
      · simp only [ho, GateOp.eval]
        exact or_lin Y _ _ _ g.inputs (fun a ha => ih a (hr a ha))
    · have hv : ∀ y : Fin m → Bool, val G (xy x y) i = false :=
        fun y => val_out _ _ _ (by rw [xy_length]; omega)
      simp only [hv]
      simp

def cnt (n m : ℕ) (G : List Gate) : ℕ :=
  ((Dg G (d0 n m)).drop (n + m)).countP (fun a => decide (0 < a))

theorem cnt_snoc (n m : ℕ) (G : List Gate) (g : Gate) :
    cnt n m (G ++ [g]) =
      cnt n m G + (if 0 < dg n m (G ++ [g]) (n + m + G.length) then 1 else 0) := by
  rw [dg_new]
  unfold cnt
  rw [Dg_snoc, List.drop_append_of_le_length (by rw [Dg_length, d0_length]; omega),
    List.countP_append]
  simp [List.countP_cons]

theorem cnt_snoc_le (n m : ℕ) (G : List Gate) (g : Gate) :
    cnt n m (G ++ [g]) ≤ cnt n m G + 1 := by
  rw [cnt_snoc]
  split_ifs <;> omega

theorem cnt_append_le (n m : ℕ) (G A : List Gate) :
    cnt n m (G ++ A) ≤ cnt n m G + A.length := by
  induction A using List.reverseRecOn with
  | nil => simp
  | append_singleton A a ih =>
    rw [← List.append_assoc]
    have := cnt_snoc_le n m (G ++ A) a
    simp only [List.length_append, List.length_singleton]
    omega

theorem cnt_append_zero (n m : ℕ) (G A : List Gate)
    (h : ∀ k < A.length, dg n m (G ++ A) (n + m + G.length + k) = 0) :
    cnt n m (G ++ A) = cnt n m G := by
  induction A using List.reverseRecOn with
  | nil => simp
  | append_singleton A a ih =>
    have h1 : cnt n m (G ++ A) = cnt n m G := by
      apply ih
      intro k hk
      have := h k (by simp; omega)
      rw [← List.append_assoc, dg_prefix _ _ _ _ _ (by simp; omega)] at this
      exact this
    have h2 := h A.length (by simp)
    rw [← List.append_assoc] at h2 ⊢
    rw [cnt_snoc, h1]
    have e : n + m + (G ++ A).length = n + m + G.length + A.length := by simp; omega
    rw [e, h2]
    simp

theorem ncard_le_cnt (n m : ℕ) (G : List Gate) :
    Set.ncard {j : ℕ | j < G.length ∧ 0 < dg n m G (n + m + j)} ≤ cnt n m G := by
  induction G using List.reverseRecOn with
  | nil => simp
  | append_singleton G g ih =>
    have hfin : Set.Finite {j : ℕ | j < G.length ∧ 0 < dg n m G (n + m + j)} :=
      (Set.finite_Iio G.length).subset (fun j hj => hj.1)
    rw [cnt_snoc]
    by_cases hpos : 0 < dg n m (G ++ [g]) (n + m + G.length)
    · have hsub : {j : ℕ | j < (G ++ [g]).length ∧ 0 < dg n m (G ++ [g]) (n + m + j)} ⊆
          insert G.length {j : ℕ | j < G.length ∧ 0 < dg n m G (n + m + j)} := by
        intro j hj
        obtain ⟨h1, h2⟩ := hj
        by_cases hjl : j < G.length
        · right
          rw [dg_prefix _ _ _ _ _ (by omega)] at h2
          exact ⟨hjl, h2⟩
        · left
          simp at h1
          show j = G.length
          omega
      have h1 := Set.ncard_le_ncard hsub (hfin.insert _)
      have h2 := Set.ncard_insert_le G.length {j : ℕ | j < G.length ∧ 0 < dg n m G (n + m + j)}
      simp only [hpos, ite_true]
      omega
    · have hsub : {j : ℕ | j < (G ++ [g]).length ∧ 0 < dg n m (G ++ [g]) (n + m + j)} ⊆
          {j : ℕ | j < G.length ∧ 0 < dg n m G (n + m + j)} := by
        intro j hj
        obtain ⟨h1, h2⟩ := hj
        by_cases hjl : j < G.length
        · rw [dg_prefix _ _ _ _ _ (by omega)] at h2
          exact ⟨hjl, h2⟩
        · simp at h1
          have : j = G.length := by omega
          subst this
          exact absurd h2 hpos
      have h1 := Set.ncard_le_ncard hsub hfin
      simp only [hpos, ite_false]
      omega

theorem RB_append (N : ℕ) (G A : List Gate) (h : RB N G)
    (hA : ∀ k < A.length, ∀ i ∈ (A.getD k dflt).inputs, i < N + G.length + k) :
    RB N (G ++ A) := by
  intro j hj i hi
  by_cases hlt : j < G.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    exact h j hlt i hi
  · obtain ⟨k, rfl⟩ : ∃ k, j = G.length + k := ⟨j - G.length, by omega⟩
    rw [getD_app] at hi
    have := hA k (by simp at hj; omega) i hi
    omega

theorem Mono_append (G A : List Gate) (h : Mono G)
    (hA : ∀ g ∈ A, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Mono (G ++ A) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h g hg
  · exact hA g hg

theorem NC_append (n m : ℕ) (G A : List Gate) (hrb : RB (n + m) (G ++ A)) (h : NC n m G)
    (hA : ∀ k < A.length, (A.getD k dflt).op = GateOp.and → (A.getD k dflt).inputs.length = 2 →
      ∃ i ∈ (A.getD k dflt).inputs, dg n m (G ++ A) i = 0) :
    NC n m (G ++ A) := by
  intro j hj ho hl
  by_cases hlt : j < G.length
  · have hr := hrb j hj
    rw [List.getD_append _ _ _ _ hlt] at ho hl hr ⊢
    obtain ⟨i, hi, hz⟩ := h j hlt ho hl
    refine ⟨i, hi, ?_⟩
    rw [dg_prefix _ _ _ _ _ (by have := hr i hi; omega)]
    exact hz
  · obtain ⟨k, rfl⟩ : ∃ k, j = G.length + k := ⟨j - G.length, by omega⟩
    rw [getD_app] at ho hl ⊢
    exact hA k (by simp at hj; omega) ho hl

theorem lineDegree_eq_zero (g : Gate) (d : List ℕ) (h : ∀ a ∈ g.inputs, d.getD a 0 = 0) :
    g.lineDegree d = 0 := by
  have e : g.inputs.map (fun i => d.getD i 0) = g.inputs.map (fun _ => 0) :=
    List.map_congr_left h
  have e2 : ∀ l : List ℕ, (l.map (fun _ => 0)).foldr max 0 = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      show max 0 (List.foldr max 0 (List.map (fun _ => 0) l)) = 0
      rw [ih]
      rfl
  unfold Gate.lineDegree
  rw [e]
  split_ifs
  · simp
  · exact e2 _

-- a block of gates of degree zero keeps everything
theorem zero_block (n m : ℕ) (G A : List Gate) (hm : Mono G) (hrb : RB (n + m) G)
    (hnc : NC n m G)
    (hA1 : ∀ g ∈ A, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hA2 : ∀ k < A.length, ∀ i ∈ (A.getD k dflt).inputs, i < n + m + G.length + k)
    (hA3 : ∀ k < A.length, dg n m (G ++ A) (n + m + G.length + k) = 0) :
    Mono (G ++ A) ∧ RB (n + m) (G ++ A) ∧ NC n m (G ++ A) ∧ cnt n m (G ++ A) = cnt n m G := by
  have hrb' := RB_append _ G A hrb hA2
  refine ⟨Mono_append G A hm hA1, hrb', ?_, cnt_append_zero n m G A hA3⟩
  apply NC_append n m G A hrb' hnc
  intro k hk ho hl
  have hz := hA3 k hk
  have e : n + m + G.length + k = n + m + (G.length + k) := by omega
  rw [e, dg_gate n m (G ++ A) (G.length + k) hrb' (by simp; omega), getD_app] at hz
  have hall := lineDegree_zero _ _ hz
  rcases shape _ (le_of_eq hl) with h | ⟨a, h⟩ | ⟨a, b, h⟩
  · rw [h] at hl; simp at hl
  · rw [h] at hl; simp at hl
  · exact ⟨a, by rw [h]; exact List.mem_cons_self, hall a (by rw [h]; exact List.mem_cons_self)⟩

-- zero copy
def qx (n m : ℕ) (i : ℕ) : Bool := decide (i < n ∨ n + m ≤ i)

def zc (n m : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.or => Gate.mk GateOp.or (g.inputs.filter (qx n m))
  | _ => if g.inputs.all (qx n m) = true then g else Gate.mk GateOp.or []

theorem zc_or (n m : ℕ) (g : Gate) (h : g.op = GateOp.or) :
    zc n m g = Gate.mk GateOp.or (g.inputs.filter (qx n m)) := by
  simp [zc, h]

theorem zc_and (n m : ℕ) (g : Gate) (h : g.op = GateOp.and) :
    zc n m g = if g.inputs.all (qx n m) = true then g else Gate.mk GateOp.or [] := by
  simp [zc, h]

theorem getD_map (C : List Gate) (f : Gate → Gate) (j : ℕ) (hj : j < C.length) :
    (C.map f).getD j dflt = f (C.getD j dflt) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj]
  simp

theorem zc_in (n m : ℕ) (g : Gate) (ho : g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i ∈ (zc n m g).inputs, i ∈ g.inputs ∧ qx n m i = true := by
  intro i hi
  rcases ho with ho | ho
  · rw [zc_and n m g ho] at hi
    split_ifs at hi with hall
    · exact ⟨hi, List.all_eq_true.mp hall i hi⟩
    · simp at hi
  · rw [zc_or n m g ho] at hi
    exact List.mem_filter.mp hi

theorem zc_mono (n m : ℕ) (g : Gate) (ho : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hl : g.inputs.length ≤ 2) :
    ((zc n m g).op = GateOp.and ∨ (zc n m g).op = GateOp.or) ∧ (zc n m g).inputs.length ≤ 2 := by
  rcases ho with ho | ho
  · rw [zc_and n m g ho]
    split_ifs
    · exact ⟨Or.inl ho, hl⟩
    · exact ⟨Or.inr rfl, by simp⟩
  · rw [zc_or n m g ho]
    exact ⟨Or.inr rfl, le_trans (List.length_filter_le _ _) hl⟩

theorem Z_mono (n m : ℕ) (C : List Gate) (hm : Mono C) : Mono (C.map (zc n m)) := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  have h := hm g0 hg0
  have ho : g0.op = GateOp.and ∨ g0.op = GateOp.or := by
    have h1 := h.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  have := zc_mono n m g0 ho h.2
  refine ⟨?_, this.2⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact this.1

theorem Z_in (n m : ℕ) (C : List Gate) (hm : Mono C) (j : ℕ) (hj : j < C.length) :
    ∀ i ∈ ((C.map (zc n m)).getD j dflt).inputs,
      i ∈ (C.getD j dflt).inputs ∧ (i < n ∨ n + m ≤ i) := by
  intro i hi
  rw [getD_map C _ j hj] at hi
  have := zc_in n m _ (opcase C hm j hj).1 i hi
  refine ⟨this.1, ?_⟩
  have h2 := this.2
  simp only [qx, decide_eq_true_eq] at h2
  exact h2

theorem Z_rb (n m : ℕ) (C : List Gate) (hm : Mono C) (hrb : RB (n + m) C) :
    RB (n + m) (C.map (zc n m)) := by
  intro j hj i hi
  have hj' : j < C.length := by simpa using hj
  exact hrb j hj' i (Z_in n m C hm j hj' i hi).1

theorem Z_dg (n m : ℕ) (C : List Gate) (hm : Mono C) (hrb : RB (n + m) C) :
    ∀ i, (i < n ∨ n + m ≤ i) → dg n m (C.map (zc n m)) i = 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hq
    by_cases h1 : i < n
    · rw [dg_input _ _ _ _ (by omega)]
      simp; omega
    by_cases h3 : i < n + m + C.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + m + j := ⟨i - (n + m), by omega⟩
      have hj : j < C.length := by omega
      rw [dg_gate n m _ j (Z_rb n m C hm hrb) (by simpa using hj)]
      apply lineDegree_eq_zero
      intro a ha
      have := Z_in n m C hm j hj a ha
      have hlt := hrb j hj a this.1
      exact ih a (by omega) this.2
    · exact dg_out _ _ _ _ (by simp; omega)

theorem val_y0 {n m : ℕ} (G : List Gate) (x : Fin n → Bool) (a : ℕ) (h1 : n ≤ a)
    (h2 : a < n + m) : val G (xy x (fun _ : Fin m => false)) a = false := by
  have := val_y G x (fun _ : Fin m => false) ⟨a - n, by omega⟩
  have e : n + ((⟨a - n, by omega⟩ : Fin m) : ℕ) = a := by simp; omega
  rw [e] at this
  exact this

theorem any_filter (l : List ℕ) (q : ℕ → Bool) (f f' : ℕ → Bool)
    (h1 : ∀ a ∈ l, q a = true → f a = f' a) (h2 : ∀ a ∈ l, q a = false → f' a = false) :
    ((l.filter q).map f).any id = (l.map f').any id := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih (fun b hb => h1 b (List.mem_cons_of_mem _ hb))
      (fun b hb => h2 b (List.mem_cons_of_mem _ hb))
    cases hq : q a
    · rw [List.filter_cons_of_neg (by simp [hq]), ih']
      simp [h2 a List.mem_cons_self hq]
    · rw [List.filter_cons_of_pos (by simp [hq])]
      simp only [List.map_cons, List.any_cons, id_eq]
      rw [ih', h1 a List.mem_cons_self hq]

theorem Z_val (n m : ℕ) (C : List Gate) (hm : Mono C) (hrb : RB (n + m) C)
    (x : Fin n → Bool) (y : Fin m → Bool) :
    ∀ i, (i < n ∨ n + m ≤ i) →
      val (C.map (zc n m)) (xy x y) i = val C (xy x (fun _ : Fin m => false)) i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hq
    by_cases h1 : i < n
    · rw [val_x _ _ _ _ h1, val_x _ _ _ _ h1]
    by_cases h3 : i < n + m + C.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + m + j := ⟨i - (n + m), by omega⟩
      have hj : j < C.length := by omega
      rw [val_g _ x y j (Z_rb n m C hm hrb) (by simpa using hj), val_g C x _ j hrb hj,
        getD_map C _ j hj]
      have hr := hrb j hj
      obtain ⟨ho, hlen⟩ := opcase C hm j hj
      generalize C.getD j dflt = g at hr ho hlen ⊢
      rcases ho with ho | ho
      · rw [zc_and n m g ho]
        split_ifs with hall
        · congr 1
          apply List.map_congr_left
          intro a ha
          have hqa := List.all_eq_true.mp hall a ha
          simp only [qx, decide_eq_true_eq] at hqa
          exact ih a (by have := hr a ha; omega) hqa
        · have hex : ∃ a ∈ g.inputs, qx n m a = false := by
            by_contra hcon
            apply hall
            apply List.all_eq_true.mpr
            intro a ha
            by_contra hna
            exact hcon ⟨a, ha, by simpa using hna⟩
          obtain ⟨a, ha, hqa⟩ := hex
          simp only [qx, decide_eq_false_iff_not, not_or, not_lt, not_le] at hqa
          have hv := val_y0 C x a hqa.1 hqa.2
          rw [ho]
          symm
          simp only [GateOp.eval, List.map_nil, List.any_nil]
          apply List.all_eq_false.mpr
          exact ⟨_, List.mem_map.mpr ⟨a, ha, rfl⟩, by simp [hv]⟩
      · rw [zc_or n m g ho, ho]
        simp only [GateOp.eval]
        apply any_filter
        · intro a ha hqa
          simp only [qx, decide_eq_true_eq] at hqa
          exact ih a (by have := hr a ha; omega) hqa
        · intro a ha hqa
          simp only [qx, decide_eq_false_iff_not, not_or, not_lt, not_le] at hqa
          exact val_y0 C x a hqa.1 hqa.2
    · rw [val_out _ _ _ (by rw [xy_length]; simp; omega),
        val_out _ _ _ (by rw [xy_length]; omega)]

def St (n m : ℕ) (G : List Gate) : Prop := Mono G ∧ RB (n + m) G ∧ NC n m G

theorem val_or2 {n m : ℕ} (G : List Gate) (x : Fin n → Bool) (y : Fin m → Bool) (j a b : ℕ)
    (hrb : RB (n + m) G) (hj : j < G.length) (hg : G.getD j dflt = Gate.mk GateOp.or [a, b]) :
    val G (xy x y) (n + m + j) = (val G (xy x y) a || val G (xy x y) b) := by
  rw [val_g G x y j hrb hj, hg]
  simp [GateOp.eval]

theorem val_and2 {n m : ℕ} (G : List Gate) (x : Fin n → Bool) (y : Fin m → Bool) (j a b : ℕ)
    (hrb : RB (n + m) G) (hj : j < G.length) (hg : G.getD j dflt = Gate.mk GateOp.and [a, b]) :
    val G (xy x y) (n + m + j) = (val G (xy x y) a && val G (xy x y) b) := by
  rw [val_g G x y j hrb hj, hg]
  simp [GateOp.eval]

theorem dg_or2 (n m : ℕ) (G : List Gate) (j a b : ℕ)
    (hrb : RB (n + m) G) (hj : j < G.length) (hg : G.getD j dflt = Gate.mk GateOp.or [a, b]) :
    dg n m G (n + m + j) = max (dg n m G a) (dg n m G b) := by
  rw [dg_gate n m G j hrb hj, hg, lineDegree_or _ _ rfl]
  simp [dg]

theorem dg_and2 (n m : ℕ) (G : List Gate) (j a b : ℕ)
    (hrb : RB (n + m) G) (hj : j < G.length) (hg : G.getD j dflt = Gate.mk GateOp.and [a, b]) :
    dg n m G (n + m + j) = dg n m G a + dg n m G b := by
  rw [dg_gate n m G j hrb hj, hg, lineDegree_and _ _ rfl]
  simp [dg]

def muxA1 (N len zu zv b c : ℕ) : List Gate :=
  [Gate.mk GateOp.or [zu, b], Gate.mk GateOp.or [zv, c],
    Gate.mk GateOp.and [N + (len + 0), N + (len + 1)]]

def muxA2 (N len yl e : ℕ) : List Gate :=
  [Gate.mk GateOp.and [yl, N + (len + 2)], Gate.mk GateOp.or [e, N + (len + 3)]]

theorem mux_step (n m : ℕ) (G : List Gate) (hst : St n m G) (zu zv b c e : ℕ) (l : Fin m)
    (hzu : zu < n + m + G.length) (hzv : zv < n + m + G.length) (hb : b < n + m + G.length)
    (hc : c < n + m + G.length) (he : e < n + m + G.length)
    (dzu : dg n m G zu = 0) (dzv : dg n m G zv = 0) (db : dg n m G b = 0)
    (dc : dg n m G c = 0) (de : dg n m G e ≤ 1) :
    St n m (G ++ (muxA1 (n + m) G.length zu zv b c ++ muxA2 (n + m) G.length (n + l) e)) ∧
    cnt n m (G ++ (muxA1 (n + m) G.length zu zv b c ++ muxA2 (n + m) G.length (n + l) e)) ≤
      cnt n m G + 2 ∧
    dg n m (G ++ (muxA1 (n + m) G.length zu zv b c ++ muxA2 (n + m) G.length (n + l) e))
      (n + m + (G.length + 4)) ≤ 1 ∧
    ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      val (G ++ (muxA1 (n + m) G.length zu zv b c ++ muxA2 (n + m) G.length (n + l) e))
        (xy x y) (n + m + (G.length + 4)) =
      (val G (xy x y) e || (y l && ((val G (xy x y) zu || val G (xy x y) b) &&
        (val G (xy x y) zv || val G (xy x y) c)))) := by
  obtain ⟨hm, hrb, hnc⟩ := hst
  have hl := l.isLt
  generalize hA1 : muxA1 (n + m) G.length zu zv b c = A1
  generalize hA2 : muxA2 (n + m) G.length (n + l) e = A2
  have hlen : (A1 ++ A2).length = 5 := by rw [← hA1, ← hA2]; rfl
  have hrb' : RB (n + m) (G ++ (A1 ++ A2)) := by
    apply RB_append _ _ _ hrb
    intro k hk i hi
    rw [hlen] at hk
    rw [← hA1, ← hA2] at hi
    interval_cases k <;> simp [muxA1, muxA2] at hi <;> omega
  have g0 : (G ++ (A1 ++ A2)).getD (G.length + 0) dflt = Gate.mk GateOp.or [zu, b] := by
    rw [getD_app, ← hA1, ← hA2]; rfl
  have g1 : (G ++ (A1 ++ A2)).getD (G.length + 1) dflt = Gate.mk GateOp.or [zv, c] := by
    rw [getD_app, ← hA1, ← hA2]; rfl
  have g2 : (G ++ (A1 ++ A2)).getD (G.length + 2) dflt =
      Gate.mk GateOp.and [n + m + (G.length + 0), n + m + (G.length + 1)] := by
    rw [getD_app, ← hA1, ← hA2]; rfl
  have g3 : (G ++ (A1 ++ A2)).getD (G.length + 3) dflt =
      Gate.mk GateOp.and [n + l, n + m + (G.length + 2)] := by
    rw [getD_app, ← hA1, ← hA2]; rfl
  have g4 : (G ++ (A1 ++ A2)).getD (G.length + 4) dflt =
      Gate.mk GateOp.or [e, n + m + (G.length + 3)] := by
    rw [getD_app, ← hA1, ← hA2]; rfl
  have lt : ∀ k < 5, G.length + k < (G ++ (A1 ++ A2)).length := by
    intro k hk
    rw [List.length_append, hlen]
    omega
  have p : ∀ i, i < n + m + G.length → dg n m (G ++ (A1 ++ A2)) i = dg n m G i :=
    fun i hi => dg_prefix n m G _ i hi
  have d_0 : dg n m (G ++ (A1 ++ A2)) (n + m + (G.length + 0)) = 0 := by
    rw [dg_or2 n m _ _ zu b hrb' (lt 0 (by omega)) g0, p zu hzu, p b hb, dzu, db]
    rfl
  have d_1 : dg n m (G ++ (A1 ++ A2)) (n + m + (G.length + 1)) = 0 := by
    rw [dg_or2 n m _ _ zv c hrb' (lt 1 (by omega)) g1, p zv hzv, p c hc, dzv, dc]
    rfl
  have d_2 : dg n m (G ++ (A1 ++ A2)) (n + m + (G.length + 2)) = 0 := by
    rw [dg_and2 n m _ _ _ _ hrb' (lt 2 (by omega)) g2, d_0, d_1]
  have d_3 : dg n m (G ++ (A1 ++ A2)) (n + m + (G.length + 3)) = 1 := by
    rw [dg_and2 n m _ _ _ _ hrb' (lt 3 (by omega)) g3, d_2, p _ (by omega),
      dg_input _ _ _ _ (by omega)]
    simp
  have d_4 : dg n m (G ++ (A1 ++ A2)) (n + m + (G.length + 4)) ≤ 1 := by
    rw [dg_or2 n m _ _ _ _ hrb' (lt 4 (by omega)) g4, d_3, p e he]
    exact max_le de (le_refl 1)
  have hmono' : Mono (G ++ (A1 ++ A2)) := by
    apply Mono_append G _ hm
    intro g hg
    rw [← hA1, ← hA2] at hg
    simp only [muxA1, muxA2, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  have hnc' : NC n m (G ++ (A1 ++ A2)) := by
    apply NC_append n m G _ hrb' hnc
    intro k hk ho hl2
    rw [hlen] at hk
    have h0 := g0
    have h1 := g1
    have h2 := g2
    have h3 := g3
    have h4 := g4
    rw [getD_app] at h0 h1 h2 h3 h4
    interval_cases k
    · rw [h0] at ho; simp at ho
    · rw [h1] at ho; simp at ho
    · rw [h2]
      exact ⟨n + m + (G.length + 0), List.mem_cons_self, d_0⟩
    · rw [h3]
      exact ⟨n + m + (G.length + 2), by simp, d_2⟩
    · rw [h4] at ho; simp at ho
  have hA1len : A1.length = 3 := by rw [← hA1]; rfl
  have hA2len : A2.length = 2 := by rw [← hA2]; rfl
  have c1 : cnt n m (G ++ A1) = cnt n m G := by
    apply cnt_append_zero
    intro k hk
    rw [hA1len] at hk
    rw [← dg_prefix n m (G ++ A1) A2 _ (by rw [List.length_append, hA1len]; omega),
      List.append_assoc]
    interval_cases k
    · exact d_0
    · exact d_1
    · exact d_2
  have c2 := cnt_append_le n m (G ++ A1) A2
  rw [List.append_assoc, hA2len, c1] at c2
  refine ⟨⟨hmono', hrb', hnc'⟩, c2, d_4, ?_⟩
  intro x y
  have pv : ∀ i, i < n + m + G.length →
      val (G ++ (A1 ++ A2)) (xy x y) i = val G (xy x y) i :=
    fun i hi => val_prefix G _ _ i (by rw [xy_length]; exact hi)
  rw [val_or2 _ x y _ _ _ hrb' (lt 4 (by omega)) g4,
    val_and2 _ x y _ _ _ hrb' (lt 3 (by omega)) g3,
    val_and2 _ x y _ _ _ hrb' (lt 2 (by omega)) g2,
    val_or2 _ x y _ _ _ hrb' (lt 0 (by omega)) g0,
    val_or2 _ x y _ _ _ hrb' (lt 1 (by omega)) g1,
    pv e he, pv zu hzu, pv b hb, pv zv hzv, pv c hc, val_y]

theorem ex_succ {m : ℕ} (P : Fin m → Bool) (l : ℕ) (hl : l < m) :
    decide (∃ j : Fin m, (j : ℕ) < l + 1 ∧ P j = true) =
      (decide (∃ j : Fin m, (j : ℕ) < l ∧ P j = true) || P ⟨l, hl⟩) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨j, hj, hp⟩
    by_cases h : (j : ℕ) < l
    · exact Or.inl ⟨j, h, hp⟩
    · right
      have : j = ⟨l, hl⟩ := Fin.ext (by simp; omega)
      rw [← this]
      exact hp
  · rintro (⟨j, hj, hp⟩ | hp)
    · exact ⟨j, by omega, hp⟩
    · exact ⟨⟨l, hl⟩, by simp, hp⟩

theorem mux_loop (n m : ℕ) (G : List Gate) (hst : St n m G) (zu zv e0 : ℕ) (b c : Fin m → ℕ)
    (hzu : zu < n + m + G.length) (hzv : zv < n + m + G.length)
    (hb : ∀ j, b j < n + m + G.length) (hc : ∀ j, c j < n + m + G.length)
    (he : e0 < n + m + G.length)
    (dzu : dg n m G zu = 0) (dzv : dg n m G zv = 0) (db : ∀ j, dg n m G (b j) = 0)
    (dc : ∀ j, dg n m G (c j) = 0) (de : dg n m G e0 ≤ 1) :
    ∀ l ≤ m, ∃ (H : List Gate) (e : ℕ),
      St n m (G ++ H) ∧ H.length = 5 * l ∧ cnt n m (G ++ H) ≤ cnt n m G + 2 * l ∧
      e < n + m + (G ++ H).length ∧ dg n m (G ++ H) e ≤ 1 ∧
      ∀ (x : Fin n → Bool) (y : Fin m → Bool),
        val (G ++ H) (xy x y) e =
          (val G (xy x y) e0 || decide (∃ j : Fin m, (j : ℕ) < l ∧
            (y j && ((val G (xy x y) zu || val G (xy x y) (b j)) &&
              (val G (xy x y) zv || val G (xy x y) (c j)))) = true)) := by
  intro l
  induction l with
  | zero =>
    intro _
    refine ⟨[], e0, by simpa using hst, rfl, by simp, by simpa using he, by simpa using de, ?_⟩
    intro x y
    simp
  | succ l ih =>
    intro hl
    obtain ⟨H, e, hst', hlen, hcnt, he', hde, hval⟩ := ih (by omega)
    have hlt : l < m := by omega
    have hGH : (G ++ H).length = G.length + H.length := List.length_append
    obtain ⟨s1, s2, s3, s4⟩ := mux_step n m (G ++ H) hst' zu zv (b ⟨l, hlt⟩) (c ⟨l, hlt⟩) e
      ⟨l, hlt⟩ (by omega) (by omega) (by have := hb ⟨l, hlt⟩; omega)
      (by have := hc ⟨l, hlt⟩; omega) he'
      (by rw [dg_prefix _ _ _ _ _ hzu]; exact dzu) (by rw [dg_prefix _ _ _ _ _ hzv]; exact dzv)
      (by rw [dg_prefix _ _ _ _ _ (hb _)]; exact db _)
      (by rw [dg_prefix _ _ _ _ _ (hc _)]; exact dc _) hde
    refine ⟨H ++ (muxA1 (n + m) (G ++ H).length zu zv (b ⟨l, hlt⟩) (c ⟨l, hlt⟩) ++
      muxA2 (n + m) (G ++ H).length (n + l) e), n + m + ((G ++ H).length + 4), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← List.append_assoc]; exact s1
    · rw [List.length_append, hlen]
      show 5 * l + 5 = 5 * (l + 1)
      omega
    · rw [← List.append_assoc]
      refine le_trans s2 ?_
      omega
    · rw [← List.append_assoc, List.length_append (as := G ++ H)]
      show n + m + ((G ++ H).length + 4) < n + m + ((G ++ H).length + 5)
      omega
    · rw [← List.append_assoc]; exact s3
    · intro x y
      have pv : ∀ i, i < n + m + G.length → val (G ++ H) (xy x y) i = val G (xy x y) i :=
        fun i hi => val_prefix G _ _ i (by rw [xy_length]; exact hi)
      rw [← List.append_assoc, s4 x y, hval x y, pv zu hzu, pv zv hzv, pv _ (hb _), pv _ (hc _),
        ex_succ (fun j : Fin m => (y j && ((val G (xy x y) zu || val G (xy x y) (b j)) &&
              (val G (xy x y) zv || val G (xy x y) (c j))))) l hlt, Bool.or_assoc]

theorem adj' (n m : ℕ) (hadj : ∀ (G : List Gate) (r : ℕ), AdjointSpec n m G r) (G : List Gate)
    (hst : St n m G) (r : ℕ) (hr : r < n + m + G.length) :
    ∃ (A : List Gate) (o : Fin m → ℕ), St n m (G ++ A) ∧ cnt n m (G ++ A) = cnt n m G ∧
      A.length ≤ 3 * cnt n m G + m ∧
      (∀ j : Fin m, o j < n + m + (G ++ A).length ∧ dg n m (G ++ A) (o j) = 0) ∧
      ∀ (x : Fin n → Bool) (y : Fin m → Bool) (j : Fin m),
        val G (xy x (fun l => decide (l = j))) r =
          (val G (xy x (fun _ : Fin m => false)) r || val (G ++ A) (xy x y) (o j)) := by
  obtain ⟨hm, hrb, hnc⟩ := hst
  obtain ⟨A, o, h1, h2, h3, h4, h5, h6⟩ := hadj G r hm hrb hnc hr
  obtain ⟨z1, z2, z3, z4⟩ := zero_block n m G A hm hrb hnc h1 h2 h4
  have h3' : A.length ≤
      3 * Set.ncard {j : ℕ | j < G.length ∧ 0 < dg n m G (n + m + j)} + m := h3
  have hle := ncard_le_cnt n m G
  refine ⟨A, o, ⟨z1, z2, z3⟩, z4, by omega, ?_, h6⟩
  intro j
  have := h5 j
  refine ⟨?_, this.2⟩
  rw [List.length_append]
  omega

def Wok (n m : ℕ) (C G : List Gate) (w pw : ℕ) : Prop :=
  pw < n + m + G.length ∧ dg n m G pw ≤ dg n m C w ∧
  ∀ x : Fin n → Bool,
    val G (xy x (fun _ : Fin m => false)) pw = val C (xy x (fun _ : Fin m => false)) w ∧
    ∀ j : Fin m, val G (xy x (fun l => decide (l = j))) pw =
      val C (xy x (fun l => decide (l = j))) w

theorem Wok_append (n m : ℕ) (C G : List Gate) (w pw : ℕ) (h : Wok n m C G w pw)
    (B : List Gate) : Wok n m C (G ++ B) w pw := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [List.length_append]; omega, by rw [dg_prefix _ _ _ _ _ h1]; exact h2,
    fun x => ⟨?_, fun j => ?_⟩⟩
  · rw [val_prefix _ _ _ _ (by rw [xy_length]; exact h1)]; exact (h3 x).1
  · rw [val_prefix _ _ _ _ (by rw [xy_length]; exact h1)]; exact (h3 x).2 j

theorem sum_map_le (l : List ℕ) (f f' : ℕ → ℕ) (h : ∀ a ∈ l, f a ≤ f' a) :
    (l.map f).sum ≤ (l.map f').sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.sum_cons]
    omega

theorem foldr_map_le (l : List ℕ) (f f' : ℕ → ℕ) (h : ∀ a ∈ l, f a ≤ f' a) :
    (l.map f).foldr max 0 ≤ (l.map f').foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le_max (h a List.mem_cons_self) (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

def Inv (n m : ℕ) (C G : List Gate) (p : ℕ → ℕ) (i κ : ℕ) : Prop :=
  St n m G ∧ (∃ A, G = C.map (zc n m) ++ A) ∧ (∀ w < n + m + i, Wok n m C G w (p w)) ∧
  G.length ≤ C.length + i + κ * (6 * (i + κ * (2 * m + 1)) + 7 * m + 2) ∧
  cnt n m G ≤ i + κ * (2 * m + 1)

theorem copy_step (n m : ℕ) (C G : List Gate) (p : ℕ → ℕ) (i κ : ℕ) (hmC : Mono C)
    (hrbC : RB (n + m) C) (hi : i < C.length) (hinv : Inv n m C G p i κ)
    (hnx : (C.getD i dflt).op = GateOp.and → (C.getD i dflt).inputs.length = 2 →
      ∃ a ∈ (C.getD i dflt).inputs, dg n m C a = 0) :
    ∃ (G' : List Gate) (p' : ℕ → ℕ), Inv n m C G' p' (i + 1) κ := by
  obtain ⟨⟨hm, hrb, hnc⟩, ⟨A, hA⟩, hw, hsz, hcn⟩ := hinv
  have hr := hrbC i hi
  obtain ⟨ho, hlen⟩ := opcase C hmC i hi
  have dC := dg_gate n m C i hrbC hi
  have vC : ∀ (x : Fin n → Bool) (y : Fin m → Bool), val C (xy x y) (n + m + i) =
      (C.getD i dflt).op.eval ((C.getD i dflt).inputs.map (val C (xy x y))) :=
    fun x y => val_g C x y i hrbC hi
  generalize C.getD i dflt = g at hr ho hlen hnx dC vC
  have hin : ∀ a ∈ g.inputs, Wok n m C G a (p a) :=
    fun a ha => hw a (by have := hr a ha; omega)
  have hrb' : RB (n + m) (G ++ [Gate.mk g.op (g.inputs.map p)]) := by
    apply RB_append _ _ _ hrb
    intro k hk b hb
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp only [List.getD_cons_zero, List.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    have := (hin a ha).1
    omega
  have hm' : Mono (G ++ [Gate.mk g.op (g.inputs.map p)]) := by
    apply Mono_append G _ hm
    intro q hq
    have hq' : q = Gate.mk g.op (g.inputs.map p) := by simpa using hq
    subst hq'
    refine ⟨?_, by simpa using hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ho
  have hnc' : NC n m (G ++ [Gate.mk g.op (g.inputs.map p)]) := by
    apply NC_append n m G _ hrb' hnc
    intro k hk ho' hl'
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    simp only [List.getD_cons_zero, List.length_map] at ho' hl' ⊢
    obtain ⟨a, ha, hz⟩ := hnx ho' hl'
    refine ⟨p a, List.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
    rw [dg_prefix _ _ _ _ _ (hin a ha).1]
    have := (hin a ha).2.1
    omega
  have hnew : Wok n m C (G ++ [Gate.mk g.op (g.inputs.map p)]) (n + m + i)
      (n + m + G.length) := by
    refine ⟨by simp, ?_, fun x => ⟨?_, fun j => ?_⟩⟩
    · rw [dg_new, dC]
      rcases ho with ho | ho
      · rw [lineDegree_and g _ ho, lineDegree_and (Gate.mk g.op (g.inputs.map p)) _ ho]
        show ((g.inputs.map p).map _).sum ≤ _
        rw [List.map_map]
        apply sum_map_le
        intro a ha
        exact (hin a ha).2.1
      · rw [lineDegree_or g _ ho, lineDegree_or (Gate.mk g.op (g.inputs.map p)) _ ho]
        show ((g.inputs.map p).map _).foldr max 0 ≤ _
        rw [List.map_map]
        apply foldr_map_le
        intro a ha
        exact (hin a ha).2.1
    · have e := val_new G (Gate.mk g.op (g.inputs.map p)) (xy x (fun _ : Fin m => false))
      rw [xy_length] at e
      rw [e, vC]
      show g.op.eval ((g.inputs.map p).map _) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ((hin a ha).2.2 x).1
    · have e := val_new G (Gate.mk g.op (g.inputs.map p)) (xy x (fun l => decide (l = j)))
      rw [xy_length] at e
      rw [e, vC]
      show g.op.eval ((g.inputs.map p).map _) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ((hin a ha).2.2 x).2 j
  refine ⟨G ++ [Gate.mk g.op (g.inputs.map p)],
    fun w => if w = n + m + i then n + m + G.length else p w,
    ⟨hm', hrb', hnc'⟩, ⟨A ++ [Gate.mk g.op (g.inputs.map p)], by rw [hA, List.append_assoc]⟩,
    ?_, ?_, ?_⟩
  · intro w hw'
    by_cases hwe : w = n + m + i
    · subst hwe
      simp only [↓reduceIte]
      exact hnew
    · simp only [hwe, ↓reduceIte]
      exact Wok_append n m C G w _ (hw w (by omega)) _
  · simp only [List.length_append, List.length_singleton]
    have : κ * (6 * (i + κ * (2 * m + 1)) + 7 * m + 2) ≤
        κ * (6 * (i + 1 + κ * (2 * m + 1)) + 7 * m + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · have := cnt_snoc_le n m G (Gate.mk g.op (g.inputs.map p))
    omega

theorem add_zero (n m : ℕ) (G : List Gate) (hst : St n m G) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hin : ∀ a ∈ g.inputs, a < n + m + G.length ∧ dg n m G a = 0) :
    St n m (G ++ [g]) ∧ cnt n m (G ++ [g]) = cnt n m G ∧
      dg n m (G ++ [g]) (n + m + G.length) = 0 ∧
      ∀ (x : Fin n → Bool) (y : Fin m → Bool),
        val (G ++ [g]) (xy x y) (n + m + G.length) = g.op.eval (g.inputs.map (val G (xy x y))) := by
  obtain ⟨hm, hrb, hnc⟩ := hst
  have hd : dg n m (G ++ [g]) (n + m + G.length) = 0 := by
    rw [dg_new]
    exact lineDegree_eq_zero _ _ (fun a ha => (hin a ha).2)
  obtain ⟨z1, z2, z3, z4⟩ := zero_block n m G [g] hm hrb hnc
    (by
      intro q hq
      have hq' : q = g := by simpa using hq
      subst hq'
      refine ⟨?_, hlen⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact hop)
    (by
      intro k hk a ha
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      simp only [List.getD_cons_zero] at ha
      have := (hin a ha).1
      omega)
    (by
      intro k hk
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      exact hd)
  refine ⟨⟨z1, z2, z3⟩, z4, hd, ?_⟩
  intro x y
  have e := val_new G g (xy x y)
  rw [xy_length] at e
  exact e

theorem zf (n m : ℕ) (C G3 : List Gate) (hmC : Mono C) (hrbC : RB (n + m) C) (B : List Gate)
    (hG3 : G3 = C.map (zc n m) ++ B) (Fw : ℕ) (hF1 : Fw < n + m + G3.length)
    (hF2 : dg n m G3 Fw = 0) (hF3 : ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      val G3 (xy x y) Fw = false) (u : ℕ) (hu : u < n + m + C.length) :
    (if n ≤ u ∧ u < n + m then Fw else u) < n + m + G3.length ∧
    dg n m G3 (if n ≤ u ∧ u < n + m then Fw else u) = 0 ∧
    ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      val G3 (xy x y) (if n ≤ u ∧ u < n + m then Fw else u) =
        val C (xy x (fun _ : Fin m => false)) u := by
  split_ifs with h
  · exact ⟨hF1, hF2, fun x y => by rw [hF3, val_y0 C x u h.1 h.2]⟩
  · have hq : u < n ∨ n + m ≤ u := by omega
    subst hG3
    refine ⟨by simp; omega, ?_, fun x y => ?_⟩
    · rw [dg_prefix _ _ _ _ _ (by simp; omega)]
      exact Z_dg n m C hmC hrbC u hq
    · rw [val_prefix _ _ _ _ (by rw [xy_length]; simp; omega)]
      exact Z_val n m C hmC hrbC x y u hq

theorem ex_single {m : ℕ} (P : Fin m → Bool) (l : Fin m) :
    decide (∃ j : Fin m, (decide (j = l) && P j) = true) = P l := by
  rw [Bool.eq_iff_iff]
  simp

theorem cross_step (n m : ℕ) (hadj : ∀ (G : List Gate) (r : ℕ), AdjointSpec n m G r)
    (C G : List Gate) (p : ℕ → ℕ) (i κ : ℕ) (hmC : Mono C)
    (hrbC : RB (n + m) C) (hi : i < C.length) (hinv : Inv n m C G p i κ) (u v : ℕ)
    (hg : C.getD i dflt = Gate.mk GateOp.and [u, v]) (hu : 0 < dg n m C u)
    (hv : 0 < dg n m C v) :
    ∃ (G' : List Gate) (p' : ℕ → ℕ), Inv n m C G' p' (i + 1) (κ + 1) := by
  obtain ⟨hst, ⟨A, hA⟩, hw, hsz, hcn⟩ := hinv
  have hr := hrbC i hi
  rw [hg] at hr
  have hul : u < n + m + i := hr u (by simp)
  have hvl : v < n + m + i := hr v (by simp)
  have wu := hw u hul
  have wv := hw v hvl
  have hold : ∀ (H : List Gate), ∀ w < n + m + i,
      Wok n m C (G ++ H) w (p w) := fun H w hlt => Wok_append n m C G w _ (hw w hlt) H
  -- first adjoint
  obtain ⟨A1, o1, st1, c1, len1, ho1, eq1⟩ := adj' n m hadj G hst (p u) wu.1
  have l1 : (G ++ A1).length = G.length + A1.length := List.length_append
  have pv1 : ∀ (X : List Bool) (a : ℕ), X.length = n + m → a < n + m + G.length →
      val (G ++ A1) X a = val G X a :=
    fun X a hX ha => val_prefix G A1 X a (by rw [hX]; exact ha)
  have hG1 : ∃ B1, G ++ A1 = G ++ B1 := ⟨A1, rfl⟩
  generalize G ++ A1 = G1 at st1 c1 ho1 eq1 l1 pv1 hG1
  -- second adjoint
  obtain ⟨A2, o2, st2, c2, len2, ho2, eq2⟩ :=
    adj' n m hadj G1 st1 (p v) (by have := wv.1; omega)
  have l2 : (G1 ++ A2).length = G1.length + A2.length := List.length_append
  have pv2 : ∀ (X : List Bool) (a : ℕ), X.length = n + m → a < n + m + G1.length →
      val (G1 ++ A2) X a = val G1 X a :=
    fun X a hX ha => val_prefix G1 A2 X a (by rw [hX]; exact ha)
  have pd2 : ∀ a, a < n + m + G1.length → dg n m (G1 ++ A2) a = dg n m G1 a :=
    fun a ha => dg_prefix n m G1 A2 a ha
  have hG2 : ∃ B2, G1 ++ A2 = G ++ B2 := by
    obtain ⟨B1, hB1⟩ := hG1
    exact ⟨B1 ++ A2, by rw [hB1, List.append_assoc]⟩
  generalize G1 ++ A2 = G2 at st2 c2 ho2 eq2 l2 pv2 pd2 hG2
  -- the constant false
  obtain ⟨st3, c3, d3, v3⟩ := add_zero n m G2 st2 (Gate.mk GateOp.or []) (Or.inr rfl)
    (by simp) (by intro a ha; cases ha)
  have l3 : (G2 ++ [Gate.mk GateOp.or []]).length = G2.length + 1 := by simp
  have pv3 : ∀ (X : List Bool) (a : ℕ), X.length = n + m → a < n + m + G2.length →
      val (G2 ++ [Gate.mk GateOp.or []]) X a = val G2 X a :=
    fun X a hX ha => val_prefix G2 _ X a (by rw [hX]; exact ha)
  have pd3 : ∀ a, a < n + m + G2.length →
      dg n m (G2 ++ [Gate.mk GateOp.or []]) a = dg n m G2 a :=
    fun a ha => dg_prefix n m G2 _ a ha
  have hG3 : ∃ B3, G2 ++ [Gate.mk GateOp.or []] = G ++ B3 := by
    obtain ⟨B2, hB2⟩ := hG2
    exact ⟨B2 ++ [Gate.mk GateOp.or []], by rw [hB2, List.append_assoc]⟩
  have v3' : ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      val (G2 ++ [Gate.mk GateOp.or []]) (xy x y) (n + m + G2.length) = false := by
    intro x y
    rw [v3]
    simp [GateOp.eval]
  generalize G2 ++ [Gate.mk GateOp.or []] = G3 at st3 c3 d3 l3 pv3 pd3 hG3 v3'
  have hG3Z : ∃ B, G3 = C.map (zc n m) ++ B := by
    obtain ⟨B3, hB3⟩ := hG3
    exact ⟨A ++ B3, by rw [hB3, hA, List.append_assoc]⟩
  obtain ⟨BZ, hBZ⟩ := hG3Z
  obtain ⟨zu1, zu2, zu3⟩ := zf n m C G3 hmC hrbC BZ hBZ (n + m + G2.length) (by omega) d3 v3'
    u (by omega)
  obtain ⟨zv1, zv2, zv3⟩ := zf n m C G3 hmC hrbC BZ hBZ (n + m + G2.length) (by omega) d3 v3'
    v (by omega)
  generalize (if n ≤ u ∧ u < n + m then n + m + G2.length else u) = zu at zu1 zu2 zu3
  generalize (if n ≤ v ∧ v < n + m then n + m + G2.length else v) = zv at zv1 zv2 zv3
  -- the gate zu AND zv
  obtain ⟨st4, c4, d4, v4⟩ := add_zero n m G3 st3 (Gate.mk GateOp.and [zu, zv]) (Or.inl rfl)
    (by simp) (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨zu1, zu2⟩
      · exact ⟨zv1, zv2⟩)
  have l4 : (G3 ++ [Gate.mk GateOp.and [zu, zv]]).length = G3.length + 1 := by simp
  have pv4 : ∀ (X : List Bool) (a : ℕ), X.length = n + m → a < n + m + G3.length →
      val (G3 ++ [Gate.mk GateOp.and [zu, zv]]) X a = val G3 X a :=
    fun X a hX ha => val_prefix G3 _ X a (by rw [hX]; exact ha)
  have pd4 : ∀ a, a < n + m + G3.length →
      dg n m (G3 ++ [Gate.mk GateOp.and [zu, zv]]) a = dg n m G3 a :=
    fun a ha => dg_prefix n m G3 _ a ha
  have hG4 : ∃ B4, G3 ++ [Gate.mk GateOp.and [zu, zv]] = G ++ B4 := by
    obtain ⟨B3, hB3⟩ := hG3
    exact ⟨B3 ++ [Gate.mk GateOp.and [zu, zv]], by rw [hB3, List.append_assoc]⟩
  have v4' : ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      val (G3 ++ [Gate.mk GateOp.and [zu, zv]]) (xy x y) (n + m + G3.length) =
        (val C (xy x (fun _ : Fin m => false)) u && val C (xy x (fun _ : Fin m => false)) v) := by
    intro x y
    rw [v4]
    simp [GateOp.eval, zu3, zv3]
  generalize G3 ++ [Gate.mk GateOp.and [zu, zv]] = G4 at st4 c4 d4 l4 pv4 pd4 hG4 v4'
  have hzu4 : ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      val G4 (xy x y) zu = val C (xy x (fun _ : Fin m => false)) u := by
    intro x y
    rw [pv4 _ _ (xy_length x y) zu1, zu3]
  have hzv4 : ∀ (x : Fin n → Bool) (y : Fin m → Bool),
      val G4 (xy x y) zv = val C (xy x (fun _ : Fin m => false)) v := by
    intro x y
    rw [pv4 _ _ (xy_length x y) zv1, zv3]
  have hU : ∀ (x : Fin n → Bool) (y : Fin m → Bool) (j : Fin m),
      (val C (xy x (fun _ : Fin m => false)) u || val G4 (xy x y) (o1 j)) =
        val C (xy x (fun l => decide (l = j))) u := by
    intro x y j
    have hb := (ho1 j).1
    rw [pv4 _ _ (xy_length x y) (by omega), pv3 _ _ (xy_length x y) (by omega),
      pv2 _ _ (xy_length x y) hb, ← (wu.2.2 x).1, ← (wu.2.2 x).2 j]
    exact (eq1 x y j).symm
  have hV : ∀ (x : Fin n → Bool) (y : Fin m → Bool) (j : Fin m),
      (val C (xy x (fun _ : Fin m => false)) v || val G4 (xy x y) (o2 j)) =
        val C (xy x (fun l => decide (l = j))) v := by
    intro x y j
    have hb := (ho2 j).1
    have e2 := eq2 x y j
    rw [pv1 _ _ (xy_length x _) wv.1, pv1 _ _ (xy_length x _) wv.1, (wv.2.2 x).1,
      (wv.2.2 x).2 j] at e2
    rw [pv4 _ _ (xy_length x y) (by omega), pv3 _ _ (xy_length x y) hb]
    exact e2.symm
  -- the multiplexer
  obtain ⟨H, e, st5, lenH, c5, he, hde, hval⟩ := mux_loop n m G4 st4 zu zv (n + m + G3.length)
    o1 o2 (by omega) (by omega) (fun j => by have := (ho1 j).1; omega)
    (fun j => by have := (ho2 j).1; omega) (by omega)
    (by rw [pd4 _ zu1]; exact zu2) (by rw [pd4 _ zv1]; exact zv2)
    (fun j => by
      have hb := (ho1 j).1
      rw [pd4 _ (by omega), pd3 _ (by omega), pd2 _ hb]
      exact (ho1 j).2)
    (fun j => by
      have hb := (ho2 j).1
      rw [pd4 _ (by omega), pd3 _ hb]
      exact (ho2 j).2)
    (by omega) m (le_refl m)
  have key : ∀ (x : Fin n → Bool) (y : Fin m → Bool), val (G4 ++ H) (xy x y) e =
      ((val C (xy x (fun _ : Fin m => false)) u && val C (xy x (fun _ : Fin m => false)) v) ||
        decide (∃ j : Fin m, (y j && (val C (xy x (fun l => decide (l = j))) u &&
          val C (xy x (fun l => decide (l = j))) v)) = true)) := by
    intro x y
    rw [hval x y, v4']
    simp only [hzu4, hzv4, hU, hV, Fin.is_lt, true_and]
  have dCi := dg_and2 n m C i u v hrbC hi hg
  have hnew : Wok n m C (G4 ++ H) (n + m + i) e := by
    refine ⟨he, by omega, fun x => ⟨?_, fun l => ?_⟩⟩
    · rw [key, val_and2 C x _ i u v hrbC hi hg]
      simp
    · rw [key, val_and2 C x _ i u v hrbC hi hg, ex_single]
      have h1 := hU x (fun _ => false) l
      have h2 := hV x (fun _ => false) l
      rw [← h1, ← h2]
      generalize val C (xy x (fun _ : Fin m => false)) u = a
      generalize val C (xy x (fun _ : Fin m => false)) v = b
      generalize val G4 (xy x (fun _ : Fin m => false)) (o1 l) = c
      generalize val G4 (xy x (fun _ : Fin m => false)) (o2 l) = d
      cases a <;> cases b <;> cases c <;> cases d <;> rfl
  obtain ⟨B4, hB4⟩ := hG4
  have e1 : (κ + 1) * (2 * m + 1) = κ * (2 * m + 1) + (2 * m + 1) := by ring
  refine ⟨G4 ++ H, fun w => if w = n + m + i then e else p w, st5,
    ⟨A ++ B4 ++ H, by rw [hB4, hA]; simp [List.append_assoc]⟩, ?_, ?_, ?_⟩
  · intro w hw'
    by_cases hwe : w = n + m + i
    · subst hwe
      simp only [↓reduceIte]
      exact hnew
    · simp only [hwe, ↓reduceIte]
      rw [hB4, List.append_assoc]
      exact hold _ w (by omega)
  · rw [List.length_append, lenH]
    have e3 : κ * (6 * (i + κ * (2 * m + 1)) + 7 * m + 2) ≤
        κ * (6 * (i + 1 + (κ * (2 * m + 1) + (2 * m + 1))) + 7 * m + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have e2 : (κ + 1) * (6 * (i + 1 + (κ * (2 * m + 1) + (2 * m + 1))) + 7 * m + 2) =
        κ * (6 * (i + 1 + (κ * (2 * m + 1) + (2 * m + 1))) + 7 * m + 2) +
          (6 * (i + 1 + (κ * (2 * m + 1) + (2 * m + 1))) + 7 * m + 2) := by ring
    rw [e1, e2]
    omega
  · rw [e1]
    omega

def crossB (n m : ℕ) (C : List Gate) (j : ℕ) : Bool :=
  match (C.getD j dflt).op, (C.getD j dflt).inputs with
  | GateOp.and, [a, b] => decide (0 < dg n m C a) && decide (0 < dg n m C b)
  | _, _ => false

theorem crossB_true (n m : ℕ) (C : List Gate) (j : ℕ) (h : crossB n m C j = true) :
    ∃ u v, C.getD j dflt = Gate.mk GateOp.and [u, v] ∧ 0 < dg n m C u ∧ 0 < dg n m C v := by
  unfold crossB at h
  split at h
  · rename_i a b h1 h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨a, b, ?_, h.1, h.2⟩
    cases hgd : C.getD j dflt with
    | mk op inp =>
      rw [hgd] at h1 h2
      simp only at h1 h2
      rw [h1, h2]
  · simp at h

theorem crossB_false (n m : ℕ) (C : List Gate) (j : ℕ) (h : crossB n m C j = false)
    (ho : (C.getD j dflt).op = GateOp.and) (hl : (C.getD j dflt).inputs.length = 2) :
    ∃ a ∈ (C.getD j dflt).inputs, dg n m C a = 0 := by
  rcases shape _ (le_of_eq hl) with hs | ⟨a, hs⟩ | ⟨a, b, hs⟩
  · rw [hs] at hl; simp at hl
  · rw [hs] at hl; simp at hl
  · unfold crossB at h
    rw [ho, hs] at h
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt, Nat.le_zero] at h
    rw [hs]
    rcases h with h | h
    · exact ⟨a, by simp, h⟩
    · exact ⟨b, by simp, h⟩

def kap (n m : ℕ) (C : List Gate) (i : ℕ) : ℕ :=
  ((Finset.range i).filter (fun j => crossB n m C j = true)).card

theorem kap_succ (n m : ℕ) (C : List Gate) (i : ℕ) :
    kap n m C (i + 1) = kap n m C i + (if crossB n m C i = true then 1 else 0) := by
  unfold kap
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem kap_le (n m : ℕ) (C : List Gate) :
    kap n m C C.length ≤ Set.ncard {j : ℕ | j < C.length ∧
      (C.getD j dflt).op = GateOp.and ∧ (C.getD j dflt).inputs.length = 2 ∧
      ∀ i ∈ (C.getD j dflt).inputs, 0 < dg n m C i} := by
  unfold kap
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj
    obtain ⟨u, v, hg, hu, hv⟩ := crossB_true n m C j hj.2
    refine ⟨hj.1, ?_, ?_, ?_⟩
    · rw [hg]
    · rw [hg]; rfl
    · rw [hg]
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hu
      · exact hv
  · exact (Set.finite_Iio C.length).subset (fun j hj => hj.1)

theorem cnt_nil (n m : ℕ) : cnt n m [] = 0 := by
  unfold cnt
  rw [List.drop_eq_nil_of_le (by rw [Dg_length, d0_length]; simp)]
  rfl

theorem main_ind (n m : ℕ) (hadj : ∀ (G : List Gate) (r : ℕ), AdjointSpec n m G r)
    (C : List Gate) (hmC : Mono C) (hrbC : RB (n + m) C) :
    ∀ i ≤ C.length, ∃ (G : List Gate) (p : ℕ → ℕ), Inv n m C G p i (kap n m C i) := by
  intro i
  induction i with
  | zero =>
    intro _
    have hZrb := Z_rb n m C hmC hrbC
    have hZd := Z_dg n m C hmC hrbC
    refine ⟨C.map (zc n m), fun w => w, ⟨Z_mono n m C hmC, hZrb, ?_⟩, ⟨[], by simp⟩, ?_, ?_, ?_⟩
    · intro j hj ho hl
      have hj' : j < C.length := by simpa using hj
      rcases shape _ (le_of_eq hl) with hs | ⟨a, hs⟩ | ⟨a, b, hs⟩
      · rw [hs] at hl; simp at hl
      · rw [hs] at hl; simp at hl
      · have hin := Z_in n m C hmC j hj' a (by rw [hs]; exact List.mem_cons_self)
        exact ⟨a, by rw [hs]; exact List.mem_cons_self, hZd a hin.2⟩
    · intro w hw
      refine ⟨by show w < _; omega, ?_, fun x => ⟨?_, fun j => ?_⟩⟩
      · rw [dg_input _ _ _ _ (by omega), dg_input _ _ _ _ (by omega)]
      · rw [val_input _ _ _ (by rw [xy_length]; omega), val_input _ _ _ (by rw [xy_length]; omega)]
      · rw [val_input _ _ _ (by rw [xy_length]; omega), val_input _ _ _ (by rw [xy_length]; omega)]
    · simp
    · have h0 := cnt_append_zero n m [] (C.map (zc n m)) (by
        intro k hk
        exact hZd _ (by simp))
      simp only [List.nil_append] at h0
      rw [h0, cnt_nil]
      omega
  | succ i ih =>
    intro hi
    obtain ⟨G, p, hinv⟩ := ih (by omega)
    rw [kap_succ]
    cases hc : crossB n m C i
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact copy_step n m C G p i _ hmC hrbC (by omega) hinv (crossB_false n m C i hc)
    · simp only [↓reduceIte]
      obtain ⟨u, v, hg, hu, hv⟩ := crossB_true n m C i hc
      exact cross_step n m hadj C G p i _ hmC hrbC (by omega) hinv u v hg hu hv

theorem main (hadj : ∀ (n m : ℕ) (G : List Gate) (r : ℕ), AdjointSpec n m G r) :
    (∀ (n m s k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → ∃ M : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 M ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) M ∧ (∀ j < M.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt M j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs, (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) ∧ M.size ≤ (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k ∧ Set.ncard {j : ℕ | j < M.gates.length ∧ 0 < (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} ≤ s + k * (2 * m + 1) ∧ ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), PEqualNP.MetaComplexity.circuitFun (n + m) M (Fin.append x (fun l => decide (l ∈ Y))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || decide (∃ j ∈ Y, PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = true))) := by
  intro n m s k C hM hR hs hk
  obtain ⟨G, p, hinv⟩ := main_ind n m (hadj n m) C.gates hM hR C.gates.length le_rfl
  obtain ⟨⟨hm, hrb, hnc⟩, _, hw, hsz, hcn⟩ := hinv
  have hκ : kap n m C.gates C.gates.length ≤ k := le_trans (kap_le n m C.gates) hk
  generalize kap n m C.gates C.gates.length = κ at hsz hcn hκ
  have hs' : C.gates.length ≤ s := hs
  refine ⟨Circuit.mk G (if C.output < n + m + C.gates.length then p C.output
    else n + m + G.length), hm, hrb, hnc, ?_, ?_, ?_⟩
  · show G.length ≤ _
    have h1 : κ * (6 * (C.gates.length + κ * (2 * m + 1)) + 7 * m + 2) ≤
        k * (6 * (s + k * (2 * m + 1)) + 7 * m + 2) :=
      Nat.mul_le_mul hκ (by have := Nat.mul_le_mul_right (2 * m + 1) hκ; omega)
    have h2 : k * (6 * (s + k * (2 * m + 1)) + 7 * m + 2) + 3 * s =
        (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k := by ring
    omega
  · have h1 := ncard_le_cnt n m G
    have h2 := Nat.mul_le_mul_right (2 * m + 1) hκ
    exact le_trans h1 (by omega)
  · intro x Y
    show val G (xy x (fun l => decide (l ∈ Y))) _ =
      (val C.gates (xy x (fun _ : Fin m => false)) C.output ||
        decide (∃ j ∈ Y, val C.gates (xy x (fun l => decide (l = j))) C.output = true))
    rw [linear n m G hm hrb hnc x Y]
    split_ifs with h
    · have hwo := (hw _ h).2.2 x
      simp only [hwo.1, hwo.2]
    · have e1 : ∀ y : Fin m → Bool, val G (xy x y) (n + m + G.length) = false :=
        fun y => val_out _ _ _ (by rw [xy_length])
      have e2 : ∀ y : Fin m → Bool, val C.gates (xy x y) C.output = false :=
        fun y => val_out _ _ _ (by rw [xy_length]; omega)
      simp only [e1, e2]

end P1623

theorem P1623_main : ∀ (n m s k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → ∃ M : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 M ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) M ∧ (∀ j < M.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt M j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs, (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) ∧ M.size ≤ (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k ∧ Set.ncard {j : ℕ | j < M.gates.length ∧ 0 < (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} ≤ s + k * (2 * m + 1) ∧ ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), PEqualNP.MetaComplexity.circuitFun (n + m) M (Fin.append x (fun l => decide (l ∈ Y))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || decide (∃ j ∈ Y, PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = true)) :=
  PEqualNP.Outside.L_meta_3040.SurvivorBound3040.P1623.main
    (fun n m G r => PEqualNP.Outside.L_meta_3040.SurvivorBound3040.P1623.aj_adjoint n m G r)

end Sec1623

section Sec1624

open PEqualNP.CircuitLowerBounds

namespace P1624

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact gate_mono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

def Sv {n : ℕ} {ι : Type*} (C : Circuit) (l : ι → Fin n → Bool) (y : Fin n → Bool)
    (p : ι) (w : ℕ) : Prop :=
  value C (l p) w = true ∧ value C y w = false

def Multi {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool) (w : ℕ) : Prop :=
  ∃ p ∈ T, ∃ p' ∈ T, p ≠ p' ∧ Sv C l y p w ∧ Sv C l y p' w

lemma list_cases (L : List ℕ) (hL : L.length ≤ 2) (Q : ℕ → Prop) :
    (L.length = 2 ∧ ∀ r ∈ L, Q r) ∨ ∃ c, ∀ r ∈ L, Q r → r = c := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
  · exact Or.inr ⟨0, fun r hr => absurd hr (by simp)⟩
  · exact Or.inr ⟨a, fun r hr _ => by simpa using hr⟩
  · by_cases ha : Q a
    · by_cases hb : Q b
      · refine Or.inl ⟨rfl, fun r hr => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · exact ha
        · exact hb
      · refine Or.inr ⟨a, fun r hr hq => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · rfl
        · exact absurd hq hb
    · refine Or.inr ⟨b, fun r hr hq => ?_⟩
      rcases List.mem_pair.mp hr with rfl | rfl
      · exact absurd hq ha
      · rfl
  · simp at hL

lemma step_cases {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < C.gates.length) (hm : Multi C T l y (n + k)) :
    (∃ r ∈ C.gates[k].inputs, r < n + k ∧ ∀ p ∈ T, Sv C l y p (n + k) → Sv C l y p r) ∨
    (C.gates[k].op = GateOp.or ∧ C.gates[k].inputs.length = 2 ∧
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, value C (l p) r = true) ∧
      ∀ p ∈ T, Sv C l y p (n + k) → ∃ r ∈ C.gates[k].inputs, r < n + k ∧ Sv C l y p r) := by
  obtain ⟨p0, hp0, _, _, _, hs0, _⟩ := hm
  rcases (hC _ (List.getElem_mem hk)).1 with hop | hop
  · left
    have hy := hs0.2
    by_contra hcon
    have hall : ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C y r = true := by
      intro r hr
      by_contra hr2
      apply hcon
      have hlt := ((and_value C k hk hop (l p0)).mp hs0.1 r hr).1
      refine ⟨r, hr, hlt, fun p _ hsp => ⟨((and_value C k hk hop (l p)).mp hsp.1 r hr).2, ?_⟩⟩
      by_contra hne
      exact hr2 ⟨hlt, by simpa using hne⟩
    rw [(and_value C k hk hop y).mpr hall] at hy
    exact Bool.noConfusion hy
  · have hyall : ∀ r ∈ C.gates[k].inputs, r < n + k → value C y r = false := by
      intro r hr hlt
      by_contra h
      have h2 : value C y (n + k) = true :=
        (or_value C k hk hop y).mpr ⟨r, hr, hlt, by simpa using h⟩
      rw [hs0.2] at h2
      exact Bool.noConfusion h2
    have hsv : ∀ p ∈ T, Sv C l y p (n + k) →
        ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C (l p) r = true ∧ Sv C l y p r := by
      intro p _ hsp
      obtain ⟨r, hr, hlt, hv⟩ := (or_value C k hk hop (l p)).mp hsp.1
      exact ⟨r, hr, hlt, hv, hv, hyall r hr hlt⟩
    rcases list_cases C.gates[k].inputs (hC _ (List.getElem_mem hk)).2
      (fun r => ∃ p ∈ T, r < n + k ∧ value C (l p) r = true) with ⟨hlen, hQ⟩ | ⟨c, hc⟩
    · right
      refine ⟨hop, hlen, fun r hr => ?_, fun p hp hsp => ?_⟩
      · obtain ⟨p, hp, _, hv⟩ := hQ r hr
        exact ⟨p, hp, hv⟩
      · obtain ⟨r, hr, hlt, _, hs⟩ := hsv p hp hsp
        exact ⟨r, hr, hlt, hs⟩
    · left
      obtain ⟨r, hr, hlt, hv, _⟩ := hsv p0 hp0 hs0
      have hrc := hc r hr ⟨p0, hp0, hlt, hv⟩
      refine ⟨r, hr, hlt, fun p hp hsp => ?_⟩
      obtain ⟨r', hr', hlt', hv', hs'⟩ := hsv p hp hsp
      have hrc' := hc r' hr' ⟨p, hp, hlt', hv'⟩
      rw [hrc, ← hrc']
      exact hs'

lemma frontier {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (W : Finset ℕ)
    (hW : ∀ k, ∀ hk : k < C.gates.length, Multi C T l y (n + k) →
      C.gates[k].op = GateOp.or → C.gates[k].inputs.length = 2 →
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, value C (l p) r = true) → n + k ∈ W)
    (hlen : ∀ w, Multi C T l y w → n ≤ w ∧ w < n + C.gates.length)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, Multi C T l y w → w < t)
    (T' : Finset ι) (hT' : T' ⊆ T) (hs : ∀ p ∈ T', ∃ w ∈ F, Sv C l y p w) :
    T'.card ≤ F.card + (W.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    choose! f hfF hfs using hs
    have hinj : Set.InjOn f T' := by
      intro p hp p' hp' e
      by_contra hne
      have hc : Multi C T l y (f p) :=
        ⟨p, hT' hp, p', hT' hp', hne, hfs p hp, by rw [e]; exact hfs p' hp'⟩
      have := hF (f p) (hfF p hp) hc
      omega
    have := Finset.card_le_card_of_injOn f (fun p hp => hfF p hp) hinj
    omega
  | succ t ih =>
    have hle : (W.filter (· < t)).card ≤ (W.filter (· < t + 1)).card :=
      Finset.card_le_card fun w hw =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
          by have := (Finset.mem_filter.mp hw).2; omega⟩
    by_cases hex : t ∈ F ∧ Multi C T l y t
    · obtain ⟨h1, h2⟩ := hlen t hex.2
      have hk : t - n < C.gates.length := by omega
      have htk : t = n + (t - n) := by omega
      have hm : Multi C T l y (n + (t - n)) := by rw [← htk]; exact hex.2
      have he := Finset.card_erase_add_one hex.1
      rcases step_cases C T l y hC (t - n) hk hm with ⟨r, hr, hlt, hall⟩ | ⟨hop, hlen2, hQ, hsv⟩
      · rw [← htk] at hlt hall
        let F' := insert r (F.erase t)
        have hF' : ∀ w ∈ F', Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_insert.mp hw with hw | hw
          · rw [hw]; exact hlt
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Sv C l y p w := by
          intro p hp
          obtain ⟨w, hw, hsv⟩ := hs p hp
          by_cases h : w = t
          · subst h
            exact ⟨r, Finset.mem_insert_self _ _, hall p (hT' hp) hsv⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h, hw⟩), hsv⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_insert_le r (F.erase t)
        change F'.card ≤ _ at hu
        omega
      · rw [← htk] at hsv
        have htW : t ∈ W := by
          have := hW (t - n) hk hm hop hlen2 hQ
          rwa [← htk] at this
        let P : Finset ℕ := (C.gates[t - n].inputs.filter (· < t)).toFinset
        have hPcard : P.card ≤ 2 := by
          have h1 := List.toFinset_card_le (C.gates[t - n].inputs.filter (· < t))
          have h2 := List.length_filter_le (fun r => decide (r < t)) C.gates[t - n].inputs
          change P.card ≤ _ at h1
          omega
        let F' := F.erase t ∪ P
        have hF' : ∀ w ∈ F', Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_union.mp hw with hw | hw
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
          · have := (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
            simpa using this
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Sv C l y p w := by
          intro p hp
          obtain ⟨w, hw, hsvp⟩ := hs p hp
          by_cases h : w = t
          · subst h
            obtain ⟨r, hr, hlt, hsr⟩ := hsv p (hT' hp) hsvp
            exact ⟨r, Finset.mem_union_right _ (List.mem_toFinset.mpr
              (List.mem_filter.mpr ⟨hr, by simpa using hlt⟩)), hsr⟩
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩), hsvp⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_union_le (F.erase t) P
        change F'.card ≤ _ at hu
        have hfilter : W.filter (· < t + 1) = insert t (W.filter (· < t)) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hg, hlt⟩
            by_cases h : w = t
            · exact Or.inl h
            · exact Or.inr ⟨hg, by omega⟩
          · rintro (rfl | ⟨hg, hlt⟩)
            · exact ⟨htW, by omega⟩
            · exact ⟨hg, by omega⟩
        rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
    · have hF' : ∀ w ∈ F, Multi C T l y w → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      have := ih F hF' hs
      omega

lemma family {n : ℕ} {ι : Type*} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T : Finset ι) (l : ι → Fin n → Bool) (y : Fin n → Bool) (o : ℕ)
    (ho : ∀ p ∈ T, Sv C l y p o)
    (hin : ∀ w, w < n → ¬ Multi C T l y w)
    (K : Finset (Fin C.gates.length))
    (hK : ∀ g : Fin C.gates.length, Multi C T l y (n + (g : ℕ)) → g ∈ K) :
    T.card ≤ K.card + 1 := by
  classical
  let W : Finset ℕ := Finset.image (fun g : Fin C.gates.length => n + (g : ℕ)) K
  have hlen : ∀ w, Multi C T l y w → n ≤ w ∧ w < n + C.gates.length := by
    intro w hc
    refine ⟨Nat.le_of_not_lt fun h => hin w h hc, ?_⟩
    by_contra hge
    obtain ⟨p, _, _, _, _, hsv, _⟩ := hc
    have hm := missing_value C (l p) w (by unfold Circuit.size; omega)
    have h1 := hsv.1
    rw [hm] at h1
    exact Bool.noConfusion h1
  have h := frontier C T l y hC W
    (fun k hk hm _ _ _ => Finset.mem_image.mpr ⟨(⟨k, hk⟩ : Fin C.gates.length), hK ⟨k, hk⟩ hm, rfl⟩)
    hlen (n + C.gates.length) {o}
    (fun w _ hc => (hlen w hc).2) T (Finset.Subset.refl T)
    (fun p hp => ⟨o, Finset.mem_singleton_self o, ho p hp⟩)
  have h1 := Finset.card_filter_le W (· < n + C.gates.length)
  have h2 : W.card ≤ K.card := Finset.card_image_le
  rw [Finset.card_singleton] at h
  omega

lemma main : ∀ (n m : ℕ) (L A : Fin m → Finset (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.NestedCover.ReadsBack n D → (∀ j : Fin m, A j ⊆ L j) → (∀ (j : Fin m) (p : Fin n), p ∈ A j → (D.wires (List.ofFn (fun i : Fin n => decide (i = p)))).getD (o j) false = true) → (∀ j : Fin m, (D.wires (List.ofFn (fun i : Fin n => decide (i ∉ L j)))).getD (o j) false = false) → ∑ j : Fin m, ((A j).card - 1) ≤ D.size := by
  classical
  intro n m L A D o hint hmono _ hAL htrue hfalse
  have hC : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h := hmono g hg
    refine ⟨?_, h.2⟩
    rcases h.1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  let l : Fin n → Fin n → Bool := fun p i => decide (i = p)
  let y : Fin m → Fin n → Bool := fun j i => decide (i ∉ L j)
  let K : Fin m → Finset (Fin D.gates.length) := fun j =>
    Finset.univ.filter fun g => Multi D (A j) l (y j) (n + (g : ℕ))
  have hK : ∀ j, (A j).card ≤ (K j).card + 1 := by
    intro j
    refine family D hC (A j) l (y j) (o j) (fun p hp => ⟨htrue j p hp, hfalse j⟩) ?_ (K j)
      (fun g hm => Finset.mem_filter.mpr ⟨Finset.mem_univ g, hm⟩)
    rintro w hw ⟨p, _, p', _, hne, hs1, hs2⟩
    have e1 : l p ⟨w, hw⟩ = true := (input_value D (l p) ⟨w, hw⟩).symm.trans hs1.1
    have e2 : l p' ⟨w, hw⟩ = true := (input_value D (l p') ⟨w, hw⟩).symm.trans hs2.1
    exact hne ((of_decide_eq_true e1).symm.trans (of_decide_eq_true e2))
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (K i) (K j) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun g hgi hgj => ?_
    obtain ⟨a, ha, b, hb, hab, hsa, hsb⟩ := (Finset.mem_filter.mp hgi).2
    obtain ⟨c, _, _, _, _, hsc, _⟩ := (Finset.mem_filter.mp hgj).2
    have hyj : value D (y j) (n + (g : ℕ)) = false := hsc.2
    have key : ∀ p : Fin n, value D (l p) (n + (g : ℕ)) = true → p ∈ L j := by
      intro p hv
      by_contra hn
      have h2 := mono D hC (l p) (y j) (fun v hv' => by
        have hvp : v = p := of_decide_eq_true hv'
        rw [hvp]
        exact decide_eq_true hn) _ hv
      exact Bool.noConfusion (hyj.symm.trans h2)
    exact hab (Finset.card_le_one.mp (hint i j hij) a
      (Finset.mem_inter.mpr ⟨hAL i ha, key a hsa.1⟩) b
      (Finset.mem_inter.mpr ⟨hAL i hb, key b hsb.1⟩))
  have h1 : ∑ j : Fin m, ((A j).card - 1) ≤ ∑ j : Fin m, (K j).card :=
    Finset.sum_le_sum fun j _ => by
      have := hK j
      omega
  rw [← Finset.card_biUnion hd] at h1
  have h2 := Finset.card_le_univ (Finset.univ.biUnion K)
  rw [Fintype.card_fin] at h2
  exact h1.trans h2

end P1624

theorem P1624_main : ∀ (n m : ℕ) (L A : Fin m → Finset (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.NestedCover.ReadsBack n D → (∀ j : Fin m, A j ⊆ L j) → (∀ (j : Fin m) (p : Fin n), p ∈ A j → (D.wires (List.ofFn (fun i : Fin n => decide (i = p)))).getD (o j) false = true) → (∀ j : Fin m, (D.wires (List.ofFn (fun i : Fin n => decide (i ∉ L j)))).getD (o j) false = false) → ∑ j : Fin m, ((A j).card - 1) ≤ D.size :=
  PEqualNP.Outside.L_meta_3040.SurvivorBound3040.P1624.main

end Sec1624

theorem glue (h22 : (∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧ D.size ≤ C.size + 3 * Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} + m ∧ ∀ (x : Fin n → Bool) (j : Fin m), PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || (D.wires (List.ofFn x)).getD (o j) false))) (h23 : (∀ (n m s k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → ∃ M : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 M ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) M ∧ (∀ j < M.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt M j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs.length = 2 → ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt M j).inputs, (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0 = 0) ∧ M.size ≤ (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k ∧ Set.ncard {j : ℕ | j < M.gates.length ∧ 0 < (M.lineDegrees (n + m) (Finset.Ico n (n + m))).getD (n + m + j) 0} ≤ s + k * (2 * m + 1) ∧ ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), PEqualNP.MetaComplexity.circuitFun (n + m) M (Fin.append x (fun l => decide (l ∈ Y))) = (PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun _ => false)) || decide (∃ j ∈ Y, PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) = true)))) (h24 : (∀ (n m : ℕ) (L A : Fin m → Finset (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.NestedCover.ReadsBack n D → (∀ j : Fin m, A j ⊆ L j) → (∀ (j : Fin m) (p : Fin n), p ∈ A j → (D.wires (List.ofFn (fun i : Fin n => decide (i = p)))).getD (o j) false = true) → (∀ j : Fin m, (D.wires (List.ofFn (fun i : Fin n => decide (i ∉ L j)))).getD (o j) false = false) → ∑ j : Fin m, ((A j).card - 1) ≤ D.size)) : (∀ (n m s k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ L j, x p = true) → (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card ≤ (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k) := by
  intro n m s k L C hL hmono hrb hs hk hsound
  obtain ⟨M, hMm, hMrb, hMx, hMs, hMt, hMf⟩ := h23 n m s k C hmono hrb hs hk
  obtain ⟨D, o, hDm, hDrb, hDs, hDf⟩ := h22 n m M hMm hMrb hMx
  have hC0 : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append x (fun _ => false)) = false := by
    intro x
    by_contra hne
    have h1 := hsound x ∅ (by simp) (by simpa using hne)
    obtain ⟨j, hj, _⟩ := h1
    simp at hj
  have hM1 : ∀ (x : Fin n → Bool) (j : Fin m), PEqualNP.MetaComplexity.circuitFun (n + m) M
      (Fin.append x (fun l => decide (l = j))) = PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append x (fun l => decide (l = j))) := by
    intro x j
    have h1 := hMf x {j}
    simp only [Finset.mem_singleton, exists_eq_left] at h1
    rw [h1, hC0]
    simp
  have hM0 : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + m) M
      (Fin.append x (fun _ => false)) = false := by
    intro x
    have h1 := hMf x ∅
    simp only [Finset.notMem_empty, decide_false, false_and, exists_false, Bool.or_false] at h1
    rw [h1, hC0]
  have hD : ∀ (x : Fin n → Bool) (j : Fin m), (D.wires (List.ofFn x)).getD (o j) false =
      PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l = j))) := by
    intro x j
    have h1 := hDf x j
    rw [hM1, hM0, Bool.false_or] at h1
    exact h1.symm
  have h := h24 n m L (fun j => (L j).filter (fun p => PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append (fun i => decide (i = p)) (fun l => decide (l = j))) = true)) D o hL hDm hDrb
    (fun j => Finset.filter_subset _ _)
    (by
      intro j p hp
      rw [hD]
      exact (Finset.mem_filter.mp hp).2)
    (by
      intro j
      rw [hD]
      by_contra hne
      have h1 := hsound (fun i : Fin n => decide (i ∉ L j)) {j} (by simp)
        (by
          have h2 : (fun l : Fin m => decide (l ∈ ({j} : Finset (Fin m)))) = fun l => decide (l = j) := by
            funext l
            simp
          rw [h2]
          simpa using hne)
      obtain ⟨j', hj', p, hp, hx⟩ := h1
      rw [Finset.mem_singleton] at hj'
      subst hj'
      simp [hp] at hx)
  have hcard : (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧
      PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1))
        (fun l => decide (l = e.2))) = true)).card ≤
      ∑ j : Fin m, ((L j).filter (fun p => PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append (fun i => decide (i = p)) (fun l => decide (l = j))) = true)).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn (fun e => ⟨e.2, e.1⟩) ?_ ?_
    · intro e he
      have he' := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
      exact Finset.mem_coe.mpr (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr he'⟩)
    · intro a _ b _ hab
      simp only [Sigma.mk.injEq, heq_eq_eq] at hab
      exact Prod.ext hab.2 hab.1
  have hsum : ∑ j : Fin m, ((L j).filter (fun p => PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append (fun i => decide (i = p)) (fun l => decide (l = j))) = true)).card ≤
      ∑ j : Fin m, (((L j).filter (fun p => PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append (fun i => decide (i = p)) (fun l => decide (l = j))) = true)).card - 1) + m := by
    have h1 : ∀ j ∈ (Finset.univ : Finset (Fin m)), ((L j).filter (fun p => PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append (fun i => decide (i = p)) (fun l => decide (l = j))) = true)).card ≤
      (((L j).filter (fun p => PEqualNP.MetaComplexity.circuitFun (n + m) C
      (Fin.append (fun i => decide (i = p)) (fun l => decide (l = j))) = true)).card - 1) + 1 := by
      intro j _
      omega
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_add_distrib] at h2
    simpa using h2
  have hDs' : D.size ≤ (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k +
      3 * (s + k * (2 * m + 1)) + m := by
    have h3 := Nat.mul_le_mul_left 3 hMt
    omega
  have hfin : (6 * k + 3) * s + 12 * k ^ 2 * m + 7 * k * m + 6 * k ^ 2 + 2 * k +
      3 * (s + k * (2 * m + 1)) + m + m = (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k := by
    ring
  omega

theorem survivorBound : ∀ (n m s k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ L j, x p = true) → (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card ≤ (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k :=
  PEqualNP.Outside.L_meta_3040.SurvivorBound3040.glue PEqualNP.Outside.L_meta_3040.SurvivorBound3040.P1622_main PEqualNP.Outside.L_meta_3040.SurvivorBound3040.P1623_main PEqualNP.Outside.L_meta_3040.SurvivorBound3040.P1624_main

end SurvivorBound3040

namespace L3040Aux


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- The gate and list sanitization below adapts the corresponding private lemmas from L-meta-25534.
private def cleanGate (cur : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.or => ⟨GateOp.or, g.inputs.filter (fun i => decide (i < cur))⟩
  | GateOp.and => if g.inputs.all (fun i => decide (i < cur)) then g else ⟨GateOp.or, []⟩
  | _ => g

private def cleanGates (cur : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => cleanGate cur g :: cleanGates (cur + 1) gs

private theorem cleanGates_length (cur : ℕ) (gs : List Gate) :
    (cleanGates cur gs).length = gs.length := by
  induction gs generalizing cur with
  | nil => rfl
  | cons g gs ih => simp [cleanGates, ih]

private theorem cleanGate_mono2 (cur : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (cleanGate cur g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (cleanGate cur g).inputs.length ≤ 2 := by
  rcases hg with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop
  · rw [cleanGate, hop]
    split_ifs
    · exact ⟨by simp [hop], hlen⟩
    · exact ⟨by simp, by simp⟩
  · rw [cleanGate, hop]
    refine ⟨by simp, ?_⟩
    exact le_trans (List.length_filter_le _ _) hlen

private theorem cleanGates_mono2 (cur : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ cleanGates cur gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing cur with
  | nil => intro g hg; simp [cleanGates] at hg
  | cons g gs ih =>
    intro g' hg'
    simp only [cleanGates, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · exact cleanGate_mono2 cur g (hgs g (by simp))
    · exact ih (cur + 1) (fun g'' h => hgs g'' (by simp [h])) g' hg'

private theorem cleanGate_wf (cur : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ i ∈ (cleanGate cur g).inputs, i < cur := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop
  · rw [cleanGate, hop]
    split_ifs with hall
    · intro i hi
      simp only [List.all_eq_true, decide_eq_true_iff] at hall
      exact hall i hi
    · intro i hi; simp at hi
  · rw [cleanGate, hop]
    intro i hi
    simp only [List.mem_filter, decide_eq_true_iff] at hi
    exact hi.2

private theorem cleanGates_wf (cur : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ j (hj : j < (cleanGates cur gs).length), ∀ i ∈ ((cleanGates cur gs)[j]).inputs, i < cur + j := by
  induction gs generalizing cur with
  | nil => intro j hj; simp [cleanGates] at hj
  | cons g gs ih =>
    intro j hj
    cases j with
    | zero =>
      simp only [cleanGates, List.getElem_cons_zero, Nat.add_zero]
      exact cleanGate_wf cur g (hgs g (by simp))
    | succ j =>
      simp only [cleanGates, List.getElem_cons_succ]
      intro i hi
      have h1 := ih (cur + 1) (fun g' h => hgs g' (by simp [h])) j (by simpa [cleanGates] using hj) i hi
      omega

private theorem cleanGate_eval (w : List Bool) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    (cleanGate w.length g).op.eval ((cleanGate w.length g).inputs.map (fun i => w.getD i false)) =
      g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop
  · by_cases hall : (g.inputs.all fun i => decide (i < w.length)) = true
    · simp only [cleanGate, hop, ite_eq_left hall]
    · simp only [cleanGate, hop, ite_eq_right hall, GateOp.eval, List.map_nil, List.any_nil,
        List.all_map, Function.comp_apply, id]
      symm
      rw [Bool.eq_false_iff]
      intro htrue
      rw [List.all_eq_true] at htrue
      simp only [List.all_eq_true, decide_eq_true_iff, not_forall] at hall
      obtain ⟨i, hi, hge⟩ := hall
      have h1 : w.getD i false = true := by simpa using htrue i hi
      have h2 := List.getD_eq_default w false (Nat.not_lt.1 hge)
      rw [h2] at h1
      exact Bool.noConfusion h1
  · simp only [cleanGate, hop, GateOp.eval, List.any_map, Function.comp_apply, id]
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true, List.mem_filter, decide_eq_true_iff, Function.comp_apply, id_eq]
    constructor
    · rintro ⟨i, ⟨hi, _⟩, hwi⟩
      exact ⟨i, hi, hwi⟩
    · rintro ⟨i, hi, hwi⟩
      refine ⟨i, ⟨hi, ?_⟩, hwi⟩
      by_contra hge
      have h2 := List.getD_eq_default w false (Nat.not_lt.1 hge)
      rw [h2] at hwi
      exact Bool.noConfusion hwi

private theorem cleanGates_wires (gs : List Gate)
    (allowed : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (w : List Bool) :
    (Circuit.mk (cleanGates w.length gs) 0).wires w = (Circuit.mk gs 0).wires w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have op := allowed g (List.mem_cons_self ..)
    let next := w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
    change (Circuit.mk (cleanGates (w.length + 1) gs) 0).wires
      (w ++ [(cleanGate w.length g).op.eval
        ((cleanGate w.length g).inputs.map (fun i => w.getD i false))]) =
        (Circuit.mk gs 0).wires next
    rw [cleanGate_eval w g op]
    have width : w.length + 1 = next.length := by simp [next]
    rw [width]
    exact ih (fun g hg => allowed g (List.mem_cons_of_mem _ hg)) next

private theorem cleanMonotone (m : ℕ) (C : Circuit) (mono : Monotone2 C) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack m D ∧
      circuitFun m D = circuitFun m C ∧ D.size = C.size := by
  let D : Circuit := ⟨cleanGates m C.gates, C.output⟩
  have allowed := fun g (here : g ∈ C.gates) => (mono g here).1
  refine ⟨D, cleanGates_mono2 m C.gates mono, ?_, ?_, ?_⟩
  · intro j hj i hi
    have gate : gateAt D j = (cleanGates m C.gates)[j]'hj := by
      simp [gateAt, D, List.getD_eq_getElem?_getD, hj]
    rw [gate] at hi
    exact cleanGates_wf m C.gates allowed j hj i hi
  · funext x
    have wires := cleanGates_wires C.gates allowed (List.ofFn x)
    simp only [List.length_ofFn] at wires
    exact congrArg (fun values => values.getD C.output false) wires
  · exact cleanGates_length m C.gates

/-- A globally minimum monotone circuit can be chosen with only backward reads. -/
theorem minimalReadsBack (m : ℕ) (C : Circuit) (mono : Monotone2 C) :
    ∃ D, IsMinimalMonoCircuit m D ∧ ReadsBack m D ∧
      circuitFun m D = circuitFun m C ∧ D.size ≤ C.size := by
  classical
  let candidate (k : ℕ) :=
    ∃ Q : Circuit, Monotone2 Q ∧ circuitFun m Q = circuitFun m C ∧ Q.size = k
  have existsSize : ∃ k, candidate k := ⟨C.size, C, mono, rfl, rfl⟩
  obtain ⟨Q, monoQ, funQ, sizeQ⟩ := Nat.find_spec existsSize
  obtain ⟨D, monoD, backD, funD, sizeD⟩ := cleanMonotone m Q monoQ
  have same : circuitFun m D = circuitFun m C := funD.trans funQ
  have minimal : IsMinimalMonoCircuit m D := by
    refine ⟨monoD, ?_⟩
    intro R monoR funR
    have eligible : candidate R.size := ⟨R, monoR, funR.trans same, rfl⟩
    exact sizeD.le.trans (sizeQ.le.trans (Nat.find_min' existsSize eligible))
  have initial : candidate C.size := ⟨C, mono, rfl, rfl⟩
  exact ⟨D, minimal, backD, same, sizeD.le.trans (sizeQ.le.trans (Nat.find_min' existsSize initial))⟩

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private def cut3040Gate (n : Nat) (C : Circuit) (g : Gate) : Gate :=
  if g.op.eval [] = true ∧ g.inputs.length = 2 ∧
      (g.inputs.all fun i => decide (0 < (C.lineDegrees (n+n) (Finset.Ico n (n+n))).getD i 0)) = true
    then ⟨.or, []⟩ else g

def cut3040 (n : Nat) (C : Circuit) : Circuit :=
  ⟨C.gates.map (cut3040Gate n C), C.output⟩

private theorem cut3040_getD_le {a b : List Nat}
    (related : List.Forall₂ (· ≤ ·) a b) (i : Nat) : a.getD i 0 ≤ b.getD i 0 := by
  by_cases ha : i < a.length
  · have hb : i < b.length := related.length_eq ▸ ha
    rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]
    exact related.get ha hb
  · have hb : b.length ≤ i := related.length_eq ▸ Nat.le_of_not_gt ha
    rw [List.getD_eq_default _ _ (Nat.le_of_not_gt ha), List.getD_eq_default _ _ hb]

private theorem cut3040_gateDegree_le (g : Gate) {a b : List Nat}
    (related : List.Forall₂ (· ≤ ·) a b) : g.lineDegree a ≤ g.lineDegree b := by
  have bounds (inputs : List Nat) :
      ((inputs.map fun i => a.getD i 0).sum ≤ (inputs.map fun i => b.getD i 0).sum) ∧
      ((inputs.map fun i => a.getD i 0).foldr max 0 ≤
        (inputs.map fun i => b.getD i 0).foldr max 0) := by
    induction inputs with
    | nil => simp
    | cons i inputs ih =>
      exact ⟨Nat.add_le_add (cut3040_getD_le related i) ih.1,
        max_le_max (cut3040_getD_le related i) ih.2⟩
  unfold Gate.lineDegree
  split
  · exact (bounds g.inputs).1
  · exact (bounds g.inputs).2

private theorem cut3040_fold_le (n : Nat) (C : Circuit) (gs : List Gate) {a b : List Nat}
    (related : List.Forall₂ (· ≤ ·) a b) :
    List.Forall₂ (· ≤ ·)
      ((gs.map (cut3040Gate n C)).foldl (fun d g => d ++ [g.lineDegree d]) a)
      (gs.foldl (fun d g => d ++ [g.lineDegree d]) b) := by
  induction gs generalizing a b with
  | nil => exact related
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    apply List.rel_append related
    refine List.Forall₂.cons ?_ List.Forall₂.nil
    unfold cut3040Gate
    split
    · have emptyDegree : (⟨.or, []⟩ : Gate).lineDegree a = 0 := by
        unfold Gate.lineDegree
        split <;> rfl
      rw [emptyDegree]
      exact Nat.zero_le _
    · exact cut3040_gateDegree_le g related

private theorem cut3040_lineDegrees_le (n : Nat) (C : Circuit) (i : Nat) :
    ((cut3040 n C).lineDegrees (n+n) (Finset.Ico n (n+n))).getD i 0 ≤
      (C.lineDegrees (n+n) (Finset.Ico n (n+n))).getD i 0 := by
  unfold Circuit.lineDegrees cut3040
  exact cut3040_getD_le (cut3040_fold_le n C C.gates (List.forall₂_refl _)) i

private theorem cut3040_gateAt (n : Nat) (C : Circuit) (j : Nat) :
    gateAt (cut3040 n C) j = cut3040Gate n C (gateAt C j) := by
  exact List.getD_map C.gates ⟨.or, []⟩ (n := j) (cut3040Gate n C)

theorem cut3040_crossZero (n : Nat) (C : Circuit) (_mono : Monotone2 C) :
    Set.ncard {j : Nat | j < (cut3040 n C).gates.length ∧
      (gateAt (cut3040 n C) j).op = .and ∧
      (gateAt (cut3040 n C) j).inputs.length = 2 ∧
      ∀ i ∈ (gateAt (cut3040 n C) j).inputs,
        0 < ((cut3040 n C).lineDegrees (n+n) (Finset.Ico n (n+n))).getD i 0} ≤ 0 := by
  calc
    _ = (∅ : Set Nat).ncard := by
      congr 1
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro j h
      change _ ∧ _ ∧ _ ∧ _ at h
      rw [cut3040_gateAt, cut3040Gate] at h
      split at h
      · exact GateOp.noConfusion h.2.1
      · rename_i notCut
        apply notCut
        refine ⟨?_, h.2.2.1, List.all_eq_true.mpr ?_⟩
        · rw [h.2.1]
          rfl
        · intro i hi
          exact decide_eq_true ((h.2.2.2 i hi).trans_le (cut3040_lineDegrees_le n C i))
    _ ≤ 0 := by simp

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private def cut3040Select (selected : Gate → Prop) [DecidablePred selected] (g : Gate) : Gate :=
  if selected g then ⟨.or, []⟩ else g

private def cut3040Step (values : List Bool) (g : Gate) : List Bool :=
  values ++ [g.op.eval (g.inputs.map fun i => values.getD i false)]

private theorem cut3040GetD {u v : List Bool} (h : List.Forall₂ (· ≤ ·) u v) (i : Nat) :
    u.getD i false ≤ v.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hHead _ ih =>
    cases i with
    | zero => simpa [List.getD_eq_getElem?_getD] using hHead
    | succ i => simpa [List.getD_eq_getElem?_getD] using ih i

private theorem cut3040SelectValue (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    {u v : List Bool} (h : List.Forall₂ (· ≤ ·) u v) :
    g.op.eval (g.inputs.map fun i => u.getD i false) ≤
      g.op.eval (g.inputs.map fun i => v.getD i false) := by
  apply Bool.le_iff_imp.mpr
  intro hu
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, Function.comp_apply, id_eq, List.all_eq_true] at hu ⊢
    intro i hi
    exact Bool.le_iff_imp.mp (cut3040GetD h i) (hu i hi)
  · simp only [hop, GateOp.eval, List.any_map, Function.comp_apply, id_eq, List.any_eq_true] at hu ⊢
    obtain ⟨i, hi, hv⟩ := hu
    exact ⟨i, hi, Bool.le_iff_imp.mp (cut3040GetD h i) hv⟩

private theorem cut3040Fold {selected : Gate → Prop} [DecidablePred selected]
    (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (u v : List Bool) (h : List.Forall₂ (· ≤ ·) u v) :
    List.Forall₂ (· ≤ ·)
      ((gs.map (cut3040Select selected)).foldl cut3040Step u)
      (gs.foldl cut3040Step v) := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih (fun gate hg => hgs gate (List.mem_cons_of_mem _ hg))
    apply List.rel_append h
    apply List.Forall₂.cons _ List.Forall₂.nil
    by_cases hg : selected g
    · simp [cut3040Select, hg, GateOp.eval]
    · simpa [cut3040Select, hg] using cut3040SelectValue g (hgs g (by simp)) h

private theorem cut3040MapSpec (m : Nat) (C : Circuit) (selected : Gate → Prop)
    [DecidablePred selected] (mono : Monotone2 C) (back : ReadsBack m C) :
    let D : Circuit := ⟨C.gates.map (cut3040Select selected), C.output⟩
    Monotone2 D ∧ ReadsBack m D ∧ D.size = C.size ∧
      ∀ x, circuitFun m D x = true → circuitFun m C x = true := by
  let D : Circuit := ⟨C.gates.map (cut3040Select selected), C.output⟩
  change Monotone2 D ∧ ReadsBack m D ∧ D.size = C.size ∧
    ∀ x, circuitFun m D x = true → circuitFun m C x = true
  refine ⟨?_, ?_, by simp [D, Circuit.size], ?_⟩
  · intro gate hGate
    obtain ⟨g, hSource, rfl⟩ := List.mem_map.mp hGate
    by_cases hc : selected g
    · simp [cut3040Select, hc]
    · simpa [cut3040Select, hc] using mono g hSource
  · intro j hj i hi
    have hjC : j < C.gates.length := by simpa [D] using hj
    have hmap : gateAt D j = cut3040Select selected (gateAt C j) := by
      simp [D, gateAt, List.getD_eq_getElem?_getD, hjC]
    rw [hmap] at hi
    by_cases hc : selected (gateAt C j)
    · simp [cut3040Select, hc] at hi
    · exact back j hjC i (by simpa [cut3040Select, hc] using hi)
  · intro x hx
    have hall : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := fun g hg => by
      simpa using (mono g hg).1
    have h := cut3040Fold (selected := selected) C.gates hall (List.ofFn x) (List.ofFn x) (by simp)
    exact Bool.le_iff_imp.mp (cut3040GetD h C.output) hx

theorem cut3040_spec (n : Nat) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack (n + n) C) :
    Monotone2 (cut3040 n C) ∧ ReadsBack (n + n) (cut3040 n C) ∧
      (cut3040 n C).size = C.size ∧
      ∀ x, circuitFun (n + n) (cut3040 n C) x = true → circuitFun (n + n) C x = true := by
  unfold cut3040
  exact cut3040MapSpec (n + n) C
    (fun g => g.op.eval [] = true ∧ g.inputs.length = 2 ∧
      (g.inputs.all fun i => decide (0 < (C.lineDegrees (n + n) (Finset.Ico n (n + n))).getD i 0)) = true)
    mono back

end L3040Aux


def Claim : Prop :=
  ¬ (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (2 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →             have x11 : Finset (Fin x2) → Fin (x2 + x2) → Bool := fun (x11 : Finset (Fin x2)) (x12 : Fin (x2 + x2)) => Fin.addCases (fun (x13 : Fin x2) => Decidable.decide ¬∃ x14 ∈ x11, x3 x13 x14) (fun (x13 : Fin x2) => Decidable.decide (x13 ∈ x11)) x12;             (∀ (x12 : Finset (Fin x2)), x12.card ≤ x1 → x5.eval (List.ofFn (x11 x12)) = Bool.false) →               have x13 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => if x13.op.eval [] = Bool.true ∧ x13.inputs.length = (2 : ℕ) ∧ (x13.inputs.all fun (x14 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x14 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x13) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };               have x14 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x14 x15 : Fin x2) (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x14 ∨ x16 = Fin.natAdd x2 x15);               ∀ (x15 : Fin x2 → Finset (Fin x2)), (∀ (x16 x17 : Fin x2), x17 ∈ x15 x16 → x3 x17 x16 ∧ x5.eval (List.ofFn (x14 x17 x16)) = Bool.true ∧ x13.eval (List.ofFn (x14 x17 x16)) = Bool.false) → ∑ x17 : Fin x2, (x15 x17).card ≤ (44 : ℕ) * Fintype.card { x17 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x17) Bool.false = Bool.false ∧ ∃ (x18 : Fin x2), ∃ x19 ∈ x15 x18, (x5.wires (List.ofFn (x14 x19 x18))).getD (x2 + x2 + ↑x17) Bool.false = Bool.true })

open Refute2003 L3040Aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection
open scoped BigOperators

theorem solveCutClaim : Claim := by
  classical
  intro wouldBound
  obtain ⟨q,n,s,S,P,w,hq,hn,degree,joins,promised,small⟩ :=
    Refute2003.OuterConcrete.promisedCircuit
  let base := P.toCircuit w
  have monoBase : Monotone2 base := by
    intro g hg
    have shape := P.gate_ops g hg
    refine ⟨?_,shape.2.le⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using shape.1
  obtain ⟨C,minimal,back,same,sizeLe⟩ := minimalReadsBack (n+n) base monoBase
  let D := cut3040 n C
  obtain ⟨monoD,backD,sizeD,preserved⟩ := cut3040_spec n C minimal.1 back
  have chosenSize : C.size ≤ s := sizeLe.trans (P.size_toCircuit w).le
  let I : Fin n → Fin n → Prop := fun p l => p ∈ S l
  letI di : DecidableRel I := fun p l => inferInstanceAs (Decidable (p ∈ S l))
  have degreeI (l : Fin n) : Fintype.card {p // I p l} = q+1 := by
    rw [Fintype.card_subtype]
    have fiber : Finset.univ.filter (fun p => I p l) = S l := by
      ext p
      simp [I]
    rw [fiber,degree l]
  have intersection (l r : Fin n) (different : l ≠ r) : (S l ∩ S r).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp z hz
    by_contra ne
    obtain ⟨a,_,unique⟩ := joins p z ne
    have left := unique l ⟨(Finset.mem_inter.mp hp).1,(Finset.mem_inter.mp hz).1⟩
    have right := unique r ⟨(Finset.mem_inter.mp hp).2,(Finset.mem_inter.mp hz).2⟩
    exact different (left.trans right.symm)
  have correct (X Y : Finset (Fin n)) (few : Y.card ≤ q) :
      circuitFun (n+n) C (input X Y) = incidenceFun S X Y := by
    rw [same]
    exact (P.toCircuit_eval (input X Y) w).trans (promised X Y few)
  have soundCut (x : Fin n → Bool) (Y : Finset (Fin n)) (few : Y.card ≤ 1)
      (on : circuitFun (n+n) D (Fin.append x (fun l => decide (l ∈ Y))) = true) :
      ∃ l ∈ Y, ∃ p ∈ S l, x p = true := by
    let X := Finset.univ.filter (fun p => x p = true)
    have sameInput : Fin.append x (fun l => decide (l ∈ Y)) = input X Y := by
      unfold input
      congr 1
      funext p
      apply Bool.eq_iff_iff.mpr
      simp [X]
    have onOrig : circuitFun (n+n) C (input X Y) = true := by
      rw [← sameInput]
      exact preserved _ on
    have both : incidenceFun S X Y = true :=
      (correct X Y (few.trans (by omega))).symm.trans onOrig
    obtain ⟨p,hp,l,hl,incident⟩ := of_decide_eq_true both
    exact ⟨l,hl,p,incident,(Finset.mem_filter.mp hp).2⟩
  let hardInput (Y : Finset (Fin n)) : Fin (n+n) → Bool :=
    Fin.addCases (fun p : Fin n => decide (¬∃ l ∈ Y, I p l))
      (fun l : Fin n => decide (l ∈ Y))
  have reject (Y : Finset (Fin n)) (few : Y.card ≤ q) :
      C.eval (List.ofFn (hardInput Y)) = false := by
    let X := Finset.univ.filter (fun p => ¬∃ l ∈ Y, I p l)
    have sameInput : hardInput Y = input X Y := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro p
        simp only [hardInput, Fin.addCases_left, input, Fin.append_left]
        apply Bool.eq_iff_iff.mpr
        simp [X]
      · intro l
        simp only [hardInput, Fin.addCases_right, input, Fin.append_right]
    have miss : IsFalseInput S X Y := by
      intro l hl
      apply Finset.disjoint_left.mpr
      intro p hp hx
      exact (Finset.mem_filter.mp hx).2 ⟨l,hl,hp⟩
    change circuitFun (n+n) C (hardInput Y) = false
    rw [sameInput,correct X Y few,incidenceFun_false miss]
  let pair (p l : Fin n) : Fin (n+n) → Bool :=
    fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)
  have toPair (p l : Fin n) : input {p} {l} = pair p l := input_pair p l
  have keepCount := SurvivorBound3040.survivorBound n n C.size 0 S D intersection
    monoD backD sizeD.le (cut3040_crossZero n C minimal.1) soundCut
  let kept (l : Fin n) := (S l).filter (fun p => circuitFun (n+n) D (input {p} {l}) = true)
  let lost (l : Fin n) := (S l).filter (fun p => ¬ circuitFun (n+n) D (input {p} {l}) = true)
  have fibers :
      (Finset.univ.filter (fun e : Fin n × Fin n => e.1 ∈ S e.2 ∧
        circuitFun (n+n) D (input {e.1} {e.2}) = true)).card =
      ∑ l : Fin n, (kept l).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun e _ => (⟨e.2,e.1⟩ : Σ _ : Fin n, Fin n)) ?_ ?_ ?_
    · intro e he
      have h := (Finset.mem_filter.mp he).2
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,Finset.mem_filter.mpr h⟩
    · intro a _ b _ ab
      simp only [Sigma.mk.injEq,heq_eq_eq] at ab
      exact Prod.ext ab.2 ab.1
    · intro z hz
      have h := Finset.mem_filter.mp (Finset.mem_sigma.mp hz).2
      exact ⟨(z.2,z.1),Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,by cases z; rfl⟩
  have survivorLimit : ∑ l : Fin n, (kept l).card ≤ 6*C.size+2*n := by
    rw [← fibers]
    simpa only [Refute2003.input,Finset.mem_singleton, zero_mul, mul_zero, zero_add,
      show (0 : ℕ)^2 = 0 from rfl, add_zero] using keepCount
  have partition : (∑ l : Fin n, (kept l).card) + (∑ l : Fin n, (lost l).card) = n*(q+1) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ l : Fin n, (S l).card := by
        apply Finset.sum_congr rfl
        intro l _
        exact Finset.card_filter_add_card_filter_not
          (fun p => circuitFun (n+n) D (input {p} {l}) = true)
      _ = _ := by simp [degree]
  have marked (l p : Fin n) (hp : p ∈ lost l) :
      I p l ∧ C.eval (List.ofFn (pair p l)) = true ∧ D.eval (List.ofFn (pair p l)) = false := by
    obtain ⟨incident,off⟩ := Finset.mem_filter.mp hp
    refine ⟨incident,?_,?_⟩
    · change circuitFun (n+n) C (pair p l) = true
      rw [← toPair,correct _ _ (by simp; omega),incidenceFun_pair_true incident]
    · change circuitFun (n+n) D (pair p l) = false
      rw [← toPair]
      cases h : circuitFun (n+n) D (input {p} {l})
      · rfl
      · exact False.elim (off h)
  have limit := @wouldBound q n I di C (by omega) hn degreeI joins minimal reject lost marked
  have subtypeBound (p : Fin C.size → Prop) [Fintype {i // p i}] :
      Fintype.card {i // p i} ≤ C.size := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective (fun x : {i // p i} => x.val) Subtype.val_injective
  have lossLimit : ∑ l : Fin n, (lost l).card ≤ 44*C.size := by
    exact limit.trans (Nat.mul_le_mul_left 44 (subtypeBound _))
  have nSmall : 2*n ≤ n*q := by
    rw [Nat.mul_comm 2 n]
    exact Nat.mul_le_mul_left n (by omega)
  rw [Nat.mul_add,Nat.mul_one] at partition
  omega

end PEqualNP.Outside.L_meta_3040

theorem PEqualNP.Outside.L_meta_3040 :
  ¬ (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (2 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →             have x11 : Finset (Fin x2) → Fin (x2 + x2) → Bool := fun (x11 : Finset (Fin x2)) (x12 : Fin (x2 + x2)) => Fin.addCases (fun (x13 : Fin x2) => Decidable.decide ¬∃ x14 ∈ x11, x3 x13 x14) (fun (x13 : Fin x2) => Decidable.decide (x13 ∈ x11)) x12;             (∀ (x12 : Finset (Fin x2)), x12.card ≤ x1 → x5.eval (List.ofFn (x11 x12)) = Bool.false) →               have x13 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => if x13.op.eval [] = Bool.true ∧ x13.inputs.length = (2 : ℕ) ∧ (x13.inputs.all fun (x14 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x14 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x13) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };               have x14 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x14 x15 : Fin x2) (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x14 ∨ x16 = Fin.natAdd x2 x15);               ∀ (x15 : Fin x2 → Finset (Fin x2)), (∀ (x16 x17 : Fin x2), x17 ∈ x15 x16 → x3 x17 x16 ∧ x5.eval (List.ofFn (x14 x17 x16)) = Bool.true ∧ x13.eval (List.ofFn (x14 x17 x16)) = Bool.false) → ∑ x17 : Fin x2, (x15 x17).card ≤ (44 : ℕ) * Fintype.card { x17 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x17) Bool.false = Bool.false ∧ ∃ (x18 : Fin x2), ∃ x19 ∈ x15 x18, (x5.wires (List.ofFn (x14 x19 x18))).getD (x2 + x2 + ↑x17) Bool.false = Bool.true }) :=
  PEqualNP.Outside.L_meta_3040.solveCutClaim
