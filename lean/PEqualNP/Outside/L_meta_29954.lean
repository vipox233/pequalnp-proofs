import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Coset.Basic

namespace PEqualNP.Outside.L_meta_29954
open Finset

theorem select_largest {T : Type*} [DecidableEq T] (mass : T → ℕ) (b : ℕ) (U : Finset T) :
    ∃ S ⊆ U, S.card = min b U.card ∧
      ∀ i ∈ S, ∀ j ∈ U, j ∉ S → mass j ≤ mass i := by
  induction b generalizing U with
  | zero => exact ⟨∅, empty_subset _, by simp, by simp⟩
  | succ b ih =>
    by_cases hU : U.Nonempty
    · obtain ⟨x,hx,hm⟩ := U.exists_max_image mass hU
      obtain ⟨R,hR,hcard,horder⟩ := ih (U.erase x)
      have hxR : x ∉ R := fun h => (mem_erase.mp (hR h)).1 rfl
      refine ⟨insert x R, insert_subset hx (hR.trans (erase_subset _ _)), ?_, ?_⟩
      · rw [card_insert_of_notMem hxR, hcard, card_erase_of_mem hx]
        have hp := card_pos.mpr hU
        omega
      · intro i hi j hj hout
        have jne : j ≠ x := fun h => hout (mem_insert.mpr (.inl h))
        rcases mem_insert.mp hi with rfl | hr
        · exact hm j hj
        · exact horder i hr j (mem_erase.mpr ⟨jne,hj⟩) (fun h => hout (mem_insert_of_mem h))
    · have he := not_nonempty_iff_eq_empty.mp hU
      subst U
      exact ⟨∅, Subset.rfl, by simp, by simp⟩

theorem bound_at_level {T : Type*} [Fintype T] (mass : T → ℕ) (S : Finset T)
    (budget z : ℕ) (hs : S.card ≤ budget) :
    ∑ i ∈ S, mass i ≤ budget*z + ∑ i, (mass i-z) := by
  calc
    _ ≤ ∑ i ∈ S, (z + (mass i-z)) := sum_le_sum (fun i _ => by omega)
    _ = S.card*z + ∑ i ∈ S, (mass i-z) := by simp [sum_add_distrib]
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_right _ hs)
      (sum_le_sum_of_subset_of_nonneg (subset_univ S) (by intros; exact Nat.zero_le _))

theorem coverage_iff_thresholds {T : Type*} [Fintype T] (mass : T → ℕ) (budget goal : ℕ) :
    (∃ S : Finset T, S.card ≤ budget ∧ goal ≤ ∑ i ∈ S, mass i) ↔
    ∀ p : Option T, let z := p.elim 0 mass
      goal ≤ budget*z + ∑ i, (mass i-z) := by
  classical
  constructor
  · rintro ⟨S,hs,hg⟩ p
    exact hg.trans (bound_at_level mass S budget _ hs)
  · intro h
    by_cases hfull : (univ : Finset T).card ≤ budget
    · exact ⟨univ,hfull,by simpa using h none⟩
    · obtain ⟨S,_,hc,ho⟩ := select_largest mass budget (univ : Finset T)
      rw [min_eq_left (by omega)] at hc
      have hout : (univ \ S).Nonempty := by
        by_contra! hn
        have hall : (univ : Finset T) ⊆ S := sdiff_eq_empty_iff_subset.mp hn
        have := card_le_card hall
        omega
      obtain ⟨x,hx,hm⟩ := (univ \ S).exists_max_image mass hout
      have hsmall (j : T) (hj : j ∉ S) : mass j ≤ mass x :=
        hm j (mem_sdiff.mpr ⟨mem_univ _,hj⟩)
      have hlarge (j : T) (hj : j ∈ S) : mass x ≤ mass j :=
        ho j hj x (mem_univ _) (mem_sdiff.mp hx).2
      have trim : ∑ i ∈ S, (mass i-mass x) = ∑ i, (mass i-mass x) :=
        sum_subset (subset_univ _) (fun j _ hj => Nat.sub_eq_zero_of_le (hsmall j hj))
      refine ⟨S, hc.le, (h (some x)).trans_eq ?_⟩
      change budget*mass x + ∑ i, (mass i-mass x) = _
      rw [← trim, ← hc]
      calc
        _ = ∑ i ∈ S, (mass x + (mass i-mass x)) := by simp [sum_add_distrib]
        _ = _ := sum_congr rfl (fun j hj => by have := hlarge j hj; omega)

theorem coverage_with_copies {I : Type*} [Fintype I] (value copies : I → ℕ)
    (budget goal : ℕ) :
    (∃ S : Finset (Σ i, Fin (copies i)), S.card ≤ budget ∧
      goal ≤ ∑ u ∈ S, value u.1) ↔
    ∀ p : Option I, let z := p.elim 0 value
      goal ≤ budget*z + ∑ i, copies i * (value i-z) := by
  classical
  have group (z : ℕ) : (∑ u : Σ i, Fin (copies i), (value u.1-z)) =
      ∑ i, copies i*(value i-z) := by
    rw [Fintype.sum_sigma]
    simp
  constructor
  · rintro ⟨S,hc,hg⟩ p
    exact (hg.trans (bound_at_level (fun u : Σ i, Fin (copies i) => value u.1) S budget _ hc)).trans_eq
      (congrArg (budget*p.elim 0 value + ·) (group _))
  · intro h
    apply (coverage_iff_thresholds _ _ _).mpr
    intro p
    cases p with
    | none => simpa only [Option.elim_none, group] using h none
    | some u => simpa only [Option.elim_some, group] using h (some u.1)

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954

abbrev F := ZMod 2
abbrev Bits (n : ℕ) := Fin n → F

def captures {k m s : ℕ} (out : Bits k → Bits m) (budget goal : ℕ) :=
  ∃ (P : (Bits k × Bits m) →ₗ[F] Bits s) (S : Finset (Bits s)),
    Function.Surjective P ∧ S.card ≤ budget ∧
    goal ≤ ((Finset.univ : Finset (Bits k)).filter (fun x => P (x,out x) ∈ S)).card

theorem add_affine_outputs {k m s : ℕ} (u : Bits k → Bits m)
    (A : Bits k →ₗ[F] Bits m) (c : Bits m) (budget goal : ℕ) :
    captures (s:=s) (fun x => u x + A x + c) budget goal ↔ captures (s:=s) u budget goal := by
  classical
  let e := (LinearEquiv.refl F (Bits k)).skewProd (LinearEquiv.refl F (Bits m)) A
  have eapp (x : Bits k) (y : Bits m) : e (x,y) = (x,y+A x) := rfl
  constructor
  · rintro ⟨P,S,hP,hS,hg⟩
    let t := P (0,c)
    let shift : Bits s ≃ Bits s := Equiv.addRight (-t)
    refine ⟨P.comp e.toLinearMap,S.map shift.toEmbedding,hP.comp e.surjective,by simpa using hS,?_⟩
    have iff_mem (x : Bits k) : P (x,u x + A x + c) ∈ S ↔
        (P.comp e.toLinearMap) (x,u x) ∈ S.map shift.toEmbedding := by
      rw [Finset.mem_map_equiv]
      change P (x,u x + A x + c) ∈ S ↔ shift.symm (P (x,u x+A x)) ∈ S
      have he : (x,u x + A x + c) = (x,u x+A x) + (0,c) := by simp
      rw [he,map_add]
      simp [shift,t]
    simpa only [← iff_mem] using hg
  · rintro ⟨P,S,hP,hS,hg⟩
    let Q := P.comp e.symm.toLinearMap
    let t := Q (0,c)
    let shift : Bits s ≃ Bits s := Equiv.addRight t
    refine ⟨Q,S.map shift.toEmbedding,hP.comp e.symm.surjective,by simpa using hS,?_⟩
    have iff_mem (x : Bits k) : Q (x,u x + A x + c) ∈ S.map shift.toEmbedding ↔
        P (x,u x) ∈ S := by
      rw [Finset.mem_map_equiv]
      have he : (x,u x + A x + c) = e (x,u x) + (0,c) := by rw [eapp]; simp
      rw [he,map_add]
      have hq : Q (e (x,u x)) = P (x,u x) := by simp [Q]
      rw [hq]
      simp [shift,t]
    simpa only [iff_mem] using hg

def index {k : ℕ} (hk : 0 < k) (n : ℕ) : Fin k := ⟨n%k, Nat.mod_lt _ hk⟩
def rotate {k : ℕ} (hk : 0 < k) (n : ℕ) (x : Bits k) (j : Fin k) :=
  x (index hk (j.val+k-n%k))
def mixing {k : ℕ} (hk : 0 < k) (b : Bool) (x : Bits k) (j : Fin k) :=
  let d := if b then 2 else 1
  x j + x (index hk (j.val+d)) + x (index hk (j.val+k-d%k))

def keyForm {k : ℕ} (hk : 0 < k) (b : Bool) (j : Fin k) : Bits k →ₗ[F] F where
  toFun x := mixing hk b (rotate hk (if b then 3 else 1) x) j
  map_add' x y := by simp [mixing,rotate]; ring
  map_smul' r x := by simp [mixing,rotate]; ring

def readForm {k : ℕ} (hk : 0 < k) (b : Bool) (j : Fin k) : Bits k →ₗ[F] F where
  toFun x := rotate hk (if b then 4 else 0) x j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem physical_normal_form {k m : ℕ} (hk : 0 < k) (bank : Fin m → Bool)
    (site : Fin m → Fin k) (name c : Bool → Bits k) :
    let mixed := fun (i : Fin m) (base source : Bits k) =>
      mixing hk (bank i) (rotate hk (if bank i then 3 else 1) source + base)
    let y := fun (x : Bits k) (i : Fin m) => mixed i (name (bank i)) x
    let out := fun x (i : Fin m) =>
      y x i (site i) + (1+y x i (index hk ((site i).val+1)))*y x i (index hk ((site i).val+2))
        + rotate hk (if bank i then 4 else 0) x (site i) + c (bank i) (site i)
    let quad := fun x (i : Fin m) =>
      mixed i 0 x (index hk ((site i).val+1)) * mixed i 0 x (index hk ((site i).val+2))
    ∃ (A : Bits k →ₗ[F] Bits m) (v : Bits m), ∀ x, out x = quad x + A x + v := by
  let j (i : Fin m) (r : ℕ) := index hk ((site i).val+r)
  let t (i : Fin m) := mixing hk (bank i) (name (bank i))
  let L (i : Fin m) := keyForm hk (bank i)
  let a (i : Fin m) := L i (site i) + readForm hk (bank i) (site i) +
    t i (j i 2) • L i (j i 1) + (1+t i (j i 1)) • L i (j i 2)
  refine ⟨LinearMap.pi a,fun i => t i (site i) + (1+t i (j i 1))*t i (j i 2) + c (bank i) (site i),?_⟩
  intro x
  funext i
  simp [a, t, j, L, keyForm, readForm, mixing, rotate, smul_eq_mul]
  ring

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954

abbrev Operands (m : ℕ) := Fin m → Bool → F

theorem split_keys {k m : ℕ} (A : Bits k →ₗ[F] Operands m)
    (hA : Function.Surjective A) :
    2*m ≤ k ∧ ∃ e : (Operands m × Bits (k-2*m)) ≃ₗ[F] Bits k,
      ∀ p, A (e p) = p.1 := by
  classical
  have onto := LinearMap.range_eq_top.mpr hA
  have dim := A.finrank_range_add_finrank_ker
  rw [onto,finrank_top] at dim
  have hdim : m*2 + Module.finrank F A.ker = k := by
    simpa [Bits, Operands, Module.finrank_pi, Module.finrank_pi_fintype, mul_comm] using dim
  have kle : 2*m ≤ k := by omega
  refine ⟨kle,?_⟩
  have hker : k-2*m = Module.finrank F A.ker := by omega
  let nice : Bits (k-2*m) ≃ₗ[F] A.ker := LinearEquiv.ofFinrankEq (R:=F) (Bits (k-2*m)) A.ker
    (by simpa only [Bits,Module.finrank_pi,Fintype.card_fin] using hker)
  obtain ⟨R,hR⟩ := A.exists_rightInverse_of_surjective onto
  have sec (x) : A (R x) = x := LinearMap.congr_fun hR x
  let J : (Operands m × Bits (k-2*m)) →ₗ[F] Bits k :=
    R.comp (LinearMap.fst _ _ _) + (A.ker.subtype.comp nice.toLinearMap).comp (LinearMap.snd _ _ _)
  have eval (p : Operands m × Bits (k-2*m)) : J p = R p.1 + (nice p.2).val := rfl
  have fst (p : Operands m × Bits (k-2*m)) : A (J p) = p.1 := by
    rw [eval,map_add,sec,show A (nice p.2).val = 0 from (nice p.2).property,add_zero]
  have inj : Function.Injective J := by
    intro p q h
    have he := congrArg A h
    rw [fst,fst] at he
    apply Prod.ext he
    apply nice.injective
    apply Subtype.ext
    rw [eval,eval,he] at h
    exact add_left_cancel h
  have surj : Function.Surjective J := by
    intro x
    let z : A.ker := ⟨x-R (A x), by change A (x-R (A x)) = 0; rw [map_sub,sec,sub_self]⟩
    refine ⟨(A x,nice.symm z),?_⟩
    rw [eval]
    change R (A x) + (nice (nice.symm z)).val = x
    rw [nice.apply_symm_apply]
    change R (A x) + (x-R (A x)) = x
    abel
  exact ⟨LinearEquiv.ofBijective J ⟨inj,surj⟩,fst⟩

def operandForm {k m : ℕ} (hk : 0 < k) (bank : Fin m → Bool) (site : Fin m → Fin k) :
    Bits k →ₗ[F] Operands m :=
  LinearMap.pi (fun i => LinearMap.pi (fun b =>
    keyForm hk (bank i) (index hk ((site i).val + if b then 2 else 1))))

theorem operandForm_eq {k m : ℕ} (hk : 0 < k) (bank : Fin m → Bool) (site : Fin m → Fin k)
    (x : Bits k) (i : Fin m) (b : Bool) :
    operandForm hk bank site x i b =
      mixing hk (bank i) (rotate hk (if bank i then 3 else 1) x + 0)
        (index hk ((site i).val + if b then 2 else 1)) := by
  rw [add_zero]; rfl

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954

def coverData {X : Type*} [AddCommGroup X] [Module F X] [Fintype X] {m s : ℕ}
    (u : X → Bits m) (budget goal : ℕ) :=
  ∃ (P : (X × Bits m) →ₗ[F] Bits s) (S : Finset (Bits s)),
    Function.Surjective P ∧ S.card ≤ budget ∧
    goal ≤ ((Finset.univ : Finset X).filter (fun x => P (x,u x) ∈ S)).card

theorem reindex_filter {X X' : Type*} [Fintype X] [Fintype X'] (e : X ≃ X') (p : X' → Prop)
    [DecidablePred p] :
    (Finset.univ.filter (fun a => p (e a))).card = (Finset.univ.filter p).card := by
  classical
  have image : (Finset.univ.filter (fun a => p (e a))).map e.toEmbedding = Finset.univ.filter p := by
    ext y
    simp [Finset.mem_map_equiv]
  rw [← image, Finset.card_map]

theorem change_key {X X' : Type*} [AddCommGroup X] [Module F X] [Fintype X]
    [AddCommGroup X'] [Module F X'] [Fintype X'] {m s : ℕ} (e : X' ≃ₗ[F] X)
    (u : X → Bits m) (budget goal : ℕ) :
    coverData (s:=s) u budget goal ↔ coverData (s:=s) (fun x => u (e x)) budget goal := by
  classical
  let e' := e.prodCongr (LinearEquiv.refl F (Bits m))
  constructor
  · rintro ⟨P,S,hP,hS,hg⟩
    refine ⟨P.comp e'.toLinearMap,S,hP.comp e'.surjective,hS,?_⟩
    change goal ≤ (Finset.univ.filter (fun x : X' => P (e x,u (e x)) ∈ S)).card
    exact hg.trans_eq (reindex_filter e.toEquiv (fun x => P (x,u x) ∈ S)).symm
  · rintro ⟨P,S,hP,hS,hg⟩
    refine ⟨P.comp e'.symm.toLinearMap,S,hP.comp e'.symm.surjective,hS,?_⟩
    change goal ≤ (Finset.univ.filter (fun x => P (e.symm x,u x) ∈ S)).card
    rw [← reindex_filter e.toEquiv (fun x => P (e.symm x,u x) ∈ S)]
    simpa using hg

def outputs {k m : ℕ} (hk : 0 < k) (bank : Fin m → Bool) (site : Fin m → Fin k)
    (name c : Bool → Bits k) (x : Bits k) (i : Fin m) :=
  let b := bank i
  let j := site i
  let y := mixing hk b (rotate hk (if b then 3 else 1) x + name b)
  y j + (1+y (index hk (j.val+1)))*y (index hk (j.val+2)) +
    rotate hk (if b then 4 else 0) x j + c b j

def blocks {m d : ℕ} (p : Operands m × Bits d) (i : Fin m) := p.1 i false * p.1 i true

theorem histories_iff_blocks {k m s : ℕ} (hk : 0 < k) (bank : Fin m → Bool)
    (site : Fin m → Fin k) (name c : Bool → Bits k) (budget goal : ℕ)
    (ha : Function.Surjective (operandForm hk bank site)) :
    captures (s:=s) (outputs hk bank site name c) budget goal ↔
      coverData (s:=s) (blocks (m:=m) (d:=k-2*m)) budget goal := by
  let A := operandForm hk bank site
  let q (x : Bits k) (i : Fin m) := A x i false * A x i true
  obtain ⟨_,e,he⟩ := split_keys A ha
  obtain ⟨L,c₀,hL⟩ := physical_normal_form hk bank site name c
  have eq : outputs hk bank site name c = fun x => q x + L x + c₀ := by
    funext x i
    simpa only [q,A,operandForm_eq,outputs,Pi.add_apply,Bool.false_eq_true,ite_false,ite_true]
      using congrFun (hL x) i
  rw [eq,add_affine_outputs]
  change coverData q budget goal ↔ _
  rw [change_key e q budget goal]
  have hq : (fun p => q (e p)) = blocks (m:=m) (d:=k-2*m) := by
    funext p i
    dsimp only [q,blocks]
    rw [he]
  rw [hq]

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954
open Finset

def blanks {n q : ℕ} (x : Fin n → Option (Fin q)) := univ.filter (fun i => x i = none)

def fill {n q : ℕ} (S : Finset (Fin n)) (a : {i : Fin n // i ∉ S} → Fin q)
    (i : Fin n) : Option (Fin q) := if h : i ∈ S then none else some (a ⟨i,h⟩)

theorem blanks_fill {n q : ℕ} (S : Finset (Fin n)) (a : {i : Fin n // i ∉ S} → Fin q) :
    blanks (fill S a) = S := by
  ext i
  by_cases hi : i ∈ S <;> simp [blanks,fill,hi]

noncomputable def digitsEquiv (n q : ℕ) : (Fin n → Option (Fin q)) ≃
    Σ S : Finset (Fin n), ({i : Fin n // i ∉ S} → Fin q) :=
  Equiv.symm <| Equiv.ofBijective (fun p => fill (n:=n) (q:=q) p.1 p.2) (by
    constructor
    · rintro ⟨S,a⟩ ⟨T,b⟩ h
      have hst := congrArg blanks h
      dsimp only at h hst
      rw [blanks_fill,blanks_fill] at hst
      subst T
      congr 1
      funext u
      have he := congrFun h u.val
      simpa only [fill,dite_eq_right u.property,Option.some.injEq] using he
    · intro x
      let S := blanks x
      have someAt (i : {j : Fin n // j ∉ S}) : (x i.val).isSome := by
        have hi := i.property
        simpa [S,blanks, Option.isSome_iff_ne_none] using hi
      refine ⟨⟨S, fun i => (x i.val).get (someAt i)⟩,?_⟩
      funext i
      by_cases hi : i ∈ S
      · simpa [fill,hi] using (show x i = none by simpa [S,blanks] using hi).symm
      · simp [fill,hi])

theorem digit_sum (n q : ℕ) (g : ℕ → ℕ) :
    (∑ x : Fin n → Option (Fin q), g (blanks x).card) =
      ∑ t : Fin (n+1), n.choose t.val * q^(n-t.val) * g t.val := by
  classical
  let e := digitsEquiv n q
  have repr (p : Σ S : Finset (Fin n), ({i : Fin n // i ∉ S} → Fin q)) :
      blanks (e.symm p) = p.1 := blanks_fill p.1 p.2
  have bySet : (∑ x : Fin n → Option (Fin q), g (blanks x).card) =
      ∑ S : Finset (Fin n), q^(n-S.card)*g S.card := by
    rw [← e.symm.sum_comp (fun x => g (blanks x).card)]
    simp only [repr,Fintype.sum_sigma]
    apply sum_congr rfl
    intro S _
    simp [Fintype.card_subtype_compl, Fintype.card_coe]
  rw [bySet, Fin.sum_univ_eq_sum_range (fun t => n.choose t * q^(n-t) * g t)]
  have inside (S : Finset (Fin n)) (_ : S ∈ univ) : S.card ∈ range (n+1) := by
    have := card_le_univ S
    simpa only [mem_range,Nat.lt_succ_iff,Fintype.card_fin] using this
  rw [← sum_fiberwise_of_maps_to' (s:=univ) (t:=range (n+1)) (g:=card) inside
    (fun t => q^(n-t)*g t)]
  apply sum_congr rfl
  intro t ht
  have he : (univ.filter (fun S : Finset (Fin n) => S.card = t)) =
      (univ : Finset (Fin n)).powersetCard t := by
    ext S; simp
  simp [he,mul_assoc]

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954
open Finset

theorem concentrate {J : Type*} [DecidableEq J] (U : Finset J)
    (count gain : J → ℕ) (pos : ∀ j ∈ U, 0 < count j) (r : ℕ) (hr : r < U.card) :
    ∃ x ∈ U, ∃ T ⊆ U.erase x, T.card = r ∧
      (∑ j ∈ U, count j * gain j) ≤
        ((∑ j ∈ U, count j)-r)*gain x + ∑ j ∈ T, gain j := by
  obtain ⟨x,hx,hmax⟩ := U.exists_max_image gain (card_pos.mp (by omega))
  obtain ⟨T,ht,hc⟩ := exists_subset_card_eq (s:=U.erase x) (n:=r)
    (by rw [card_erase_of_mem hx]; omega)
  have sub : T ⊆ U := ht.trans (erase_subset _ _)
  let rem (j : J) := count j - if j ∈ T then 1 else 0
  have split (j : J) (hj : j ∈ U) : rem j + (if j ∈ T then 1 else 0) = count j := by
    have := pos j hj
    dsimp [rem]
    split <;> omega
  have total : (∑ j ∈ U, rem j) + r = ∑ j ∈ U, count j := by
    calc
      _ = (∑ j ∈ U, rem j) + ∑ j ∈ U, (if j ∈ T then 1 else 0) := by
        simp [sum_ite_mem, inter_eq_right.mpr sub, hc]
      _ = _ := by rw [← sum_add_distrib]; exact sum_congr rfl split
  have weighted : (∑ j ∈ U, count j * gain j) =
      (∑ j ∈ U, rem j * gain j) + ∑ j ∈ T, gain j := by
    calc
      _ = ∑ j ∈ U, (rem j * gain j + if j ∈ T then gain j else 0) := by
        apply sum_congr rfl
        intro j hj
        conv_lhs => rw [← split j hj, add_mul]
        split <;> simp_all
      _ = _ := by rw [sum_add_distrib, sum_ite_mem, inter_eq_right.mpr sub]
  refine ⟨x,hx,T,ht,hc,?_⟩
  rw [weighted, ← total, Nat.add_sub_cancel]
  apply Nat.add_le_add_right
  rw [sum_mul]
  exact sum_le_sum (fun j hj => Nat.mul_le_mul_left _ (hmax j hj))

def dominated {A B : Type*} (u : A → ℕ) (v : B → ℕ) : Prop :=
  ∀ S : Finset A, ∃ T : Finset B, T.card ≤ S.card ∧ (∑ a ∈ S, u a) ≤ ∑ b ∈ T, v b

theorem ranked_block_bound {A B J H : Type*} [Fintype H] [Fintype J] [DecidableEq J] [Fintype B]
    (u : A → ℕ) (v : B → ℕ) (dom : dominated u v)
    (label : H → J) (shift : H → A ≃ A) (r : ℕ)
    (hr : r < (univ.image label).card) (S : J → Finset A) :
    ∃ (top : Finset B) (other : Fin r → Finset B),
      top.card + ∑ t, (other t).card ≤ ∑ j, (S j).card ∧
      (∑ h, ∑ a ∈ S (label h), u (shift h a)) ≤
        (Fintype.card H-r)*(∑ b ∈ top, v b) + ∑ t, ∑ b ∈ other t, v b := by
  classical
  let V (j : J) := (select_largest v (S j).card univ).choose
  have hV (j : J) := (select_largest v (S j).card univ).choose_spec
  let gain (j : J) := ∑ b ∈ V j, v b
  let U := univ.image label
  let count (j : J) := (univ.filter (fun h => label h = j)).card
  have pos (j : J) (hj : j ∈ U) : 0 < count j := by
    obtain ⟨h,_,rfl⟩ := mem_image.mp hj
    exact card_pos.mpr ⟨h,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
  have best (j : J) (T : Finset B) (ht : T.card ≤ (S j).card) :
      (∑ b ∈ T, v b) ≤ gain j := by
    have hc : T.card ≤ (V j).card := by
      rw [show (V j).card = _ from (hV j).2.1]
      exact le_min ht (card_le_card (subset_univ T))
    let lost := T \ V j
    let addn := V j \ T
    have hcard : lost.card ≤ addn.card := by
      dsimp [lost,addn]
      have h₁ := card_sdiff_add_card_inter T (V j)
      have h₂ := card_sdiff_add_card_inter (V j) T
      rw [inter_comm (V j) T] at h₂
      omega
    have inequality : (∑ b ∈ lost, v b) ≤ ∑ b ∈ addn, v b := by
      by_cases hn : lost.Nonempty
      · obtain ⟨z,hz,hmax⟩ := lost.exists_max_image v hn
        calc
          _ ≤ ∑ _b ∈ lost, v z := sum_le_sum (fun _ hb => hmax _ hb)
          _ = lost.card*v z := by simp
          _ ≤ addn.card*v z := Nat.mul_le_mul_right _ hcard
          _ = ∑ _b ∈ addn, v z := by simp
          _ ≤ _ := sum_le_sum (fun b hb => (hV j).2.2 b (mem_sdiff.mp hb).1 z
            (mem_univ _) (mem_sdiff.mp hz).2)
      · simp [not_nonempty_iff_eq_empty.mp hn]
    have left := sum_sdiff (inter_subset_left (s₁:=T) (s₂:=V j)) (f:=v)
    have right := sum_sdiff (inter_subset_right (s₁:=T) (s₂:=V j)) (f:=v)
    simp only [sdiff_inter_self_left, sdiff_inter_self_right] at left right
    change (∑ b ∈ T, v b) ≤ ∑ b ∈ V j, v b
    dsimp [lost,addn] at inequality
    omega
  have shifted (h : H) : (∑ a ∈ S (label h), u (shift h a)) ≤ gain (label h) := by
    let R := (S (label h)).map (shift h).toEmbedding
    obtain ⟨T,hc,hm⟩ := dom R
    exact (by simpa [R] using hm : (∑ a ∈ S (label h), u (shift h a)) ≤ ∑ b ∈ T, v b).trans
      (best _ T (by simpa [R] using hc))
  have fiber (f : J → ℕ) : (∑ h, f (label h)) = ∑ j ∈ U, count j*f j := by
    simpa [count] using (sum_fiberwise_of_maps_to' (s:=univ) (t:=U) (g:=label)
      (fun h _ => mem_image.mpr ⟨h,mem_univ _,rfl⟩) f).symm
  have total : (∑ j ∈ U, count j) = Fintype.card H := by
    simpa using (fiber (fun _ => 1)).symm
  obtain ⟨x,hx,T,ht,hcard,hb⟩ := concentrate U count gain pos r hr
  let e : T ≃ Fin r := Fintype.equivFinOfCardEq (by simpa using hcard)
  refine ⟨V x, fun t => V (e.symm t).val, ?_, ?_⟩
  · have sub : insert x T ⊆ (univ : Finset J) := subset_univ _
    have nx : x ∉ T := fun h => (mem_erase.mp (ht h)).1 rfl
    have he : (∑ t, (V (e.symm t).val).card) = ∑ j ∈ T, (V j).card :=
      (e.symm.sum_comp (fun t : T => (V t.val).card)).trans (Finset.sum_coe_sort T (fun j => (V j).card))
    rw [he, ← sum_insert (f:=fun j => (V j).card) nx]
    exact (sum_le_sum (fun j _ => (hV j).2.1.le.trans (min_le_left _ _))).trans
      (sum_le_sum_of_subset_of_nonneg sub (by intros; exact Nat.zero_le _))
  · have he : (∑ t, gain (e.symm t).val) = ∑ j ∈ T, gain j :=
      (e.symm.sum_comp (fun t : T => gain t.val)).trans (Finset.sum_coe_sort T gain)
    change _ ≤ _*gain x + ∑ t, gain (e.symm t).val
    rw [he, ← total]
    exact (sum_le_sum (fun h _ => shifted h)).trans ((fiber gain).le.trans hb)

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954
open Finset

theorem rank_lt_support {J H : Type*} [AddCommGroup J] [Module F J]
    [DecidableEq J] [Fintype H] (label : H → J)
    (zero : 0 ∈ Set.range label) (spans : Submodule.span F (Set.range label) = ⊤) :
    Module.finrank F J < (univ.image label).card := by
  classical
  let U := univ.image label
  have hU : (U : Set J) = Set.range label := by simp [U]
  have hspan : Submodule.span F (↑(U.erase 0) : Set J) = ⊤ := by
    rw [coe_erase,hU,Submodule.span_sdiff_singleton_zero,spans]
  have bound := finrank_span_le_card (R:=F) (↑(U.erase 0) : Set J)
  rw [hspan,finrank_top] at bound
  have hz : 0 ∈ U := by change 0 ∈ (U : Set J); rwa [hU]
  have cardpos : 0 < U.card := card_pos.mpr ⟨0,hz⟩
  have same : (↑(U.erase 0) : Set J).toFinset = U.erase 0 := by ext; simp [and_comm]
  rw [same,card_erase_of_mem hz] at bound
  change _ < U.card
  omega

theorem measure_by_fibers {K A J H : Type*} [Fintype K] [Fintype A] [Fintype H]
    [DecidableEq A] [DecidableEq J] (loc : K → A) (label : H → J) (shift : H → A ≃ A)
    (S : Finset (J × A)) :
    let buckets := fun j => univ.filter (fun a : A => (j,a) ∈ S)
    let weight := fun a => (univ.filter (fun x : K => loc x = a)).card
    (univ.filter (fun p : H × K => (label p.1,(shift p.1).symm (loc p.2)) ∈ S)).card =
      ∑ h, ∑ a ∈ buckets (label h), weight (shift h a) := by
  classical
  let bucket (h : H) := univ.filter (fun a : A => (label h,a) ∈ S)
  have row (h : H) :
      (univ.filter (fun x : K => (label h,(shift h).symm (loc x)) ∈ S)).card =
        ∑ a ∈ bucket h, (univ.filter (fun x : K => loc x = shift h a)).card := by
    have pre (a : A) : (univ.filter (fun x : K => (shift h).symm (loc x) = a)) =
        univ.filter (fun x : K => loc x = shift h a) := by
      ext x; simp [Equiv.symm_apply_eq]
    simpa only [pre,bucket,mem_filter, mem_univ,true_and] using
      (sum_card_fiberwise_eq_card_filter (univ : Finset K) (bucket h) (fun x => (shift h).symm (loc x))).symm
  dsimp only
  simp only [card_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro h _
  simpa only [card_filter,bucket] using row h

theorem ranked_projection_step {K A B J H : Type*}
    [Fintype K] [Fintype A] [Fintype B] [Fintype H] [Fintype J]
    [DecidableEq A] [DecidableEq J] [AddCommGroup J] [Module F J]
    (loc : K → A) (label : H → J) (shift : H → A ≃ A) (v : B → ℕ)
    (dom : dominated (fun a => (univ.filter (fun x : K => loc x = a)).card) v)
    (zero : 0 ∈ Set.range label) (spans : Submodule.span F (Set.range label) = ⊤)
    (S : Finset (J × A)) :
    ∃ (heavy : Finset B) (others : Fin (Module.finrank F J) → Finset B),
      heavy.card + ∑ t, (others t).card ≤ S.card ∧
      (univ.filter (fun p : H × K => (label p.1,(shift p.1).symm (loc p.2)) ∈ S)).card ≤
      (Fintype.card H-Module.finrank F J)*(∑ b ∈ heavy, v b) +
        ∑ t, ∑ b ∈ others t, v b := by
  classical
  let bucket (j : J) := univ.filter (fun a : A => (j,a) ∈ S)
  have total : (∑ j, (bucket j).card) = S.card := by
    classical
    have rhs : (univ.filter (fun z : J × A => z ∈ S)) = S := by ext; simp
    rw [← rhs]
    simp only [bucket,card_filter,Fintype.sum_prod_type]
  obtain ⟨heavy,other,hsize,hmass⟩ := ranked_block_bound _ v dom label shift _
    (rank_lt_support label zero spans) bucket
  exact ⟨heavy,other,hsize.trans_eq total,(measure_by_fibers loc label shift S).le.trans hmass⟩

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954
open Finset

def extendMass {B : Type*} (r n : ℕ) (v : B → ℕ) (u : Fin (r+1) × B) :=
  (if u.1.val = 0 then n-r else 1) * v u.2

theorem assemble_buckets {B : Type*} [Fintype B] [DecidableEq B] (r n : ℕ)
    (v : B → ℕ) (heavy : Finset B) (others : Fin r → Finset B) :
    ∃ T : Finset (Fin (r+1) × B),
      T.card = heavy.card + ∑ i, (others i).card ∧
      (∑ u ∈ T, extendMass r n v u) =
        (n-r)*(∑ b ∈ heavy, v b) + ∑ i, ∑ b ∈ others i, v b := by
  classical
  let bins : Fin (r+1) → Finset B := Fin.cons heavy others
  let T := univ.filter (fun p : Fin (r+1) × B => p.2 ∈ bins p.1)
  refine ⟨T,?_,?_⟩
  · simp only [T,card_filter,Fintype.sum_prod_type]
    rw [Fin.sum_univ_succ]
    simp [bins,← card_filter]
  · simp only [T,sum_filter,Fintype.sum_prod_type,extendMass]
    rw [Fin.sum_univ_succ]
    simp [bins,← Finset.sum_filter,Finset.mul_sum, mul_ite]

theorem extension_bound {K B Y H : Type*} [Fintype K] [Fintype B] [Fintype H] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] [Module F Y] (V : Submodule F Y) [Fintype V] [DecidableEq V]
    (loc : K → V) (v : H → Y) (prev : B → ℕ)
    (hdom : dominated (fun a => (univ.filter (fun x => loc x = a)).card) prev)
    (zero : 0 ∈ Set.range v) (span : Submodule.span F ((V : Set Y) ∪ Set.range v) = ⊤) :
    ∃ r, Module.finrank F V + r = Module.finrank F Y ∧ r < Fintype.card H ∧
      dominated (fun y => (univ.filter (fun p : H × K => v p.1 + (loc p.2).val = y)).card)
        (extendMass r (Fintype.card H) prev) := by
  classical
  obtain ⟨J,compl⟩ := V.exists_isCompl
  let e := J.prodEquivOfIsCompl V compl.symm
  let π : Y →ₗ[F] J := (LinearMap.fst F J V).comp e.symm.toLinearMap
  have app (j : J) (a : V) : e (j,a) = j.val + a.val := rfl
  have embed (a : V) : e.symm (a.val) = (0,a) := by
    apply e.symm_apply_eq.mpr
    rw [app]
    simp
  have zeroOn (a : V) : π a.val = 0 := by change (e.symm a.val).1 = 0; rw [embed]
  let label (h : H) := π (v h)
  have zeroLabel : 0 ∈ Set.range label := by
    obtain ⟨h,hh⟩ := zero
    exact ⟨h,by simp [label,hh]⟩
  have spanLabel : Submodule.span F (Set.range label) = ⊤ := by
    apply top_unique
    intro j _
    have hy : e (j,0) ∈ Submodule.span F ((V : Set Y) ∪ Set.range v) := by rw [span]; trivial
    have prop (y : Y) (hy : y ∈ Submodule.span F ((V : Set Y) ∪ Set.range v)) :
        π y ∈ Submodule.span F (Set.range label) := by
      induction hy using Submodule.span_induction with
      | mem y hy =>
        rcases hy with hV | ⟨h,rfl⟩
        · rw [show π y = 0 from zeroOn ⟨y,hV⟩]; exact Submodule.zero_mem _
        · exact Submodule.subset_span ⟨h,rfl⟩
      | zero => simp
      | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
      | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha
    simpa [π] using prop _ hy
  let shift (h : H) : V ≃ V := Equiv.addRight (-(e.symm (v h)).2)
  have rank := rank_lt_support label zeroLabel spanLabel
  refine ⟨Module.finrank F J,?_,rank.trans_le (card_image_le.trans (by simp)),?_⟩
  · simpa [Module.finrank_prod, Nat.add_comm] using e.finrank_eq
  · intro S
    let S' := S.map e.symm.toEquiv.toEmbedding
    obtain ⟨t,c,hc,hm⟩ := ranked_projection_step loc label shift prev hdom zeroLabel spanLabel S'
    obtain ⟨T,ht,hscore⟩ := assemble_buckets _ (Fintype.card H) prev t c
    refine ⟨T,by rw [ht]; simpa only [S',card_map] using hc,?_⟩
    rw [hscore,sum_card_fiberwise_eq_card_filter]
    have mem (p : H × K) :
        ((label p.1,(shift p.1).symm (loc p.2)) ∈ S') ↔ v p.1 + (loc p.2).val ∈ S := by
      rw [mem_map_equiv]
      have eq : e.symm (v p.1+(loc p.2).val) =
          (label p.1,(shift p.1).symm (loc p.2)) := by
        rw [map_add,embed]
        ext <;> simp [label,π,shift,add_comm]
      change e (label p.1,(shift p.1).symm (loc p.2)) ∈ S ↔ _
      rw [← eq,e.apply_symm_apply]
    simpa only [mem] using hm

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954
open Finset

abbrev ProfileIndex (f b c d : ℕ) :=
  Fin (2^f * 4^d) × (Fin b → Option (Fin 1)) × (Fin c → Option (Fin 2))

def mass {f b c d : ℕ} (base : ℕ) (u : ProfileIndex f b c d) :=
  base * 3^(blanks u.2.1).card * 2^(blanks u.2.2).card

theorem product_histogram (f b c d base : ℕ) (g : ℕ → ℕ) :
    (∑ u : ProfileIndex f b c d, g (mass base u)) =
      ∑ p : Fin (b+1) × Fin (c+1),
        (2^f * 4^d * b.choose p.1.val * c.choose p.2.val * 2^(c-p.2.val)) *
          g (base * 3^p.1.val * 2^p.2.val) := by
  simp only [ProfileIndex,Fintype.sum_prod_type,mass]
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  have inner (x : Fin b → Option (Fin 1)) :=
    digit_sum c 2 (fun j => g (base * 3^(blanks x).card * 2^j))
  simp only [inner]
  have outer := digit_sum b 1
    (fun i => ∑ j : Fin (c+1), c.choose j.val * 2^(c-j.val) * g (base*3^i*2^j.val))
  rw [outer]
  simp only [one_pow,mul_one,mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  simp <;> ring

theorem profile_coverage (f b c d base budget goal : ℕ) :
    (∃ S : Finset (ProfileIndex f b c d), S.card ≤ budget ∧ goal ≤ ∑ u ∈ S, mass base u) ↔
    ∀ p : Option (Fin (b+1) × Fin (c+1)),
      let value (t : Fin (b+1) × Fin (c+1)) := base * 3^t.1.val * 2^t.2.val
      let z := p.elim 0 value
      goal ≤ budget*z + ∑ t : Fin (b+1) × Fin (c+1),
        (2^f * 4^d * b.choose t.1.val * c.choose t.2.val * 2^(c-t.2.val)) * (value t-z) := by
  constructor
  · rintro ⟨S,hc,hg⟩ p
    let value (t : Fin (b+1) × Fin (c+1)) := base * 3^t.1.val * 2^t.2.val
    have upper := bound_at_level (mass base) S budget (p.elim 0 value) hc
    exact (hg.trans upper).trans_eq (congrArg (budget * p.elim 0 value + ·)
      (product_histogram f b c d base (fun v => v-p.elim 0 value)))
  · intro h
    apply (coverage_iff_thresholds (mass base) budget goal).mpr
    intro p
    let idx (u : ProfileIndex f b c d) : Fin (b+1) × Fin (c+1) :=
      (⟨(blanks u.2.1).card, Nat.lt_succ_of_le (by simpa using card_le_univ (blanks u.2.1))⟩,
       ⟨(blanks u.2.2).card, Nat.lt_succ_of_le (by simpa using card_le_univ (blanks u.2.2))⟩)
    have hh := h (p.map idx)
    dsimp only
    rw [product_histogram f b c d base (fun v => v-p.elim 0 (mass base))]
    cases p <;> exact hh

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954
open Finset

def predicted (k m s budget goal : ℕ) : Prop :=
  ∃ f a b c d : ℕ, a+b+c+d=m ∧ f≤k-2*m ∧ f+b+2*c+3*d=s ∧
    ∀ p : Option (Fin (b+1) × Fin (c+1)),
      let value := fun t : Fin (b+1) × Fin (c+1) => 2^(k-2*m-f) * 4^a * 3^t.1.val * 2^t.2.val
      let z := p.elim 0 value
      goal ≤ budget*z + ∑ t : Fin (b+1) × Fin (c+1),
        (2^f * 4^d * b.choose t.1.val * c.choose t.2.val * 2^(c-t.2.val)) * (value t-z)

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954
open Finset

theorem uniform_spare {d s : ℕ} (D : Bits d →ₗ[F] Bits s) (onto : Function.Surjective D)
    (S : Finset (Bits s)) :
    (univ.filter (fun x => D x ∈ S)).card = S.card * 2^(d-s) := by
  classical
  have dim := D.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr onto,finrank_top] at dim
  have dim' : s + Module.finrank F D.ker = d := by simpa [Bits,Module.finrank_pi] using dim
  have hk : Fintype.card D.ker = 2^(d-s) := by
    have hker : Module.finrank F D.ker = d-s := by omega
    rw [Module.card_eq_pow_finrank (K:=F)]
    rw [hker]
    rfl
  have fiber (y : Bits s) : (univ.filter (fun x => D x = y)).card = 2^(d-s) := by
    obtain ⟨x,rfl⟩ := onto y
    have eq : {z : Bits d // D z = D x} ≃ (D.ker : Type _) := D.toAddMonoidHom.fiberEquivKer x
    rw [← hk, ← Fintype.card_congr eq]
    exact (Fintype.card_subtype (fun z => D z = D x)).symm
  calc
    _ = ∑ y ∈ S, (univ.filter (fun x => D x = y)).card := by
      rw [sum_card_fiberwise_eq_card_filter]
    _ = _ := by simp [fiber]

theorem uniform_base_map {s d : ℕ} (h : s ≤ d) : ∃ D : Bits d →ₗ[F] Bits s,
    Function.Surjective D := by
  let D : Bits d →ₗ[F] Bits s := LinearMap.pi (fun i => LinearMap.proj (R:=F) (φ:=fun _ : Fin d => F)
    (Fin.castLE h i))
  refine ⟨D,?_⟩
  intro y
  refine ⟨fun j => if hj : j.val<s then y ⟨j.val,hj⟩ else 0,?_⟩
  funext i
  simp [D, Fin.castLE, i.isLt]

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954
open Finset

abbrev RecordSpace (m d : ℕ) := (Operands m × Bits d) × Bits m

def columnMap {m d s : ℕ} (D : Bits d →ₗ[F] Bits s) (a b t : Fin m → Bits s) :
    RecordSpace m d →ₗ[F] Bits s where
  toFun p := D p.1.2 + ∑ i, (p.1.1 i false • a i + p.1.1 i true • b i + p.2 i • t i)
  map_add' p q := by
    simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,map_add,add_smul]
    simp only [Finset.sum_add_distrib]
    abel
  map_smul' r p := by
    simp only [Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,map_smul,smul_add,Finset.smul_sum,
      RingHom.id_apply,smul_smul,smul_eq_mul]

def bitAt {m : ℕ} (i : Fin m) (b : Bool) : Operands m := Pi.single i (Pi.single b 1)

theorem record_expansion {m d : ℕ} (p : RecordSpace m d) :
    p = ((0,p.1.2),0) +
      ∑ i : Fin m, (p.1.1 i false • (((bitAt i false,0),0) : RecordSpace m d) +
        p.1.1 i true • (((bitAt i true,0),0) : RecordSpace m d) +
        p.2 i • (((0,0),Pi.single i 1) : RecordSpace m d)) := by
  classical
  apply Prod.ext
  · apply Prod.ext
    · funext j b
      cases b <;> simp [bitAt,Prod.fst_sum,Finset.sum_apply,Pi.single_apply,ite_apply,
        smul_eq_mul, mul_ite, ite_and, Finset.sum_add_distrib]
    · simp [Prod.fst_sum,Prod.snd_sum,Finset.sum_add_distrib]
  · funext j
    simp [Prod.snd_sum,Finset.sum_apply,Pi.single_apply,smul_eq_mul,mul_ite]

theorem every_projection {m d s : ℕ} (P : RecordSpace m d →ₗ[F] Bits s) :
    ∃ (D : Bits d →ₗ[F] Bits s) (a b t : Fin m → Bits s), P = columnMap D a b t := by
  let embed : Bits d →ₗ[F] RecordSpace m d := ((0 : Bits d →ₗ[F] Operands m).prod LinearMap.id).prod 0
  refine ⟨P.comp embed,fun i => P ((bitAt i false,0),0),
    fun i => P ((bitAt i true,0),0),fun i => P ((0,0),Pi.single i 1),?_⟩
  apply LinearMap.ext
  intro p
  conv_lhs => rw [record_expansion p]
  simp only [map_add,map_sum,map_smul,columnMap,LinearMap.coe_mk,AddHom.coe_mk]
  rfl

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954
open Finset

def blockPrediction (m spare s budget goal : ℕ) :=
  ∃ f a b c d : ℕ, a+b+c+d=m ∧ f≤spare ∧ f+b+2*c+3*d=s ∧
    ∃ S : Finset (ProfileIndex f b c d), S.card ≤ budget ∧
      goal ≤ ∑ u ∈ S, mass (2^(spare-f)*4^a) u

theorem prediction_eq (k m s budget goal : ℕ) :
    blockPrediction m (k-2*m) s budget goal ↔ predicted k m s budget goal := by
  constructor
  · rintro ⟨f,a,b,c,d,hm,hf,hs,h⟩
    exact ⟨f,a,b,c,d,hm,hf,hs,(profile_coverage f b c d _ budget goal).mp h⟩
  · rintro ⟨f,a,b,c,d,hm,hf,hs,h⟩
    exact ⟨f,a,b,c,d,hm,hf,hs,(profile_coverage f b c d _ budget goal).mpr h⟩

theorem transfer
    (independentBlocks : ∀ m spare s budget goal : ℕ,
      coverData (s:=s) (blocks (m:=m) (d:=spare)) budget goal ↔
        blockPrediction m spare s budget goal) :
∀ (k m s budget goal : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let E := Fin m → F
  let Y := Fin s → F
  let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (n : Nat) (x : W) (j : Fin k) => x (ix (j.val+k-n % k))
  let mix := fun (b : Bool) (x : W) (j : Fin k) =>
    let d := if b then 2 else 1
    x j + x (ix (j.val+d)) + x (ix (j.val+k-d % k))
  ∀ (bank : Fin m → Bool) (site : Fin m → Fin k),
    let mixed := fun (i : Fin m) (base source : W) =>
      mix (bank i) (rot (if bank i then 3 else 1) source + base)
    let operand := fun (direction : W) (i : Fin m) (second : Bool) =>
      mixed i 0 direction (ix ((site i).val + (if second then 2 else 1)))
    Function.Surjective operand →
    ∀ (name c : Bool → W),
      let out := fun (key : W) (i : Fin m) =>
        let b := bank i
        let j := site i
        let y := mixed i (name b) key
        y j + (1+y (ix (j.val+1)))*y (ix (j.val+2)) +
          rot (if b then 4 else 0) key j + c b j
      let physical := fun (P : (W × E) →ₗ[F] Y) (S : Finset Y) =>
        ((Finset.univ : Finset W).filter (fun candidate => P (candidate,out candidate) ∈ S)).card
      (∃ (P : (W × E) →ₗ[F] Y) (S : Finset Y),
        Function.Surjective P ∧ S.card ≤ budget ∧ goal ≤ physical P S) ↔
      ∃ (f a b c₂ d : Nat),
        a+b+c₂+d = m ∧ f ≤ k-2*m ∧ f+b+2*c₂+3*d = s ∧
        let I := Fin (b+1) × Fin (c₂+1)
        let value := fun pair : I => 2^(k-2*m-f) * 4^a * 3^pair.1.val * 2^pair.2.val
        let copies := fun cell : I => 2^f * 4^d * b.choose cell.1.val *
          c₂.choose cell.2.val * 2^(c₂-cell.2.val)
        ∀ pivot : Option I, let z := pivot.elim 0 value
          goal ≤ budget*z + ∑ h : I, copies h * (value h-z) := by
  intro k m s budget goal hk
  dsimp only
  intro bank site hop name c
  have ha : Function.Surjective (operandForm hk bank site) := by
    intro t
    obtain ⟨x,hx⟩ := hop t
    refine ⟨x,?_⟩
    funext i b
    rw [operandForm_eq]
    exact congrFun (congrFun hx i) b
  change captures (s:=s) (outputs hk bank site name c) budget goal ↔ predicted k m s budget goal
  exact (histories_iff_blocks hk bank site name c budget goal ha).trans
    ((independentBlocks m (k-2*m) s budget goal).trans (prediction_eq k m s budget goal))

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954
open Finset

def Tree (f : ℕ) : List ℕ → Type
  | [] => Fin (2^f)
  | r::rs => Fin (r+1) × Tree f rs

def treeFinite (f : ℕ) : (rs : List ℕ) → Fintype (Tree f rs)
  | [] => inferInstanceAs (Fintype (Fin (2^f)))
  | r::rs => letI := treeFinite f rs; inferInstanceAs (Fintype (Fin (r+1) × Tree f rs))

def treeMass (f base : ℕ) : (rs : List ℕ) → Tree f rs → ℕ
  | [],_ => base
  | r::rs,p => extendMass r 4 (treeMass f base rs) p

def history {Y : Type*} [AddCommGroup Y] [Module F Y] {spare m : ℕ}
    (D : Bits spare →ₗ[F] Y) (table : Fin m → Fin 4 → Y)
    (x : (Fin m → Fin 4) × Bits spare) := D x.2 + ∑ i, table i (x.1 i)

def fullSpan {Y : Type*} [AddCommGroup Y] [Module F Y] {spare m : ℕ}
    (D : Bits spare →ₗ[F] Y) (table : Fin m → Fin 4 → Y) :=
  Submodule.span F (Set.range D ∪ Set.range (fun p : Fin m × Fin 4 => table p.1 p.2))

theorem subspace_data {Y : Type*} [AddCommGroup Y] [Module F Y] {spare m : ℕ}
    (D : Bits spare →ₗ[F] Y) (tab : Fin m → Fin 4 → Y) :
    let V := fullSpan D tab
    ∃ (D' : Bits spare →ₗ[F] V) (tab' : Fin m → Fin 4 → V),
      (∀ x, (D' x).val = D x) ∧ (∀ i h, (tab' i h).val = tab i h) ∧ fullSpan D' tab' = ⊤ := by
  let V := fullSpan D tab
  let D' := D.codRestrict V (fun x => Submodule.subset_span (Or.inl ⟨x,rfl⟩))
  let tab' (i : Fin m) (h : Fin 4) : V := ⟨tab i h,Submodule.subset_span (Or.inr ⟨(i,h),rfl⟩)⟩
  refine ⟨D',tab',fun _ => rfl,fun _ _ => rfl,?_⟩
  apply top_unique
  intro x _
  have all (y : Y) (hy : y ∈ V) : (⟨y,hy⟩ : V) ∈ fullSpan D' tab' := by
    induction hy using Submodule.span_induction with
    | mem y h =>
      rcases h with ⟨p,rfl⟩ | ⟨p,rfl⟩
      · exact Submodule.subset_span (Or.inl ⟨p,rfl⟩)
      · exact Submodule.subset_span (Or.inr ⟨p,rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add a b _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
    | smul c a _ ha => exact Submodule.smul_mem _ c ha
  exact all x.val x.property

theorem span_head {Y : Type*} [AddCommGroup Y] [Module F Y] {spare m : ℕ}
    (D : Bits spare →ₗ[F] Y) (tab : Fin (m+1) → Fin 4 → Y) (h : fullSpan D tab = ⊤) :
    Submodule.span F ((fullSpan D (fun i : Fin m => tab i.succ) : Set Y) ∪ Set.range (tab 0)) = ⊤ := by
  rw [← h]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro y hy
    rcases hy with hv | ⟨j,rfl⟩
    · refine (Submodule.span_mono ?_) hv
      rintro z (hd | ⟨⟨i,h⟩,rfl⟩)
      · exact Or.inl hd
      · exact Or.inr ⟨(i.succ,h),rfl⟩
    · exact Submodule.subset_span (Or.inr ⟨(0,j),rfl⟩)
  · apply Submodule.span_le.mpr
    rintro y (hd | ⟨⟨i,j⟩,rfl⟩)
    · exact Submodule.subset_span (Or.inl (Submodule.subset_span (Or.inl hd)))
    · cases i using Fin.cases with
      | zero => exact Submodule.subset_span (Or.inr ⟨j,rfl⟩)
      | succ t => exact Submodule.subset_span (Or.inl (Submodule.subset_span (Or.inr ⟨(t,j),rfl⟩)))

def splitChoice {m spare : ℕ} :
    ((Fin (m+1) → Fin 4) × Bits spare) ≃ (Fin 4 × ((Fin m → Fin 4) × Bits spare)) where
  toFun p := (p.1 0,(fun i => p.1 i.succ,p.2))
  invFun p := (Fin.cons p.1 p.2.1,p.2.2)
  left_inv p := Prod.ext (Fin.cons_self_tail _) rfl
  right_inv p := by simp

theorem spare_dom {Y : Type*} [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Module F Y]
    {spare : ℕ} (D : Bits spare →ₗ[F] Y) (onto : Function.Surjective D) :
    let f := Module.finrank F Y
    f ≤ spare ∧ dominated (fun y => (univ.filter (fun x => D x = y)).card)
      (fun _ : Fin (2^f) => 2^(spare-f)) := by
  classical
  let f := Module.finrank F Y
  let e : Y ≃ₗ[F] Bits f := LinearEquiv.ofFinrankEq (R:=F) _ (Bits f) (by simp [Bits,Module.finrank_pi,f])
  let Ds := e.toLinearMap.comp D
  have hs : Function.Surjective Ds := e.surjective.comp onto
  have dim := Ds.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs,finrank_top] at dim
  have dd : f + Module.finrank F Ds.ker = spare := by simpa [Bits,Module.finrank_pi] using dim
  have hmass (y : Y) : (univ.filter (fun x => D x=y)).card = 2^(spare-f) := by
    have hh := uniform_spare Ds hs {e y}
    simpa [Ds] using hh
  refine ⟨by omega,?_⟩
  intro S
  have cardY : Fintype.card Y = 2^f := by rw [Fintype.card_congr e.toEquiv]; simp [Bits,F,ZMod.card]
  obtain ⟨T,_,he⟩ := exists_subset_card_eq (s:=(univ : Finset (Fin (2^f)))) (n:=S.card)
    (by simpa [← cardY] using card_le_univ S)
  exact ⟨T,he.le,by simp [hmass,he,f]⟩

theorem upper_tree (m : ℕ) {spare : ℕ} {Y : Type*} [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] [Module F Y] (D : Bits spare →ₗ[F] Y) (tab : Fin m → Fin 4 → Y)
    (zero : ∀ i, tab i 0=0) (span : fullSpan D tab = ⊤) :
    ∃ (f : ℕ) (rs : List ℕ), f ≤ spare ∧ rs.length=m ∧ (∀ r ∈ rs,r<4) ∧
      f+rs.sum=Module.finrank F Y ∧
      dominated (fun y => (univ.filter (fun p => history D tab p = y)).card)
        (treeMass f (2^(spare-f)) rs) := by
  classical
  induction m generalizing Y with
  | zero =>
    have emptyRange : Set.range (fun p : Fin 0 × Fin 4 => tab p.1 p.2) = ∅ := by
      ext y
      simp only [Set.mem_range,Set.mem_empty_iff_false,iff_false]
      rintro ⟨p,_⟩
      exact Fin.elim0 p.1
    have hr : LinearMap.range D = ⊤ := by simpa [fullSpan,emptyRange,← LinearMap.coe_range] using span
    obtain ⟨hf,hd⟩ := spare_dom D (LinearMap.range_eq_top.mp hr)
    refine ⟨Module.finrank F Y,[],hf,rfl,by simp,by simp,?_⟩
    intro S
    obtain ⟨T,ht,hh⟩ := hd S
    refine ⟨T,ht,?_⟩
    let e : ((Fin 0 → Fin 4) × Bits spare) ≃ Bits spare :=
      ⟨Prod.snd,fun x => (0,x),fun p => Prod.ext (Subsingleton.elim _ _) rfl,fun _ => rfl⟩
    have counts (y : Y) : (univ.filter (fun p => history D tab p = y)).card =
        (univ.filter (fun x => D x = y)).card := by
      simp only [history,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
      exact reindex_filter e (fun x => D x = y)
    rw [show (fun y => (univ.filter (fun p => history D tab p = y)).card) =
      (fun y => (univ.filter (fun x => D x=y)).card) from funext counts]
    exact hh
  | succ m ih =>
    let tail (i : Fin m) := tab i.succ
    let V := fullSpan D tail
    obtain ⟨D',tab',hd,ht,hs⟩ := subspace_data D tail
    have hz (i : Fin m) : tab' i 0 = 0 := by apply Subtype.ext; rw [ht]; exact zero i.succ
    obtain ⟨f,rs,hf,hl,hr,hsum,hdom⟩ := ih D' tab' hz hs
    letI := treeFinite f rs
    obtain ⟨r,hrank,hfour,hext⟩ := extension_bound V (history D' tab') (tab 0)
      (treeMass f (2^(spare-f)) rs) hdom ⟨0,zero 0⟩ (span_head D tab span)
    refine ⟨f,r::rs,hf,by simp [hl],?_,?_,?_⟩
    · intro t hm
      rcases List.mem_cons.mp hm with rfl | h
      · simpa using hfour
      · exact hr t h
    · simp only [List.sum_cons]
      calc
        _ = (f+rs.sum)+r := by omega
        _ = Module.finrank F V+r := congrArg (·+r) hsum
        _ = _ := hrank
    · have he (p : ((Fin (m+1) → Fin 4) × Bits spare)) :
          history D tab p = tab 0 (splitChoice p).1 + (history D' tab' (splitChoice p).2).val := by
        simp only [history, splitChoice, Equiv.coe_fn_mk, Submodule.coe_add, Submodule.coe_sum,hd,ht]
        rw [Fin.sum_univ_succ]
        dsimp [tail]
        abel
      have counts (y : Y) : (univ.filter (fun p => history D tab p = y)).card =
          (univ.filter (fun p : Fin 4 × ((Fin m → Fin 4) × Bits spare) =>
            tab 0 p.1 + (history D' tab' p.2).val = y)).card := by
        simp only [he]
        exact reindex_filter (splitChoice (m:=m) (spare:=spare))
          (fun p : Fin 4 × ((Fin m → Fin 4) × Bits spare) => tab 0 p.1 + (history D' tab' p.2).val = y)
      intro S
      obtain ⟨T,hT,hv⟩ := hext S
      refine ⟨T,hT,?_⟩
      simp only [counts]
      simp only [Fintype.card_fin] at hv
      exact hv

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954
open Finset

def decodeBits (h : Fin 4) (b : Bool) : F :=
  if b then (h.val / 2 : ℕ) else (h.val % 2 : ℕ)

def encodeBits (p : Bool → F) : Fin 4 :=
  ⟨(p false).val + 2*(p true).val, by
    have h₀ := ZMod.val_lt (p false)
    have h₁ := ZMod.val_lt (p true)
    omega⟩

def bitEquiv : Fin 4 ≃ (Bool → F) where
  toFun := decodeBits
  invFun := encodeBits
  left_inv := by decide
  right_inv := by decide

def recordEquiv (m spare : ℕ) : ((Fin m → Fin 4) × Bits spare) ≃ (Operands m × Bits spare) :=
  (Equiv.piCongrRight (fun _ => bitEquiv)).prodCongr (Equiv.refl _)

def tableOf {m s : ℕ} (a b t : Fin m → Bits s) (i : Fin m) (h : Fin 4) :=
  (decodeBits h false) • a i + (decodeBits h true) • b i +
    (decodeBits h false * decodeBits h true) • t i

theorem table_zero {m s : ℕ} (a b t : Fin m → Bits s) (i : Fin m) : tableOf a b t i 0 = 0 := by
  simp [tableOf,decodeBits]

theorem dictionary_apply {m spare s : ℕ} (D : Bits spare →ₗ[F] Bits s)
    (a b t : Fin m → Bits s) (p : (Fin m → Fin 4) × Bits spare) :
    columnMap D a b t (recordEquiv _ _ p, blocks (recordEquiv _ _ p)) =
      history D (tableOf a b t) p := rfl

theorem dictionary_rank {m spare s : ℕ} (D : Bits spare →ₗ[F] Bits s)
    (a b t : Fin m → Bits s) :
    Function.Surjective (columnMap D a b t) ↔ fullSpan D (tableOf a b t)=⊤ := by
  classical
  let P := columnMap D a b t
  let V := fullSpan D (tableOf a b t)
  have da (i : Fin m) : tableOf a b t i 1 = a i := by simp [tableOf,decodeBits]
  have db (i : Fin m) : tableOf a b t i 2 = b i := by simp [tableOf,decodeBits]
  have dt (i : Fin m) : tableOf a b t i 3 = a i + b i + t i := by simp [tableOf,decodeBits]
  have mem (i : Fin m) (h : Fin 4) : tableOf a b t i h ∈ V :=
    Submodule.subset_span (Or.inr ⟨(i,h),rfl⟩)
  have dmem (x : Bits spare) : D x ∈ V := Submodule.subset_span (Or.inl ⟨x,rfl⟩)
  constructor
  · intro onto
    apply top_unique
    intro y _
    obtain ⟨p,rfl⟩ := onto y
    apply V.add_mem (dmem p.1.2)
    apply V.sum_mem
    intro i _
    have ma : a i ∈ V := da i ▸ mem i 1
    have mb : b i ∈ V := db i ▸ mem i 2
    have mt : t i ∈ V := by
      have h := V.sub_mem (dt i ▸ mem i 3) (V.add_mem ma mb)
      simpa using h
    exact V.add_mem (V.add_mem (V.smul_mem _ ma) (V.smul_mem _ mb)) (V.smul_mem _ mt)
  · intro h
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← h]
    apply Submodule.span_le.mpr
    rintro y (⟨x,rfl⟩ | ⟨⟨i,j⟩,rfl⟩)
    · refine ⟨((0,x),0),?_⟩
      simp [columnMap]
    · refine ⟨((Pi.single i (decodeBits j),0), Pi.single i (decodeBits j false*decodeBits j true)),?_⟩
      simp [columnMap,tableOf,Pi.single_apply,Finset.sum_add_distrib,ite_apply,ite_smul]

theorem arbitrary_table {m s : ℕ} (tab : Fin m → Fin 4 → Bits s)
    (zero : ∀ i, tab i 0=0) :
    tableOf (fun i => tab i 1) (fun i => tab i 2) (fun i => tab i 3-tab i 1-tab i 2) = tab := by
  funext i j
  fin_cases j <;> simp [tableOf,decodeBits,zero] <;> abel

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954
open Finset

def digitCons (q n : ℕ) : (Fin (q+1) × (Fin n → Option (Fin q))) ≃
    (Fin (n+1) → Option (Fin q)) where
  toFun p := Fin.cons (finSuccEquiv q p.1) p.2
  invFun x := ((finSuccEquiv q).symm (x 0),fun i => x i.succ)
  left_inv p := by simp
  right_inv x := by simp only [Equiv.apply_symm_apply]; exact Fin.cons_self_tail x

theorem blanks_more {q n : ℕ} (j : Fin (q+1)) (x : Fin n → Option (Fin q)) :
    (blanks (digitCons q n (j,x))).card =
      (if j.val=0 then 1 else 0) + (blanks x).card := by
  have card_as_sum {k : ℕ} (z : Fin k → Option (Fin q)) : (blanks z).card =
      ∑ i, if z i = none then 1 else 0 := by simp [blanks]
  simp only [card_as_sum,Fin.sum_univ_succ,digitCons,Equiv.coe_fn_mk,
    Fin.cons_zero,Fin.cons_succ]
  cases j using Fin.cases <;> simp

def putOne (f b c d : ℕ) : Fin 2 × ProfileIndex f b c d ≃ ProfileIndex f (b+1) c d where
  toFun p := (p.2.1,digitCons 1 b (p.1,p.2.2.1),p.2.2.2)
  invFun u := (((digitCons 1 b).symm u.2.1).1,u.1,((digitCons 1 b).symm u.2.1).2,u.2.2)
  left_inv := by rintro ⟨j,z,x,y⟩; simp
  right_inv := by rintro ⟨z,x,y⟩; simp

def putTwo (f b c d : ℕ) : Fin 3 × ProfileIndex f b c d ≃ ProfileIndex f b (c+1) d where
  toFun p := (p.2.1,p.2.2.1,digitCons 2 c (p.1,p.2.2.2))
  invFun u := (((digitCons 2 c).symm u.2.2).1,u.1,u.2.1,((digitCons 2 c).symm u.2.2).2)
  left_inv := by rintro ⟨j,z,x,y⟩; simp
  right_inv := by rintro ⟨z,x,y⟩; simp

def putThree (f b c d : ℕ) : Fin 4 × ProfileIndex f b c d ≃ ProfileIndex f b c (d+1) :=
  let e : Fin 4 × Fin (2^f*4^d) ≃ Fin (2^f*4^(d+1)) :=
    finProdFinEquiv.trans (finCongr (by rw [pow_succ]; ring))
  { toFun := fun p => (e (p.1,p.2.1),p.2.2)
    invFun := fun u => ((e.symm u.1).1,(e.symm u.1).2,u.2)
    left_inv := by rintro ⟨j,z,x,y⟩; simp
    right_inv := by rintro ⟨z,x,y⟩; simp }

def putZero (f b c d : ℕ) : Fin 1 × ProfileIndex f b c d ≃ ProfileIndex f b c d where
  toFun := Prod.snd
  invFun u := (0,u)
  left_inv p := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl

theorem putOne_mass {f b c d t : ℕ} (j : Fin 2) (u : ProfileIndex f b c d) :
    mass t (putOne f b c d (j,u)) = (if j.val=0 then 3 else 1)*mass t u := by
  simp only [mass,putOne,Equiv.coe_fn_mk,blanks_more,pow_add]
  split <;> simp <;> ring

theorem putTwo_mass {f b c d t : ℕ} (j : Fin 3) (u : ProfileIndex f b c d) :
    mass t (putTwo f b c d (j,u)) = (if j.val=0 then 2 else 1)*mass t u := by
  simp only [mass,putTwo,Equiv.coe_fn_mk,blanks_more,pow_add]
  split <;> simp <;> ring

def emptyProfile (f : ℕ) : Fin (2^f) ≃ ProfileIndex f 0 0 0 where
  toFun j := (Fin.cast (by simp) j,Fin.elim0,Fin.elim0)
  invFun u := Fin.cast (by simp) u.1
  left_inv _ := rfl
  right_inv u := Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

theorem group_tree (f base : ℕ) (rs : List ℕ) (hr : ∀ r ∈ rs, r<4) :
    ∃ a b c d : ℕ, a+b+c+d=rs.length ∧ b+2*c+3*d=rs.sum ∧
      ∃ e : Tree f rs ≃ ProfileIndex f b c d, ∀ u,
        treeMass f base rs u = mass (base*4^a) (e u) := by
  induction rs with
  | nil =>
    refine ⟨0,0,0,0,rfl,rfl,emptyProfile f,?_⟩
    intro u
    simp [mass,blanks,treeMass]
  | cons r rs ih =>
    obtain ⟨a,b,c,d,hl,hs,e,hm⟩ := ih (fun i hi => hr i (List.mem_cons_of_mem r hi))
    have hsmall := hr r List.mem_cons_self
    interval_cases r
    · let p := ((Equiv.refl (Fin 1)).prodCongr e).trans (putZero f b c d)
      refine ⟨a+1,b,c,d,by simp; omega,by simpa using hs,p,?_⟩
      rintro ⟨j,u⟩
      have hj : j.val=0 := by omega
      change (if j.val=0 then 4-0 else 1)*treeMass f base rs u = mass (base*4^(a+1)) (e u)
      rw [hm]
      simp [hj,mass,pow_succ] <;> ring
    · let p := ((Equiv.refl (Fin 2)).prodCongr e).trans (putOne f b c d)
      refine ⟨a,b+1,c,d,by simp; omega,by simp; omega,p,?_⟩
      rintro ⟨j,u⟩
      change (if j.val=0 then 4-1 else 1)*treeMass f base rs u = mass _ (putOne _ _ _ _ (j,e u))
      rw [hm,putOne_mass]
    · let p := ((Equiv.refl (Fin 3)).prodCongr e).trans (putTwo f b c d)
      refine ⟨a,b,c+1,d,by simp; omega,by simp; omega,p,?_⟩
      rintro ⟨j,u⟩
      change (if j.val=0 then 4-2 else 1)*treeMass f base rs u = mass _ (putTwo _ _ _ _ (j,e u))
      rw [hm,putTwo_mass]
    · let p := ((Equiv.refl (Fin 4)).prodCongr e).trans (putThree f b c d)
      refine ⟨a,b,c,d+1,by simp; omega,by simp; omega,p,?_⟩
      rintro ⟨j,u⟩
      change (if j.val=0 then 4-3 else 1)*treeMass f base rs u = mass _ (putThree _ _ _ _ (j,e u))
      simp [hm,putThree,mass]

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954
open Finset

theorem dictionary_count {m spare s : ℕ} (D : Bits spare →ₗ[F] Bits s)
    (a b t : Fin m → Bits s) (S : Finset (Bits s)) :
    (univ.filter (fun x => columnMap D a b t (x,blocks x) ∈ S)).card =
      ∑ y ∈ S, (univ.filter (fun p => history D (tableOf a b t) p=y)).card := by
  rw [sum_card_fiberwise_eq_card_filter]
  symm
  exact reindex_filter (recordEquiv m spare) (fun x => columnMap D a b t (x,blocks x) ∈ S)

theorem upper_blocks {m spare s budget goal : ℕ}
    (h : coverData (s:=s) (blocks (m:=m) (d:=spare)) budget goal) :
    blockPrediction m spare s budget goal := by
  classical
  obtain ⟨P,S,hP,hS,hg⟩ := h
  obtain ⟨D,a,b,t,rfl⟩ := every_projection P
  obtain ⟨f,rs,hf,hl,hr,hs,hd⟩ := upper_tree m D (tableOf a b t) (table_zero a b t)
    ((dictionary_rank D a b t).mp hP)
  obtain ⟨aa,bb,cc,dd,h₁,h₂,e,he⟩ := group_tree f (2^(spare-f)) rs hr
  obtain ⟨T,hT,hm⟩ := hd S
  have dim : f+rs.sum=s := by simpa [Bits,Module.finrank_pi] using hs
  refine ⟨f,aa,bb,cc,dd,h₁.trans hl,hf,by omega,T.map e.toEmbedding,?_,?_⟩
  · simpa using hT.trans hS
  · rw [dictionary_count] at hg
    simpa only [sum_map,Equiv.toEmbedding_apply,← he] using hg.trans hm

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954
open Finset

def realized {I : Type} (spare m s : ℕ) (w : I → ℕ) : Prop :=
  ∃ (D : Bits spare →ₗ[F] Bits s) (tab : Fin m → Fin 4 → Bits s) (key : I ↪ Bits s),
    (∀ i, tab i 0=0) ∧ fullSpan D tab=⊤ ∧
    ∀ u, (univ.filter (fun p => history D tab p=key u)).card = w u

theorem realized_relabel {A B : Type} {spare m s : ℕ} {w : A → ℕ} {v : B → ℕ}
    (h : realized spare m s w) (e : A ≃ B) (he : ∀ u,w u=v (e u)) :
    realized spare m s v := by
  obtain ⟨D,tab,k,hz,hs,hw⟩ := h
  refine ⟨D,tab,e.symm.toEmbedding.trans k,hz,hs,fun u => (hw (e.symm u)).trans ?_⟩
  simpa using he (e.symm u)

theorem realized_base {f spare : ℕ} (hf : f≤spare) :
    realized spare 0 f (fun _ : Fin (2^f) => 2^(spare-f)) := by
  classical
  obtain ⟨D,hd⟩ := uniform_base_map hf
  let e : Fin (2^f) ≃ Bits f := (Fintype.equivFinOfCardEq (by simp [Bits,F,ZMod.card])).symm
  refine ⟨D,(fun _ _ => 0),e.toEmbedding,by simp,?_,?_⟩
  · apply top_unique
    intro y _
    exact Submodule.subset_span (Or.inl (hd y))
  · intro u
    let t : ((Fin 0 → Fin 4) × Bits spare) ≃ Bits spare :=
      ⟨Prod.snd,fun x => (0,x),fun p => Prod.ext (Subsingleton.elim _ _) rfl,fun _ => rfl⟩
    have eq := reindex_filter t (fun x => D x=e u)
    have hmass := uniform_spare D hd {e u}
    simp only [history,Finset.sum_const_zero,add_zero]
    exact eq.trans (by simpa using hmass)

def slot (r : ℕ) (j : Fin 4) : Fin (r+1) := if h : j.val<r+1 then ⟨j.val,h⟩ else 0

def tag (r : ℕ) : Fin (r+1) → Bits r := Fin.cases 0 (fun i => Pi.single i 1)

theorem slot_card (r : ℕ) (hr : r<4) (i : Fin (r+1)) :
    (univ.filter (fun j => slot r j=i)).card = if i.val=0 then 4-r else 1 := by
  interval_cases r <;> revert i <;> decide

theorem slot_tag_inj (r : ℕ) (hr : r<4) : Function.Injective (tag r) := by
  interval_cases r <;> decide

theorem key_product_count {A B X Y : Type*} [Fintype A] [Fintype B] [DecidableEq X] [DecidableEq Y]
    (g : A → X) (h : B → Y) (x : X) (y : Y) :
    (univ.filter (fun p : A × B => (g p.1,h p.2)=(x,y))).card =
      (univ.filter (fun a => g a=x)).card*(univ.filter (fun b => h b=y)).card := by
  classical
  rw [← Finset.card_product]
  congr 1
  ext p
  simp

theorem realized_more {I : Type} {spare m s : ℕ} {w : I → ℕ} (h : realized spare m s w)
    (r : ℕ) (hr : r<4) : realized spare (m+1) (r+s) (extendMass r 4 w) := by
  classical
  obtain ⟨D,tab,k,hz,hs,hw⟩ := h
  let e := LinearEquiv.ofFinrankEq (R:=F) (Bits r × Bits s) (Bits (r+s))
    (by simp [Bits,Module.finrank_prod,Module.finrank_pi])
  let L : Bits r →ₗ[F] Bits (r+s) := e.toLinearMap.comp (LinearMap.inl F _ _)
  let R : Bits s →ₗ[F] Bits (r+s) := e.toLinearMap.comp (LinearMap.inr F _ _)
  let v (j : Fin 4) := tag r (slot r j)
  let tabNew : Fin (m+1) → Fin 4 → Bits (r+s) :=
    Fin.cons (fun j => L (v j)) (fun i j => R (tab i j))
  let kNew : (Fin (r+1) × I) ↪ Bits (r+s) :=
    (Function.Embedding.prodMap ⟨tag r,slot_tag_inj r hr⟩ k).trans e.toEquiv.toEmbedding
  refine ⟨R.comp D,tabNew,kNew,?_,?_,?_⟩
  · intro i
    cases i using Fin.cases with
    | zero => simp [tabNew,v,slot,tag]
    | succ i => simp [tabNew,hz]
  · let V := fullSpan (R.comp D) tabNew
    have dr (p : Bits spare) : R (D p) ∈ V := Submodule.subset_span (Or.inl ⟨p,rfl⟩)
    have tr (i : Fin m) (j : Fin 4) : R (tab i j) ∈ V :=
      Submodule.subset_span (Or.inr ⟨(i.succ,j),by simp [tabNew]⟩)
    have allR (y : Bits s) : R y ∈ V := by
      have hle : fullSpan D tab ≤ V.comap R := by
        apply Submodule.span_le.mpr
        rintro z (⟨x,rfl⟩ | ⟨⟨i,j⟩,rfl⟩)
        · exact dr x
        · exact tr i j
      apply hle
      simp [hs]
    have eigen (i : Fin r) : L (Pi.single i 1) ∈ V := by
      let j : Fin 4 := ⟨i.val+1,by omega⟩
      have jh : slot r j = i.succ := by ext; simp [slot,j,i.isLt]
      exact Submodule.subset_span (Or.inr ⟨(0,j),by simp [tabNew,v,jh,tag]⟩)
    have allL (x : Bits r) : L x ∈ V := by
      have ids : (∑ i : Fin r, x i • Pi.single i (1:F)) = x := by
        funext j
        simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul,mul_ite]
      rw [← ids,map_sum]
      exact V.sum_mem (fun i _ => by rw [map_smul]; exact V.smul_mem _ (eigen i))
    apply top_unique
    intro z _
    obtain ⟨⟨x,y⟩,rfl⟩ := e.surjective z
    convert V.add_mem (allL x) (allR y) using 1
    simp [L,R,← map_add]
  · rintro ⟨i,u⟩
    have hx (x : (Fin (m+1) → Fin 4) × Bits spare) :
        history (R.comp D) tabNew x =
          e (v (splitChoice x).1,history D tab (splitChoice x).2) := by
      simp only [history,LinearMap.comp_apply,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,
        tabNew,splitChoice,Equiv.coe_fn_mk]
      simp [L,R,← map_sum,← map_add]
      apply Prod.ext <;> simp [Prod.fst_sum,Prod.snd_sum]
    have hc : (univ.filter (fun p => history (R.comp D) tabNew p=kNew (i,u))).card =
        (univ.filter (fun p : Fin 4 × ((Fin m → Fin 4) × Bits spare) =>
        (slot r p.1,history D tab p.2)=(i,k u))).card := by
      have eq (x : (Fin (m+1) → Fin 4) × Bits spare) :
          history (R.comp D) tabNew x=kNew (i,u) ↔
            (slot r (splitChoice x).1,history D tab (splitChoice x).2)=(i,k u) := by
        rw [hx]
        change e (_,_) = e (_,_) ↔ _
        simp [v,Prod.ext_iff,(slot_tag_inj r hr).eq_iff]
      simp only [eq]
      exact reindex_filter (splitChoice (m:=m) (spare:=spare)) (fun p =>
        (slot r p.1,history D tab p.2)=(i,k u))
    rw [hc,key_product_count,slot_card r hr,hw]
    rfl

end PEqualNP.Outside.L_meta_29954

namespace PEqualNP.Outside.L_meta_29954
open Finset

theorem profile_realized {spare f : ℕ} (hf : f≤spare) (a b c d : ℕ) :
    realized spare (a+b+c+d) (f+b+2*c+3*d)
      (mass (2^(spare-f)*4^a) : ProfileIndex f b c d → ℕ) := by
  let Good (a b c d : ℕ) := realized spare (a+b+c+d) (f+b+2*c+3*d)
    (mass (2^(spare-f)*4^a) : ProfileIndex f b c d → ℕ)
  change Good a b c d
  have start : Good 0 0 0 0 := by
    simp only [Good,Nat.add_zero,Nat.mul_zero,pow_zero,mul_one]
    apply realized_relabel (realized_base hf) (emptyProfile f)
    intro j
    simp [mass,blanks]
  have zeroStep {i : ℕ} (h : Good i 0 0 0) : Good (i+1) 0 0 0 := by
    unfold Good at *
    simp only [Nat.add_zero,Nat.mul_zero] at *
    have ht := realized_more h 0 (by decide)
    simp only [Nat.zero_add] at ht
    apply realized_relabel ht (putZero f 0 0 0)
    rintro ⟨j,u⟩
    simp [putZero,mass,extendMass,pow_succ] <;> ring
  have oneStep {i : ℕ} (h : Good a i 0 0) : Good a (i+1) 0 0 := by
    unfold Good at *
    simp only [Nat.add_zero,Nat.mul_zero] at *
    have ht := realized_more h 1 (by decide)
    rw [show a+i+1=a+(i+1) by omega,show 1+(f+i)=f+(i+1) by omega] at ht
    apply realized_relabel ht (putOne f i 0 0)
    rintro ⟨j,u⟩
    rw [putOne_mass]
    rfl
  have twoStep {i : ℕ} (h : Good a b i 0) : Good a b (i+1) 0 := by
    unfold Good at *
    simp only [Nat.add_zero,Nat.mul_zero] at *
    have ht := realized_more h 2 (by decide)
    rw [show a+b+i+1=a+b+(i+1) by omega,show 2+(f+b+2*i)=f+b+2*(i+1) by omega] at ht
    apply realized_relabel ht (putTwo f b i 0)
    rintro ⟨j,u⟩
    rw [putTwo_mass]
    rfl
  have threeStep {i : ℕ} (h : Good a b c i) : Good a b c (i+1) := by
    unfold Good at *
    have ht := realized_more h 3 (by decide)
    rw [show a+b+c+i+1=a+b+c+(i+1) by omega,
      show 3+(f+b+2*c+3*i)=f+b+2*c+3*(i+1) by omega] at ht
    apply realized_relabel ht (putThree f b c i)
    rintro ⟨j,u⟩
    simp [putThree,mass,extendMass]
  have ha : ∀ i, Good i 0 0 0 := fun i => Nat.rec (motive:=fun t => Good t 0 0 0)
    start (fun _ ih => zeroStep ih) i
  have hb : ∀ i, Good a i 0 0 := fun i => Nat.rec (motive:=fun t => Good a t 0 0)
    (ha a) (fun _ ih => oneStep ih) i
  have hc : ∀ i, Good a b i 0 := fun i => Nat.rec (motive:=fun t => Good a b t 0)
    (hb b) (fun _ ih => twoStep ih) i
  exact Nat.rec (motive:=fun t => Good a b c t) (hc c) (fun _ ih => threeStep ih) d

theorem lower_blocks {m spare s budget goal : ℕ} (h : blockPrediction m spare s budget goal) :
    coverData (s:=s) (blocks (m:=m) (d:=spare)) budget goal := by
  classical
  obtain ⟨f,a,b,c,d,rfl,hf,rfl,S,hS,hg⟩ := h
  obtain ⟨D,tab,k,hz,hs,hw⟩ := profile_realized hf a b c d
  let aa := fun i => tab i 1
  let bb := fun i => tab i 2
  let tt := fun i => tab i 3-tab i 1-tab i 2
  have eqtab : tableOf aa bb tt=tab := arbitrary_table tab hz
  refine ⟨columnMap D aa bb tt,S.map k,(dictionary_rank D aa bb tt).mpr (eqtab ▸ hs),?_,?_⟩
  · simpa using hS
  · rw [dictionary_count,eqtab,Finset.sum_map]
    simpa only [hw] using hg

end PEqualNP.Outside.L_meta_29954

theorem PEqualNP.Outside.L_meta_29954 : (∀ (k m s budget goal : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let E := Fin m → F
  let Y := Fin s → F
  let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (n : Nat) (x : W) (j : Fin k) => x (ix (j.val+k-n % k))
  let mix := fun (b : Bool) (x : W) (j : Fin k) =>
    let d := if b then 2 else 1
    x j + x (ix (j.val+d)) + x (ix (j.val+k-d % k))
  ∀ (bank : Fin m → Bool) (site : Fin m → Fin k),
    let mixed := fun (i : Fin m) (base source : W) =>
      mix (bank i) (rot (if bank i then 3 else 1) source + base)
    let operand := fun (direction : W) (i : Fin m) (second : Bool) =>
      mixed i 0 direction (ix ((site i).val + (if second then 2 else 1)))
    Function.Surjective operand →
    ∀ (name c : Bool → W),
      let out := fun (key : W) (i : Fin m) =>
        let b := bank i
        let j := site i
        let y := mixed i (name b) key
        y j + (1+y (ix (j.val+1)))*y (ix (j.val+2)) +
          rot (if b then 4 else 0) key j + c b j
      let physical := fun (P : (W × E) →ₗ[F] Y) (S : Finset Y) =>
        ((Finset.univ : Finset W).filter (fun candidate => P (candidate,out candidate) ∈ S)).card
      (∃ (P : (W × E) →ₗ[F] Y) (S : Finset Y),
        Function.Surjective P ∧ S.card ≤ budget ∧ goal ≤ physical P S) ↔
      ∃ (f a b c₂ d : Nat),
        a+b+c₂+d = m ∧ f ≤ k-2*m ∧ f+b+2*c₂+3*d = s ∧
        let I := Fin (b+1) × Fin (c₂+1)
        let value := fun pair : I => 2^(k-2*m-f) * 4^a * 3^pair.1.val * 2^pair.2.val
        let copies := fun cell : I => 2^f * 4^d * b.choose cell.1.val *
          c₂.choose cell.2.val * 2^(c₂-cell.2.val)
        ∀ pivot : Option I, let z := pivot.elim 0 value
          goal ≤ budget*z + ∑ h : I, copies h * (value h-z)) := by
  apply PEqualNP.Outside.L_meta_29954.transfer
  intro m spare s budget goal
  exact ⟨PEqualNP.Outside.L_meta_29954.upper_blocks, PEqualNP.Outside.L_meta_29954.lower_blocks⟩
