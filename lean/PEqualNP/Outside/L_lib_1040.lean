import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1040_aux

namespace Geometry1040

abbrev F := ZMod 2
abbrev W (n : ℕ) := Fin n → F

def synd (n : ℕ) : W n →ₗ[F] (Fin 2 → F) where
  toFun x e := ∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0
  map_add' x y := by
    ext e
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split <;> simp
  map_smul' c x := by
    ext e
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split <;> simp

theorem synd_single {n : ℕ} (j : Fin n) (c : F) (e : Fin 2) :
    synd n (Pi.single j c) e = if j.val % 3 = e.val ∨ j.val % 3 = 2 then c else 0 := by
  change (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then Pi.single j c i else 0) = _
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ h
    simp [Pi.single_eq_of_ne h]
  · simp

theorem synd_surj {n : ℕ} (hn : 2 ≤ n) : Function.Surjective (synd n) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  intro y
  refine ⟨Pi.single a (y 0) + Pi.single b (y 1), ?_⟩
  rw [map_add]
  ext e
  fin_cases e <;> simp [synd_single, a, b]

theorem codeDimension {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank F (LinearMap.ker (synd n)) + 2 = n := by
  have h := LinearMap.finrank_range_add_finrank_ker (synd n)
  rw [LinearMap.range_eq_top.mpr (synd_surj hn)] at h
  simp at h
  omega

def ext0 {n : ℕ} (S : Finset (Fin n)) : (S → F) →ₗ[F] W n where
  toFun x i := if hi : i ∈ S then x ⟨i,hi⟩ else 0
  map_add' x y := by ext i; by_cases h : i ∈ S <;> simp [h]
  map_smul' c x := by ext i; by_cases h : i ∈ S <;> simp [h]

def checkOn {n : ℕ} (S : Finset (Fin n)) := (synd n).comp (ext0 S)

theorem ext0_single {n : ℕ} (S : Finset (Fin n)) (j : S) (c : F) :
    ext0 S (Pi.single j c) = Pi.single j.val c := by
  ext i
  by_cases hi : i = j.val
  · subst i; simp [ext0,j.property]
  · by_cases h : i ∈ S
    · have hne : (⟨i,h⟩ : S) ≠ j := fun h' => hi (congrArg Subtype.val h')
      simp [ext0,h,Pi.single_eq_of_ne hne,Pi.single_eq_of_ne hi]
    · simp [ext0,h,Pi.single_eq_of_ne hi]

theorem reSingle {n : ℕ} (S : Finset (Fin n)) (j : S) (c : F) (e : Fin 2) :
    checkOn S (Pi.single j c) e = if j.val.val % 3 = e.val ∨ j.val.val % 3 = 2 then c else 0 := by
  rw [checkOn,LinearMap.comp_apply,ext0_single,synd_single]

theorem supportLoss {n : ℕ} (S : Finset (Fin n)) (U : Submodule F (W n))
    (hc : U ≤ (synd n).ker) (hs : ∀ x ∈ U, ∀ i ∉ S, x i = 0) :
    Module.finrank F U + Module.finrank F (checkOn S).range ≤ S.card := by
  let f : U →ₗ[F] (checkOn S).ker := {
    toFun := fun x => ⟨fun j => x.val j.val, by
      change synd n (ext0 S (fun j => x.val j.val)) = 0
      have eqx : ext0 S (fun j => x.val j.val) = x.val := by
        ext i
        by_cases h : i ∈ S
        · simp [ext0,h]
        · simp [ext0,h,hs x x.property i h]
      rw [eqx]
      exact hc x.property⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have inj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · exact congrFun (congrArg Subtype.val h) ⟨i,hi⟩
    · rw [hs x x.property i hi,hs y y.property i hi]
  have h := LinearMap.finrank_le_finrank_of_injective inj
  have dim := LinearMap.finrank_range_add_finrank_ker (checkOn S)
  simp at dim
  omega

theorem color_surj : ∀ a b : Fin 3, a ≠ b → ∀ y : Fin 2 → F, ∃ u v : F, ∀ e : Fin 2,
    (if a.val = e.val ∨ a.val = 2 then u else 0) +
    (if b.val = e.val ∨ b.val = 2 then v else 0) = y e := by decide +kernel

theorem rankTwo {n : ℕ} (S : Finset (Fin n)) (j k : S)
    (hne : j.val.val % 3 ≠ k.val.val % 3) : Module.finrank F (checkOn S).range = 2 := by
  have sur : Function.Surjective (checkOn S) := by
    intro y
    let a : Fin 3 := ⟨j.val.val % 3, Nat.mod_lt _ (by decide)⟩
    let b : Fin 3 := ⟨k.val.val % 3, Nat.mod_lt _ (by decide)⟩
    obtain ⟨u,v,h⟩ := color_surj a b (fun eq => hne (congrArg Fin.val eq)) y
    refine ⟨Pi.single j u + Pi.single k v, ?_⟩
    rw [map_add]
    ext e
    simp only [Pi.add_apply,reSingle]
    exact h e
  rw [LinearMap.range_eq_top.mpr sur]
  simp

theorem rankOneLe {n : ℕ} (S : Finset (Fin n)) (j : S) : 1 ≤ Module.finrank F (checkOn S).range := by
  have ht : ∀ a : Fin 3, ∃ e : Fin 2, a.val = e.val ∨ a.val = 2 := by decide
  obtain ⟨e,h⟩ := ht ⟨j.val.val % 3,Nat.mod_lt _ (by decide)⟩
  change j.val.val % 3 = e.val ∨ j.val.val % 3 = 2 at h
  let y : (checkOn S).range := ⟨checkOn S (Pi.single j (1:F)), ⟨_,rfl⟩⟩
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨y,fun he => ?_⟩
  have hy := congrFun (congrArg Subtype.val he) e
  change checkOn S (Pi.single j (1:F)) e = 0 at hy
  simp [reSingle,h] at hy

end Geometry1040


namespace Geometry1040

def idx {t : ℕ} (ht : 0 < t) (j : ℕ) : Fin (3*t) := ⟨j % (3*t), Nat.mod_lt _ (by omega)⟩
def nx {t : ℕ} (ht : 0 < t) (i : Fin (3*t)) := idx ht (i.val+1)

theorem nx_val {t : ℕ} (ht : 0 < t) (i : Fin (3*t)) :
    (nx ht i).val = if i.val+1=3*t then 0 else i.val+1 := by
  change (i.val+1) % (3*t) = _
  split_ifs with h
  · simp [h]
  · exact Nat.mod_eq_of_lt (by omega)

theorem nx_inj {t : ℕ} (ht : 0 < t) : Function.Injective (nx ht) := by
  intro i j eq
  have h := congrArg Fin.val eq
  rw [nx_val,nx_val] at h
  apply Fin.ext
  split_ifs at h <;> omega

theorem nx_color {t : ℕ} (ht : 0 < t) (i : Fin (3*t)) :
    (nx ht i).val % 3 ≠ i.val % 3 := by
  rw [nx_val]
  split_ifs <;> omega

def mono {t : ℕ} (S : Finset (Fin (3*t))) :=
  ∀ i ∈ S, ∀ j ∈ S, i.val % 3 = j.val % 3

theorem mono_size {t : ℕ} (S : Finset (Fin (3*t))) (h : mono S) : S.card ≤ t := by
  let f : S → Fin t := fun i => ⟨i.val.val/3, by have hi := i.val.isLt; omega⟩
  have inj : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    apply Fin.ext
    have hh := h i i.property j j.property
    have hd : i.val.val/3 = j.val.val/3 := congrArg Fin.val he
    omega
  simpa using Fintype.card_le_of_injective f inj

theorem triple_card {n : ℕ} (S T A : Finset (Fin n))
    (hST : Disjoint S T) (hSA : Disjoint S A) (hTA : Disjoint T A) :
    S.card + T.card + A.card ≤ n := by
  rw [←Finset.card_union_of_disjoint hST,
      ←Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hSA,hTA⟩)]
  simpa using Finset.card_le_univ (S ∪ T ∪ A)

theorem mono_gap {t : ℕ} (ht : 0 < t) (S T : Finset (Fin (3*t))) (hST : Disjoint S T)
    (hstep : ∀ j ∈ T, nx ht j ∉ S) :
    (mono T → S.card+T.card+T.card ≤ 3*t) ∧
    (mono S → S.card+T.card+S.card ≤ 3*t) := by
  let f : Fin (3*t) ↪ Fin (3*t) := ⟨nx ht,nx_inj ht⟩
  have hSX : Disjoint S (T.map f) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨b,hbin,rfl⟩ := Finset.mem_map.mp hb
    exact hstep b hbin ha
  have avoid (R : Finset (Fin (3*t))) (hm : mono R) : Disjoint R (R.map f) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨b,hbin,rfl⟩ := Finset.mem_map.mp hb
    exact nx_color ht b (hm _ ha _ hbin)
  constructor
  · intro hm
    simpa using triple_card S T (T.map f) hST hSX (avoid T hm)
  · intro hm
    have hTS : Disjoint (T.map f) (S.map f) := by
      rw [Finset.disjoint_left]
      intro a hb ha
      obtain ⟨b,hbin,rfl⟩ := Finset.mem_map.mp hb
      obtain ⟨c,hc,hh⟩ := Finset.mem_map.mp ha
      exact Finset.disjoint_left.mp hST hc ((f.injective hh).symm ▸ hbin)
    simpa using triple_card S (T.map f) (S.map f) hSX (avoid S hm) hTS

theorem boundary_gap {t : ℕ} (ht : 0 < t) (S T : Finset (Fin (3*t)))
    (hs : S.Nonempty) (ht' : T.Nonempty) (hST : Disjoint S T) (hstep : ∀ j ∈ T, nx ht j ∉ S) :
    S.card + T.card + 1 ≤ 3*t := by
  classical
  by_contra! h
  have eq : S ∪ T = Finset.univ := by
    apply Finset.eq_univ_of_card
    have H := Finset.card_le_univ (S ∪ T)
    rw [Finset.card_union_of_disjoint hST] at H ⊢
    simp only [Fintype.card_fin] at H ⊢
    omega
  have closed {i} (hi : i ∈ T) : nx ht i ∈ T := by
    have hmem : nx ht i ∈ S ∪ T := eq ▸ Finset.mem_univ _
    exact (Finset.mem_union.mp hmem).resolve_left (hstep i hi)
  obtain ⟨i,hi⟩ := ht'
  obtain ⟨j,hj⟩ := hs
  have go (k : ℕ) : idx ht (i.val+k) ∈ T := by
    induction k with
    | zero =>
      convert hi using 1
      apply Fin.ext
      simp [idx,Nat.mod_eq_of_lt i.isLt]
    | succ k ih =>
      have hh := closed ih
      convert hh using 1
      apply Fin.ext
      simpa only [idx,nx,Nat.add_assoc] using
        (Nat.mod_add_mod (i.val+k) (3*t) 1).symm
  have reach := go (3*t-i.val+j.val)
  have same : idx ht (i.val + (3*t-i.val+j.val)) = j := by
    apply Fin.ext
    change (i.val + (3*t-i.val+j.val))%(3*t)=j.val
    rw [show i.val + (3*t-i.val+j.val) = j.val + 3*t by omega]
    simp [Nat.mod_eq_of_lt j.isLt]
  rw [same] at reach
  exact Finset.disjoint_left.mp hST hj reach

end Geometry1040
namespace Geometry1040

noncomputable def supp {n : ℕ} (U : Submodule F (W n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ x ∈ U, x i ≠ 0)

theorem mem_supp {n : ℕ} (U : Submodule F (W n)) (i : Fin n) :
    i ∈ supp U ↔ ∃ x ∈ U, x i ≠ 0 := by
  classical
  simp [supp]

theorem suppLoss {n : ℕ} (U : Submodule F (W n)) (hc : U ≤ (synd n).ker) :
    Module.finrank F U + Module.finrank F (checkOn (supp U)).range ≤ (supp U).card := by
  apply supportLoss _ U hc
  intro x hx i hi
  by_contra hn
  exact hi ((mem_supp U i).mpr ⟨x,hx,hn⟩)

theorem oneOrTwo {t : ℕ} (S : Finset (Fin (3*t))) (hs : S.Nonempty) :
    1 ≤ Module.finrank F (checkOn S).range ∧
      (¬mono S → 2 ≤ Module.finrank F (checkOn S).range) := by
  obtain ⟨j,hj⟩ := hs
  refine ⟨rankOneLe _ ⟨j,hj⟩,?_⟩
  intro h
  unfold mono at h
  push_neg at h
  obtain ⟨a,ha,b,hb,hab⟩ := h
  exact (rankTwo S ⟨a,ha⟩ ⟨b,hb⟩ hab).ge

theorem mixedBound {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t) (U V : Submodule F (W (3*t)))
    (hcU : U ≤ (synd (3*t)).ker) (hcV : V ≤ (synd (3*t)).ker)
    (hu : 0 < Module.finrank F U) (hv : 0 < Module.finrank F V)
    (ann : ∀ x ∈ U, ∀ y ∈ V, ∀ i, x i * y i = 0 ∧ x (nx ht i) * y i = 0) :
    Module.finrank F U + Module.finrank F V + (if t = 2 then 4 else 5) ≤ 3*t := by
  classical
  let S := supp U
  let T := supp V
  have us : Module.finrank F U + Module.finrank F (checkOn S).range ≤ S.card := suppLoss U hcU
  have vs : Module.finrank F V + Module.finrank F (checkOn T).range ≤ T.card := suppLoss V hcV
  have sn : S.Nonempty := Finset.card_pos.mp (by omega)
  have tn : T.Nonempty := Finset.card_pos.mp (by omega)
  have dst : Disjoint S T := by
    refine Finset.disjoint_left.mpr ?_
    intro i h1 h2
    obtain ⟨x,hx,xi⟩ := (mem_supp U i).mp h1
    obtain ⟨y,hy,yi⟩ := (mem_supp V i).mp h2
    exact mul_ne_zero xi yi (ann x hx y hy i).1
  have hstep : ∀ i ∈ T, nx ht i ∉ S := by
    intro i hi hn
    obtain ⟨x,hx,xi⟩ := (mem_supp U _).mp hn
    obtain ⟨y,hy,yi⟩ := (mem_supp V _).mp hi
    exact mul_ne_zero xi yi (ann x hx y hy i).2
  obtain ⟨s1,s2⟩ := oneOrTwo S sn
  obtain ⟨t1,t2⟩ := oneOrTwo T tn
  obtain ⟨gT,gS⟩ := mono_gap ht S T dst hstep
  by_cases a : mono S
  · by_cases b : mono T
    · have hS := mono_size S a
      have hT := mono_size T b
      split_ifs <;> omega
    · have H := t2 b
      have G := gS a
      split_ifs <;> omega
  · by_cases b : mono T
    · have H := s2 a
      have G := gT b
      split_ifs <;> omega
    · have H := s2 a
      have J := t2 b
      have G := boundary_gap ht S T sn tn dst hstep
      split_ifs <;> omega

end Geometry1040

namespace Geometry1040

def evalAt {n : ℕ} (U : Submodule F (W n)) (i : Fin n) : Module.Dual F U :=
  (LinearMap.proj i).comp U.subtype

def leftEval {t : ℕ} (ht : 0 < t) (P : Submodule F (W (3*t))) (s : Bool × Fin (3*t)) :=
  evalAt P (if s.1 then nx ht s.2 else s.2)

def rightEval {t : ℕ} (Q : Submodule F (W (3*t))) (s : Bool × Fin (3*t)) :=
  evalAt Q s.2

abbrev Live {t : ℕ} (ht : 0 < t) (P Q : Submodule F (W (3*t))) :=
  {s : Bool × Fin (3*t) // leftEval ht P s ≠ 0 ∧ rightEval Q s ≠ 0}

def forms {I A : Type*} [AddCommGroup A] [Module F A] (u : I → Module.Dual F A) :=
  Submodule.span F (Set.range u)

theorem annSlot {I A B : Type*} [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
    (l : I → Module.Dual F A) (r : I → Module.Dual F B)
    (x : A) (y : B) (i : I)
    (h : ∀ j, l j ≠ 0 → r j ≠ 0 → l j x = 0) : l i x * r i y = 0 := by
  by_cases a : l i = 0
  · simp [a]
  by_cases b : r i = 0
  · simp [b]
  simp [h i a b]

theorem effectiveRanks {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t) (P Q : Submodule F (W (3*t)))
    (hp : P ≤ (synd (3*t)).ker) (hq : Q ≤ (synd (3*t)).ker)
    (large : 3*t-1 ≤ Module.finrank F P + Module.finrank F Q)
    (np : 2 ≤ Module.finrank F P) (nq : 2 ≤ Module.finrank F Q) :
    let u := fun s : Live ht P Q => leftEval ht P s.val
    let v := fun s : Live ht P Q => rightEval Q s.val
    let a := Module.finrank F (forms u)
    let b := Module.finrank F (forms v)
    2 ≤ a ∧ 2 ≤ b ∧ (3 ≤ a ∨ 3 ≤ b) := by
  intro u v a b
  let RA := (forms u).dualCoannihilator
  let RB := (forms v).dualCoannihilator
  let U := RA.map P.subtype
  let V := RB.map Q.subtype
  have radA : a + Module.finrank F U = Module.finrank F P := by
    rw [show Module.finrank F U = Module.finrank F RA from Submodule.finrank_map_subtype_eq P RA]
    exact Subspace.finrank_add_finrank_dualCoannihilator_eq _
  have radB : b + Module.finrank F V = Module.finrank F Q := by
    rw [show Module.finrank F V = Module.finrank F RB from Submodule.finrank_map_subtype_eq Q RB]
    exact Subspace.finrank_add_finrank_dualCoannihilator_eq _
  have cup : U ≤ P := by
    rintro _ ⟨x,_,rfl⟩
    exact x.property
  have cvq : V ≤ Q := by
    rintro _ ⟨y,_,rfl⟩
    exact y.property
  have annA : ∀ x ∈ U, ∀ y ∈ Q, ∀ i, x i * y i = 0 ∧ x (nx ht i) * y i = 0 := by
    rintro _ ⟨x,hx,rfl⟩ y hy i
    have ann (s : Bool × Fin (3*t)) : leftEval ht P s x * rightEval Q s ⟨y,hy⟩ = 0 := by
      apply annSlot
      intro z hz hv
      exact (Submodule.mem_dualCoannihilator x).mp hx (u ⟨z,hz,hv⟩)
        (Submodule.subset_span ⟨⟨z,hz,hv⟩,rfl⟩)
    exact ⟨ann (false,i),ann (true,i)⟩
  have annB : ∀ x ∈ P, ∀ y ∈ V, ∀ i, x i * y i = 0 ∧ x (nx ht i) * y i = 0 := by
    rintro x hx _ ⟨y,hy,rfl⟩ i
    have ann (s : Bool × Fin (3*t)) : leftEval ht P s ⟨x,hx⟩ * rightEval Q s y = 0 := by
      rw [mul_comm]
      apply annSlot
      intro z hz hv
      exact (Submodule.mem_dualCoannihilator y).mp hy (v ⟨z,hv,hz⟩)
        (Submodule.subset_span ⟨⟨z,hv,hz⟩,rfl⟩)
    exact ⟨ann (false,i),ann (true,i)⟩
  have ga : 0 < Module.finrank F U → 3 ≤ a := by
    intro hu
    have g := mixedBound ht ht2 U Q (cup.trans hp) hq hu (by omega) annA
    split_ifs at g <;> omega
  have gb : 0 < Module.finrank F V → 3 ≤ b := by
    intro hv
    have g := mixedBound ht ht2 P V hp (cvq.trans hq) (by omega) hv annB
    split_ifs at g <;> omega
  omega

end Geometry1040

namespace Geometry1040

section
variable {A : Type*} [AddCommGroup A] [Module F A] [FiniteDimensional F A]
variable {I : Type*}

theorem varies (u : I → Module.Dual F A) (hu : 2 ≤ Module.finrank F (forms u)) :
    ∃ i j, u i ≠ u j := by
  classical
  by_contra! hn
  cases isEmpty_or_nonempty I with
  | inl h =>
    have he : Set.range u = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨i,rfl⟩
      exact isEmptyElim i
    have le : forms u ≤ (⊥ : Submodule F (Module.Dual F A)) := by
      apply Submodule.span_le.mpr
      rw [he]
      simp
    have z : Module.finrank F (forms u) ≤ 0 := (Submodule.finrank_mono le).trans_eq (by simp)
    omega
  | inr hi =>
    let i := hi.some
    have hle : forms u ≤ Submodule.span F ({u i} : Set _) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact Submodule.subset_span (by simp [hn j i])
    have h := Submodule.finrank_mono hle
    have H := finrank_span_le_card (R := F) ({u i} : Set _)
    simp at H
    omega

theorem jointSurj {k : ℕ} (L : Fin k → Module.Dual F A)
    (hk : k ≤ Module.finrank F (forms L)) : Function.Surjective (LinearMap.pi L) := by
  have he : (LinearMap.pi L).ker = (forms L).dualCoannihilator := by
    ext x
    rw [LinearMap.mem_ker,Submodule.mem_dualCoannihilator]
    constructor
    · intro h f hf
      have hh : forms L ≤ (Module.Dual.eval F A x).ker := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j,rfl⟩
        exact congrFun h j
      exact hh hf
    · intro h
      funext i
      exact h (L i) (Submodule.subset_span ⟨i,rfl⟩)
  have D := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi L)
  have A' := Subspace.finrank_add_finrank_dualCoannihilator_eq (forms L)
  rw [he] at D
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  have H := Submodule.finrank_le (LinearMap.pi L).range
  simp at H ⊢
  omega

theorem pairDim (u v : Module.Dual F A) (hu : u ≠ 0) (hv : v ≠ 0) (hd : u ≠ v) :
    2 ≤ Module.finrank F (forms ![u,v]) := by
  have ha : u ∈ forms ![u,v] := Submodule.subset_span ⟨(0:Fin 2),rfl⟩
  have hb : v ∈ forms ![u,v] := Submodule.subset_span ⟨(1:Fin 2),rfl⟩
  have lt : Submodule.span F ({u} : Set _) < forms ![u,v] := by
    apply lt_of_le_of_ne
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ha)
    · intro he
      rw [←he,Submodule.mem_span_singleton] at hb
      obtain ⟨a,ha⟩ := hb
      have hcases : ∀ w : F, w = 0 ∨ w = 1 := by decide
      rcases hcases a with rfl|rfl <;> simp_all
  have ht := Submodule.finrank_lt_finrank_of_lt lt
  rw [finrank_span_singleton hu] at ht
  exact ht

theorem third {u : I → Module.Dual F A} (i j : I)
    (hthree : 3 ≤ Module.finrank F (forms u)) (hp : 2 ≤ Module.finrank F (forms ![u i,u j])) :
    ∃ k, Function.Surjective (LinearMap.pi ![u i,u j,u k]) := by
  classical
  let S := forms ![u i,u j]
  have two : Module.finrank F S ≤ 2 := by
    have E : Set.range ![u i,u j] = ({u i,u j} : Set _) := by
      ext v
      constructor
      · rintro ⟨z,rfl⟩; fin_cases z <;> simp
      · rintro (rfl|h)
        · exact ⟨(0:Fin 2),rfl⟩
        · exact ⟨(1:Fin 2), h.symm⟩
    have le : S ≤ Submodule.span F ({u i,u j} : Set _) := by
      apply Submodule.span_le.mpr
      rw [E]
      exact Submodule.subset_span
    exact (Submodule.finrank_mono le).trans ((finrank_span_le_card (R := F) _).trans (by simpa using (Finset.card_le_two (a:=u i) (b:=u j))))
  have hout : ∃ k, u k ∉ S := by
    by_contra! h
    have hle : forms u ≤ S := Submodule.span_le.mpr (by rintro _ ⟨z,rfl⟩; exact h z)
    have hm := Submodule.finrank_mono hle
    omega
  obtain ⟨k,hk⟩ := hout
  refine ⟨k,jointSurj _ ?_⟩
  have hlt : S < forms ![u i,u j,u k] := by
    apply lt_of_le_of_ne
    · apply Submodule.span_le.mpr
      rintro _ ⟨z,rfl⟩
      fin_cases z
      · exact Submodule.subset_span ⟨(0:Fin 3),rfl⟩
      · exact Submodule.subset_span ⟨(1:Fin 3),rfl⟩
    · intro eq
      exact hk (eq ▸ Submodule.subset_span ⟨(2:Fin 3),rfl⟩)
  have hl := Submodule.finrank_lt_finrank_of_lt hlt
  change 2 ≤ Module.finrank F S at hp
  omega

end



private theorem two_independent_slots {I A B : Type*} (u : I → A) (v : I → B)
    (leftVaries : ∃ j k, u j ≠ u k) (rightVaries : ∃ j k, v j ≠ v k) :
    ∃ j k, u j ≠ u k ∧ v j ≠ v k := by
  classical
  by_contra! same
  obtain ⟨a,b,hab⟩ := leftVaries
  have v0 := same a b hab
  have flat (i : I) : v i = v a := by
    by_cases h : u i = u a
    · exact (same i b (h ▸ hab)).trans v0.symm
    · exact same i a h
  obtain ⟨p,q,h⟩ := rightVaries
  exact h ((flat p).trans (flat q).symm)
theorem goodSlots {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t) (P Q : Submodule F (W (3*t)))
    (hp : P ≤ (synd (3*t)).ker) (hq : Q ≤ (synd (3*t)).ker)
    (large : 3*t-1 ≤ Module.finrank F P + Module.finrank F Q)
    (np : 2 ≤ Module.finrank F P) (nq : 2 ≤ Module.finrank F Q) :
    let u := fun s : Live ht P Q => leftEval ht P s.val
    let v := fun s : Live ht P Q => rightEval Q s.val
    ∃ i j k : Live ht P Q,
      (Function.Surjective (LinearMap.pi ![u i,u j,u k]) ∧ Function.Surjective (LinearMap.pi ![v i,v j])) ∨
      (Function.Surjective (LinearMap.pi ![v i,v j,v k]) ∧ Function.Surjective (LinearMap.pi ![u i,u j])) := by
  intro u v
  obtain ⟨hr,hs,hi⟩ := effectiveRanks ht ht2 P Q hp hq large np nq
  obtain ⟨i,j,di,dj⟩ := two_independent_slots u v (varies u hr) (varies v hs)
  have hx := pairDim (u i) (u j) i.property.1 j.property.1 di
  have hy := pairDim (v i) (v j) i.property.2 j.property.2 dj
  rcases hi with high|high
  · obtain ⟨k,hk⟩ := third i j high hx
    exact ⟨i,j,k,Or.inl ⟨hk,jointSurj _ hy⟩⟩
  · obtain ⟨k,hk⟩ := third i j high hy
    exact ⟨i,j,k,Or.inr ⟨hk,jointSurj _ hx⟩⟩

end Geometry1040

namespace Geometry1040Count

abbrev F := ZMod 2

private theorem pull_count {A T : Type*} [AddCommGroup A] [AddCommGroup T]
    [Module F A] [Module F T] [Finite A] [Finite T] (f : A →ₗ[F] T)
    (hs : Function.Surjective f) (P : T → Prop) :
    Nat.card {a : A // P (f a)} * Nat.card T = Nat.card A * Nat.card {t : T // P t} := by
  classical
  choose s h using hs
  let pack (p : T → Prop) : {a : A // p (f a)} ≃ {t : T // p t} × f.ker :=
    {toFun := fun a => (⟨f a.val,a.property⟩, ⟨a.val-s (f a.val),by simp [LinearMap.mem_ker,h]⟩)
     invFun := fun z => ⟨z.2.val + s z.1.val, by
       have hz : f z.2.val = 0 := z.2.property
       simpa [hz,h] using z.1.property⟩
     left_inv := by intro a; apply Subtype.ext; simp
     right_inv := by
       rintro ⟨t,k⟩
       have hz : f k.val = 0 := k.property
       apply Prod.ext <;> apply Subtype.ext <;> simp [hz,h]}
  have hp := Nat.card_congr (pack P)
  rw [Nat.card_prod] at hp
  have ht := Nat.card_congr (pack (fun _ => True))
  simp only [Nat.card_prod,Nat.card_subtype_true] at ht
  rw [hp,ht]
  ac_rfl

private theorem disjoint_count {X : Type*} [Finite X] (H D G : X → Prop)
    (hg : ∀ x, H x → G x) (dg : ∀ x, D x → G x)
    (hd : ∀ x, H x → D x → False) :
    Nat.card {x // H x} + Nat.card {x // D x} ≤ Nat.card {x // G x} := by
  let put : {x // H x} ⊕ {x // D x} → {x // G x} :=
    Sum.elim (fun x => ⟨x.val,hg x x.property⟩) (fun x => ⟨x.val,dg x x.property⟩)
  rw [← Nat.card_sum]
  apply Nat.card_le_card_of_injective put
  rintro (x|x) (y|y) e
  · have hxy : x.val = y.val := congrArg (fun z : {z // G z} => z.val) e
    exact congrArg Sum.inl (Subtype.ext hxy)
  · have hxy : x.val = y.val := congrArg (fun z : {z // G z} => z.val) e
    exact (hd x x.property (hxy ▸ y.property)).elim
  · have hxy : x.val = y.val := congrArg (fun z : {z // G z} => z.val) e
    exact (hd y y.property (hxy ▸ x.property)).elim
  · have hxy : x.val = y.val := congrArg (fun z : {z // G z} => z.val) e
    exact congrArg Sum.inr (Subtype.ext hxy)

private def G (p : (Fin 3 → F) × (Fin 2 → F)) : Prop :=
  p.1 0 * p.2 0 = 0 ∧ p.1 1 * p.2 1 = 0

private def D (p : (Fin 3 → F) × F) : Prop :=
  p.1 0 = 0 ∧ p.1 1 = 0 ∧ p.1 2 = 1 ∧ p.2 = 1

private theorem good_card : Nat.card {p // G p} = 18 := by
  unfold G
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem bad_card : Nat.card {p // D p} = 1 := by
  unfold D
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem three_checks {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module F A] [Module F B]
    [Finite A] [Finite B] (u : A →ₗ[F] (Fin 3 → F)) (v : B →ₗ[F] (Fin 2 → F))
    (f : B →ₗ[F] F) (hu : Function.Surjective u) (hv : Function.Surjective v)
    (hf : f ≠ 0) (H : A → B → Prop)
    (controls : ∀ a b, H a b →
      u a 0 * v b 0 = 0 ∧ u a 1 * v b 1 = 0 ∧ u a 2 * f b = 0) :
    2 * Nat.card {p : A × B // H p.1 p.2} ≤ Nat.card A * Nat.card B := by
  classical
  have hf' : Function.Surjective f := by
    have hn : ∃ b, f b ≠ 0 := by
      by_contra! hall
      apply hf
      ext b
      exact hall b
    obtain ⟨b,hb⟩ := hn
    have casesF : ∀ x : F, x = 0 ∨ x = 1 := by decide
    intro x
    rcases casesF x with rfl|rfl
    · exact ⟨0,map_zero f⟩
    · exact ⟨b,(casesF _).resolve_left hb⟩
  have gc := pull_count (u.prodMap v) (Prod.map_surjective.mpr ⟨hu,hv⟩) G
  have dc := pull_count (u.prodMap f) (Prod.map_surjective.mpr ⟨hu,hf'⟩) D
  have t32 : Nat.card ((Fin 3 → F) × (Fin 2 → F)) = 32 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have t16 : Nat.card ((Fin 3 → F) × F) = 16 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  rw [t32,good_card,Nat.card_prod] at gc
  rw [t16,bad_card,Nat.card_prod] at dc
  have cap := disjoint_count (fun p : A × B => H p.1 p.2) (fun p => D ((u.prodMap f) p))
      (fun p => G ((u.prodMap v) p)) (fun p hp => ⟨(controls _ _ hp).1,(controls _ _ hp).2.1⟩)
      (by rintro ⟨a,b⟩ ⟨h0,h1,_,_⟩; change u a 0 * v b 0 = 0 ∧ u a 1 * v b 1 = 0; simp_all)
      (by rintro ⟨a,b⟩ hh ⟨_,_,h2,hf1⟩; have he := (controls a b hh).2.2
          change u a 2 = 1 at h2
          change f b = 1 at hf1
          simp [h2,hf1] at he)
  omega

end Geometry1040Count

namespace Geometry1040

theorem half_of_good_slots {t : ℕ} (ht : 0 < t) (P Q : Submodule F (W (3*t)))
    (slots :
      let u := fun s : Live ht P Q => leftEval ht P s.val
      let v := fun s : Live ht P Q => rightEval Q s.val
      ∃ i j k : Live ht P Q,
        (Function.Surjective (LinearMap.pi ![u i,u j,u k]) ∧
          Function.Surjective (LinearMap.pi ![v i,v j])) ∨
        (Function.Surjective (LinearMap.pi ![v i,v j,v k]) ∧
          Function.Surjective (LinearMap.pi ![u i,u j]))) :
    2 * Nat.card {w : P × Q // ∀ i : Fin (3*t),
      w.1.val i * w.2.val i = 0 ∧ w.1.val (nx ht i) * w.2.val i = 0} ≤
      Nat.card P * Nat.card Q := by
  let H (a : P) (b : Q) :=
    ∀ i : Fin (3*t), a.val i * b.val i = 0 ∧ a.val (nx ht i) * b.val i = 0
  let u := fun s : Live ht P Q => leftEval ht P s.val
  let v := fun s : Live ht P Q => rightEval Q s.val
  have test (s : Live ht P Q) (a : P) (b : Q) (h : H a b) : u s a * v s b = 0 := by
    rcases s with ⟨⟨b',i⟩,hs⟩
    cases b' with
    | false => exact (h i).1
    | true => exact (h i).2
  obtain ⟨i,j,k,hf|hr⟩ := slots
  · apply Geometry1040Count.three_checks (LinearMap.pi ![u i,u j,u k])
      (LinearMap.pi ![v i,v j]) (v k) hf.1 hf.2 k.property.2 H
    exact fun a b h => ⟨test i a b h,test j a b h,test k a b h⟩
  · have rev := Geometry1040Count.three_checks (LinearMap.pi ![v i,v j,v k])
      (LinearMap.pi ![u i,u j]) (u k) hr.1 hr.2 k.property.1 (fun b a => H a b)
      (fun b a h => ⟨(mul_comm _ _).trans (test i a b h),
        (mul_comm _ _).trans (test j a b h),(mul_comm _ _).trans (test k a b h)⟩)
    let swap : {z : P × Q // H z.1 z.2} ≃ {z : Q × P // H z.2 z.1} :=
      ⟨fun z => ⟨z.val.swap,z.property⟩,fun z => ⟨z.val.swap,z.property⟩,fun _ => rfl,fun _ => rfl⟩
    change 2 * Nat.card {z : P × Q // H z.1 z.2} ≤ Nat.card P * Nat.card Q
    rw [Nat.card_congr swap, Nat.mul_comm (Nat.card P)]
    exact rev

end Geometry1040

namespace Geometry1040
theorem mixed_half {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t) (P Q : Submodule F (W (3*t)))
    (hp : P ≤ (synd (3*t)).ker) (hq : Q ≤ (synd (3*t)).ker)
    (large : 3*t-1 ≤ Module.finrank F P + Module.finrank F Q)
    (np : 2 ≤ Module.finrank F P) (nq : 2 ≤ Module.finrank F Q) :
    2 * Nat.card {w : P × Q // ∀ i : Fin (3*t),
      w.1.val i * w.2.val i = 0 ∧ w.1.val (nx ht i) * w.2.val i = 0} ≤
      Nat.card P * Nat.card Q :=
  half_of_good_slots ht P Q (goodSlots ht ht2 P Q hp hq large np nq)
end Geometry1040

namespace Geometry1040

def fullLine {n : ℕ} (P Q : Submodule F (W n)) : Prop :=
  Q = (synd n).ker ∧ ∃ w : W n, w ≠ 0 ∧ ∀ x, x ∈ P ↔ x = 0 ∨ x = w

theorem low_rank_line {n : ℕ} (hn : 2 ≤ n) (P Q : Submodule F (W n))
    (hp : P ≤ (synd n).ker) (hq : Q ≤ (synd n).ker)
    (large : n-1 ≤ Module.finrank F P + Module.finrank F Q)
    (small : ¬2 ≤ Module.finrank F P) : fullLine P Q := by
  have hdim := codeDimension hn
  have qle := Submodule.finrank_mono hq
  have hp1 : Module.finrank F P = 1 := by omega
  have hQ : Q = (synd n).ker := Submodule.eq_of_le_of_finrank_eq hq (by omega)
  have hc : Nat.card P = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := P),Nat.card_zmod,hp1]
    decide
  obtain ⟨w,hw,hwuniq⟩ := (Nat.card_eq_two_iff' (0 : P)).mp hc
  refine ⟨hQ,w.val,fun h => hw (Subtype.ext h),?_⟩
  intro x
  constructor
  · intro hx
    by_cases h : x = 0
    · exact Or.inl h
    · have hnz : (⟨x,hx⟩ : P) ≠ 0 := fun he => h (congrArg Subtype.val he)
      exact Or.inr (congrArg Subtype.val (hwuniq ⟨x,hx⟩ hnz))
  · rintro (rfl|rfl)
    · exact P.zero_mem
    · exact w.property

theorem low_rank_cases {t : ℕ} (ht : 0 < t) (P Q : Submodule F (W (3*t)))
    (hp : P ≤ (synd (3*t)).ker) (hq : Q ≤ (synd (3*t)).ker)
    (large : 3*t-1 ≤ Module.finrank F P + Module.finrank F Q)
    (small : ¬(2 ≤ Module.finrank F P ∧ 2 ≤ Module.finrank F Q)) :
    fullLine P Q ∨ fullLine Q P := by
  by_cases hl : 2 ≤ Module.finrank F P
  · exact Or.inr (low_rank_line (by omega) Q P hq hp (by omega) (fun h => small ⟨hl,h⟩))
  · exact Or.inl (low_rank_line (by omega) P Q hp hq large hl)

end Geometry1040

namespace PNP1040
def parityCol (e : Fin 2) (j : Fin 3) : ZMod 2 :=
  if j.val = e.val ∨ j.val = 2 then 1 else 0
def colour {n : ℕ} (i : Fin n) : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩
theorem column_nonzero : ∀ j : Fin 3, ∃ e : Fin 2, parityCol e j ≠ 0 := by decide +kernel
theorem column_pair : ∀ i j : Fin 3, (∀ e : Fin 2, parityCol e i + parityCol e j = 0) ↔ i = j := by decide +kernel
theorem column_triple : ∀ i j k : Fin 3, (∀ e : Fin 2, parityCol e i + parityCol e j + parityCol e k = 0) ↔
    i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide +kernel
theorem support_checks {n : ℕ} (x : Fin n → ZMod 2) (hc : ∀ e : Fin 2,
    (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0) :
    ∀ e : Fin 2, ∑ i ∈ Finset.univ.filter (fun i => x i ≠ 0), parityCol e (colour i) = 0 := by
  intro e
  apply Eq.trans _ (hc e)
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have binary : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  by_cases h : x i = 0
  · simp [h]
  · by_cases test : i.val % 3 = e.val ∨ i.val % 3 = 2 <;> simp [binary _ h, parityCol, colour, test]

theorem support_pair {α : Type*} [DecidableEq α] (c : α → Fin 3) {x y : α} (h : x ≠ y)
    (hc : ∀ e : Fin 2, ∑ i ∈ ({x,y}:Finset α), parityCol e (c i) = 0) : c x = c y := by
  apply (column_pair _ _).mp
  simpa [h] using hc

theorem support_triple {α : Type*} [DecidableEq α] (c : α → Fin 3) {x y z : α}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hc : ∀ e : Fin 2, ∑ i ∈ ({x,y,z}:Finset α), parityCol e (c i) = 0) :
    c x ≠ c y ∧ c x ≠ c z ∧ c y ≠ c z := by
  apply (column_triple _ _ _).mp
  simpa [hxy,hxz,hyz,add_assoc] using hc
end PNP1040


namespace PNP1040

theorem triple_path {α : Type*} [DecidableEq α] (f : α ≃ α) (S : Finset α)
    (nofix : ∀ x, f x ≠ x) (no2 : ∀ x, f (f x) ≠ x)
    (hs : S.card = 3) (hd : (S ∪ S.map f.toEmbedding).card ≤ 4) :
    ∃ x, S = {x, f x, f (f x)} := by
  classical
  have hcount := Finset.card_union_add_card_inter S (S.map f.toEmbedding)
  rw [Finset.card_map, hs] at hcount
  have hinter : 1 < (S ∩ S.map f.toEmbedding).card := by omega
  obtain ⟨v,hv,z,hz,hvz⟩ := Finset.one_lt_card.mp hinter
  obtain ⟨hvS,hvf⟩ := Finset.mem_inter.mp hv
  obtain ⟨hzS,hzf⟩ := Finset.mem_inter.mp hz
  obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hvf
  obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hzf
  change f u ≠ f w at hvz
  change f u ∈ S at hvS
  change f w ∈ S at hzS
  have huw : u ≠ w := fun h => hvz (congrArg f h)
  have hcross : f u = w ∨ f w = u := by
    by_contra! h
    have hsub : ({u,f u,w,f w}: Finset α) ⊆ S := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hu,hvS,hw,hzS⟩
    have hcard := Finset.card_le_card hsub
    have hfour : ({u,f u,w,f w}: Finset α).card = 4 := by
      simp [huw, hvz, h.1, h.2.symm, (nofix u).symm, (nofix w).symm]
    omega
  have make (a : α) (ha : a ∈ S) (hb : f a ∈ S) (hc : f (f a) ∈ S) :
      S = {a, f a, f (f a)} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨ha,hb,hc⟩
    · simp [hs, (nofix a).symm, (no2 a).symm, (nofix (f a)).symm]
  rcases hcross with rfl | h
  · exact ⟨_,make u hu hvS hzS⟩
  · exact ⟨_,make w hw hzS (h ▸ hvS)⟩

theorem rotate_full {n : ℕ} [NeZero n] (S : Finset (Fin n)) (hs : S.Nonempty)
    (closed : ∀ x ∈ S, finRotate n x ∈ S) : S = Finset.univ := by
  classical
  obtain ⟨x,hx⟩ := hs
  have it : ∀ k : ℕ, (finRotate n)^[k] x ∈ S := by
    intro k
    induction k with
    | zero => exact hx
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact closed _ ih
  apply Finset.eq_univ_of_forall
  intro y
  have h := it (y-x).val
  rw [←finCycle_eq_finRotate_iterate,finCycle_apply] at h
  simpa [add_comm] using h

theorem rotate_growth {n : ℕ} [NeZero n] (S : Finset (Fin n)) (hs : S.Nonempty)
    (proper : S ≠ Finset.univ) :
    S.card < (S ∪ S.map (finRotate n).toEmbedding).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.subset_union_left, ?_⟩
  intro eq
  apply proper
  apply rotate_full S hs
  intro x hx
  rw [eq]
  apply Finset.mem_union_right
  exact Finset.mem_map.mpr ⟨x,hx,rfl⟩

end PNP1040

namespace PNP1040
theorem classify_small {n : ℕ} [NeZero n] (hn : 4 < n)
    (S : Finset (Fin n)) (hS : S.Nonempty) (c : Fin n → Fin 3)
    (hc : ∀ e : Fin 2, ∑ i ∈ S, parityCol e (c i) = 0)
    (no1 : ∀ i, finRotate n i ≠ i) (no2 : ∀ i, finRotate n (finRotate n i) ≠ i)
    (hD : (S ∪ S.map (finRotate n).toEmbedding).card ≤ 4) :
    (∃ j k, j ≠ k ∧ c j = c k ∧ S = {j,k}) ∨
    (∃ j, S = {j, finRotate n j, finRotate n (finRotate n j)}) := by
  have hSc : 0 < S.card := Finset.card_pos.mpr hS
  have proper : S ≠ Finset.univ := by
    intro eq; subst S
    simp at hD; omega
  have growth := rotate_growth S hS proper
  have hc3 : S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases hc3 with one | two | three
  · obtain ⟨j,hj⟩ := Finset.card_eq_one.mp one
    obtain ⟨e,he⟩ := column_nonzero (c j)
    exact False.elim (he (by simpa [hj] using hc e))
  · obtain ⟨j,k,hjk,heq⟩ := Finset.card_eq_two.mp two
    exact Or.inl ⟨j,k,hjk,support_pair c hjk (heq ▸ hc),heq⟩
  · exact Or.inr (triple_path _ S no1 no2 three hD)
end PNP1040
namespace PNP1040
theorem small_of_shape {α : Type*} [DecidableEq α] (f : α ≃ α) (S : Finset α)
    (hs : (∃ j k : α, S = {j,k}) ∨ (∃ j : α, S = {j, f j, f (f j)})) :
    (S ∪ S.map f.toEmbedding).card ≤ 4 := by
  classical
  rcases hs with ⟨j,k,rfl⟩ | ⟨j,rfl⟩
  · have hu := Finset.card_union_le ({j,k} : Finset α) (({j,k}:Finset α).map f.toEmbedding)
    rw [Finset.card_map] at hu
    have hh := Finset.card_insert_le j ({k}:Finset α)
    simp only [Finset.card_singleton] at hh
    omega
  · have hsub : ({j,f j,f (f j)} ∪ ({j,f j,f (f j)}:Finset α).map f.toEmbedding) ⊆
        ({j,f j,f (f j),f (f (f j))}:Finset α) := by
      intro x hx
      simp only [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton] at *
      tauto
    have hu := Finset.card_le_card hsub
    have h1 := Finset.card_insert_le j ({f j,f (f j),f (f (f j))}:Finset α)
    have h2 := Finset.card_insert_le (f j) ({f (f j),f (f (f j))}:Finset α)
    have h3 := Finset.card_insert_le (f (f j)) ({f (f (f j))}:Finset α)
    simp only [Finset.card_singleton] at h3
    omega

theorem rotate_period {n : ℕ} [NeZero n] (hn : 2 < n) (i : Fin n) :
    finRotate n i ≠ i ∧ finRotate n (finRotate n i) ≠ i := by
  have one : (1 : Fin n) ≠ 0 := by
    intro h
    have h' := congrArg Fin.val h
    simp [Fin.val_one, Nat.mod_eq_of_lt (show 1 < n by omega)] at h'
  have two : (2 : Fin n) ≠ 0 := by
    intro h
    have h' := congrArg Fin.val h
    have h'' : 2 % n = 0 := h'
    rw [Nat.mod_eq_of_lt hn] at h''
    omega
  constructor
  · simpa [finRotate_apply] using one
  · intro h
    have hh : (1:Fin n)+1 = 0 := by simpa [finRotate_apply,add_assoc] using h
    have he := congrArg Fin.val hh
    simp [Fin.val_add,Fin.val_one, Nat.mod_eq_of_lt (show 1 < n by omega), Nat.mod_eq_of_lt hn] at he
end PNP1040

namespace PNP1040
theorem checkedFootprintFloor {n : ℕ} [NeZero n] (hn : 4 < n) (S : Finset (Fin n))
    (positive : S.Nonempty) (c : Fin n → Fin 3)
    (hc : ∀ e : Fin 2, ∑ i ∈ S, parityCol e (c i) = 0)
    (color_move : ∀ i, c (finRotate n i) ≠ c i) :
    4 ≤ (S ∪ S.map (finRotate n).toEmbedding).card := by
  classical
  by_contra! bad
  have low : (S ∪ S.map (finRotate n).toEmbedding).card ≤ 4 := by omega
  have h₁ := fun i => (rotate_period (show 2 < n by omega) i).1
  have h₂ := fun i => (rotate_period (show 2 < n by omega) i).2
  obtain hp | ht := classify_small hn S positive c hc h₁ h₂ low
  · obtain ⟨j,k,hjk,hcol,rfl⟩ := hp
    let f := finRotate n
    have ff : f j ≠ f k := f.injective.ne hjk
    have fjj : f j ≠ j := h₁ j
    have fkk : f k ≠ k := h₁ k
    have fjk : f j ≠ k := fun h => color_move j ((congrArg c h).trans hcol.symm)
    have fkj : f k ≠ j := fun h => color_move k ((congrArg c h).trans hcol)
    change ({j,k} ∪ ({j,k}:Finset (Fin n)).map f.toEmbedding).card < 4 at bad
    simp [Finset.map_insert, Finset.map_singleton, Finset.insert_union, Finset.singleton_union,
      hjk,ff, fjj.symm,fjk.symm,fkk.symm,fkj.symm] at bad
    simp [fjj,fjk,ff,hjk,fkk.symm,fkj.symm] at bad
  · obtain ⟨j,hs⟩ := ht
    have adj : finRotate n j ≠ finRotate n (finRotate n j) := (h₁ _).symm
    have sthree : S.card = 3 := by
      exact Finset.card_eq_three.mpr ⟨j,_,_,(h₁ _).symm,(h₂ _).symm,adj,hs⟩
    have proper : S ≠ Finset.univ := by
      intro eq
      simp [eq] at sthree
      omega
    have hg := rotate_growth S positive proper
    omega
end PNP1040

namespace PNP1040
abbrev B := ZMod 2
abbrev W6 := Fin 6 → B
def c6 (x : W6) : Prop := ∀ e : Fin 2,
  (∑ i : Fin 6, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0
instance (x : W6) : Decidable (c6 x) := inferInstanceAs (Decidable (∀ e : Fin 2, _))
def annihilated (x y : W6) : Prop := ∀ i : Fin 6,
  x i * y i = 0 ∧ x (i+1) * y i = 0
instance (x y : W6) : Decidable (annihilated x y) := inferInstanceAs (Decidable (∀ i : Fin 6, _))
def cls6 (w : W6) : Prop := ∃ j k : Fin 6, j ≠ k ∧ j.val % 3 = k.val % 3 ∧ ∀ i, w i ≠ 0 ↔ i = j ∨ i = k
instance (w : W6) : Decidable (cls6 w) := inferInstanceAs (Decidable (∃ j k : Fin 6, _))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem six : ∀ w : W6, c6 w → w ≠ 0 →
    let count := (Finset.univ.filter (fun y : W6 => c6 y ∧ annihilated w y)).card
    count ≤ 2 ∧ (count = 2 ↔ cls6 w) := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem six_rev : ∀ w : W6, c6 w → w ≠ 0 →
    let count := (Finset.univ.filter (fun y : W6 => c6 y ∧ annihilated y w)).card
    count ≤ 2 ∧ (count = 2 ↔ cls6 w) := by decide +kernel

theorem six_size : (Finset.univ.filter c6).card = 16 := by decide +kernel

end PNP1040

namespace Geometry1040
def restr (n : ℕ) (D : Finset (Fin n)) : (synd n).ker →ₗ[F] (D → F) where
  toFun y i := y.val i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def shorten {n : ℕ} (D : Finset (Fin n)) :
    (restr n D).ker ≃ₗ[F] (checkOn Dᶜ).ker where
  toFun y := ⟨fun i => y.val.val i.val, by
    have he : ext0 Dᶜ (fun i => y.val.val i.val) = y.val.val := by
      funext i
      by_cases h : i ∈ D
      · simp [ext0,h]
        have hz := congrFun (show restr n D y.val = 0 from y.property) ⟨i,h⟩
        exact hz.symm
      · simp [ext0,h]
    change synd n (ext0 Dᶜ (fun i => y.val.val i.val)) = 0
    rw [he]
    exact y.val.property⟩
  invFun z := ⟨⟨ext0 Dᶜ z.val,z.property⟩, by
    change (fun i : D => ext0 Dᶜ z.val i.val) = 0
    funext i
    simp [ext0,i.property]⟩
  left_inv y := by
    apply Subtype.ext; apply Subtype.ext; funext i
    change ext0 Dᶜ (fun j => y.val.val j.val) i = y.val.val i
    by_cases h : i ∈ D
    · simp [ext0,h]
      exact (congrFun (show restr n D y.val = 0 from y.property) ⟨i,h⟩).symm
    · simp [ext0,h]
  right_inv z := by
    apply Subtype.ext; funext i
    have h : i.val ∉ D := Finset.mem_compl.mp i.property
    change ext0 Dᶜ z.val i.val = _
    simp [ext0,h]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem footprintRank {n : ℕ} (hn : 2 ≤ n) (D : Finset (Fin n)) :
    Module.finrank F (restr n D).range + 2 =
      D.card + Module.finrank F (checkOn Dᶜ).range := by
  have he := (shorten D).finrank_eq
  have hr := (restr n D).finrank_range_add_finrank_ker
  have hq := (checkOn Dᶜ).finrank_range_add_finrank_ker
  have htotal := codeDimension hn
  have hcompl := Finset.card_compl_add_card D
  simp only [Fintype.card_fin] at hcompl
  simp at hq
  omega

theorem footprintCard {n : ℕ} (D : Finset (Fin n)) :
    Nat.card (synd n).ker = 2 ^ Module.finrank F (restr n D).range *
       Nat.card {y : (synd n).ker // ∀ i ∈ D, y.val i = 0} := by
  have e : (restr n D).ker ≃ {y : (synd n).ker // ∀ i ∈ D, y.val i = 0} :=
    Equiv.subtypeEquivRight fun y => by
      change (fun i : D => y.val i.val) = 0 ↔ _
      constructor
      · intro h i hi; exact congrFun h ⟨i,hi⟩
      · intro h; funext i; exact h i i.property
  rw [← Nat.card_congr e, Module.natCard_eq_pow_finrank (K := F) (V := (synd n).ker),
      Module.natCard_eq_pow_finrank (K := F) (V := (restr n D).ker),
      Nat.card_zmod, ← pow_add, LinearMap.finrank_range_add_finrank_ker]
end Geometry1040

namespace Geometry1040
theorem footprintAtFour {t : ℕ} (ht : 3 ≤ t) (D : Finset (Fin (3*t))) (hd : 4 ≤ D.card) :
    let r := Module.finrank F (restr (3*t) D).range
    4 ≤ r ∧ (r = 4 ↔ D.card = 4) := by
  dsimp only
  have h := footprintRank (n:=3*t) (by omega) D
  have hsize := Finset.card_compl_add_card D
  simp only [Fintype.card_fin] at hsize
  by_cases hm : mono Dᶜ
  · have bound := mono_size _ hm
    by_cases he : Dᶜ.Nonempty
    · obtain ⟨p,hp⟩ := he
      have pos := rankOneLe Dᶜ ⟨p,hp⟩
      omega
    · have hz : Dᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      simp [hz] at hsize
      omega
  · have he : Dᶜ.Nonempty := by
      by_contra hn
      have hz := Finset.not_nonempty_iff_eq_empty.mp hn
      apply hm
      simp [hz,mono]
    have hr := (oneOrTwo _ he).2 hm
    have hu := Submodule.finrank_le (checkOn Dᶜ).range
    simp at hu
    omega
end Geometry1040

namespace Terminal1040
open Geometry1040

def support {n : ℕ} (w : W n) : Finset (Fin n) := Finset.univ.filter fun i => w i ≠ 0

def pos {n : ℕ} (f : Fin n ≃ Fin n) (w : W n) :=
  support w ∪ (support w).map f.toEmbedding

def neg {n : ℕ} (f : Fin n ≃ Fin n) (w : W n) :=
  (pos f w).map f.symm.toEmbedding

theorem pos_hit {n : ℕ} (f : Fin n ≃ Fin n) (w y : W n) :
    (∀ i, y i * w i = 0 ∧ y (f i) * w i = 0) ↔ ∀ i ∈ pos f w, y i = 0 := by
  constructor
  · intro h i hi
    rcases Finset.mem_union.mp hi with hs | hs
    · exact (mul_eq_zero.mp (h i).1).resolve_right (Finset.mem_filter.mp hs).2
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hs
      exact (mul_eq_zero.mp (h j).2).resolve_right (Finset.mem_filter.mp hj).2
  · intro h i
    by_cases hh : w i = 0
    · simp [hh]
    · have hs : i ∈ support w := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hh⟩
      rw [h i (Finset.mem_union_left _ hs), h (f i) (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨i,hs,rfl⟩))]
      simp

theorem neg_hit {n : ℕ} (f : Fin n ≃ Fin n) (w y : W n) :
    (∀ i, w i * y i = 0 ∧ w (f i) * y i = 0) ↔ ∀ i ∈ neg f w, y i = 0 := by
  have mem (i : Fin n) : i ∈ neg f w ↔ w (f i) ≠ 0 ∨ w i ≠ 0 := by
    simp [neg,pos,support,Finset.mem_map_equiv]
  constructor
  · intro h i hi
    rcases (mem i).mp hi with ha|hb
    · exact (mul_eq_zero.mp (h i).2).resolve_left ha
    · exact (mul_eq_zero.mp (h i).1).resolve_left hb
  · intro h i
    by_cases hi : i ∈ neg f w
    · simp [h i hi]
    · have hh := mt (mem i).mpr hi
      push_neg at hh
      simp [hh.1, hh.2]

theorem eqRotate {t : ℕ} (ht : 0<t) [NeZero (3*t)] (i : Fin (3*t)) :
    finRotate (3*t) i = nx ht i := by
  rw [finRotate_apply]
  apply Fin.ext
  change (i.val + 1 % (3*t)) % (3*t) = (i.val+1) % (3*t)
  rw [Nat.mod_eq_of_lt (show 1<3*t by omega)]

theorem eqRotate2 {t : ℕ} (ht : 0<t) [NeZero (3*t)] (i : Fin (3*t)) :
    finRotate (3*t) (finRotate (3*t) i) = idx ht (i.val+2) := by
  rw [eqRotate ht, eqRotate ht]
  apply Fin.ext
  change ((i.val+1)%(3*t)+1)%(3*t) = (i.val+2)%(3*t)
  rw [Nat.mod_add_mod]

def shape {t : ℕ} (ht : 0<t) (w : W (3*t)) :=
  (∃ j k : Fin (3*t), j ≠ k ∧ j.val % 3=k.val % 3 ∧ ∀ i, w i ≠ 0 ↔ i=j ∨ i=k) ∨
  (3≤t ∧ ∃ j : Fin (3*t), ∀ i, w i ≠ 0 ↔ i=j ∨ i=idx ht (j.val+1) ∨ i=idx ht (j.val+2))

end Terminal1040

namespace Terminal1040
open Geometry1040

def isCode {n : ℕ} (w : W n) := ∀ e : Fin 2,
  (∑ i : Fin n, if i.val % 3=e.val ∨ i.val % 3=2 then w i else 0) = 0

theorem codeKer {n : ℕ} (w : W n) : w ∈ (synd n).ker ↔ isCode w := by
  change synd n w = 0 ↔ _
  exact ⟨fun h e => congrFun h e, fun h => funext h⟩

def hitsAt {t : ℕ} (ht : 0<t) (x y : W (3*t)) :=
  ∀ i : Fin (3*t), x i * y i = 0 ∧ x (nx ht i) * y i = 0

def lineDataProp {t : ℕ} (ht : 0<t) (V : Submodule F (W (3*t)))
    (T : W (3*t) → W (3*t) → Prop) (w : W (3*t)) := ∃ r : ℕ,
    Nat.card V = 2^r * Nat.card {y : V // T w y.val} ∧
    (if t=2 then 3 else 4) ≤ r ∧ ((if t=2 then 3 else 4) = r ↔ shape ht w)

theorem sixKernelCard (T : W 6 → Prop) [DecidablePred T] :
    Nat.card {y : (synd 6).ker // T y.val} = (Finset.univ.filter (fun y : W 6 => PNP1040.c6 y ∧ T y)).card := by
  let e : {y : (synd 6).ker // T y.val} ≃ {y : W 6 // PNP1040.c6 y ∧ T y} :=
    ⟨fun y => ⟨y.val.val, (codeKer _).1 y.val.property,y.property⟩,
     fun y => ⟨⟨y.val,(codeKer _).2 y.property.1⟩, y.property.2⟩,fun _ => rfl,fun _ => rfl⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem sixFullCard : Nat.card (synd 6).ker = 16 := by
  let e : (synd 6).ker ≃ {y : W 6 // PNP1040.c6 y} :=
    ⟨fun y => ⟨y.val, (codeKer _).1 y.property⟩,
     fun y => ⟨y.val,(codeKer _).2 y.property⟩,fun _ => rfl,fun _ => rfl⟩
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype]
  exact PNP1040.six_size

theorem six_price (G : Prop) (k : ℕ) (hk : 0 < k) (hmax : k ≤ 2)
    (he : k = 2 ↔ G) : ∃ r : ℕ, 16 = 2^r*k ∧ 3 ≤ r ∧ (3=r ↔ G) := by
  by_cases h : k=2
  · exact ⟨3,by omega,by decide,iff_of_true rfl (he.mp h)⟩
  · have one : k=1 := by omega
    exact ⟨4,by omega,by decide,iff_of_false (by decide) (fun hs => h (he.mpr hs))⟩

theorem price_six (ht : 0<2) (w : W 6) (hw : w≠0) (hc : isCode w) :
    lineDataProp ht (synd 6).ker (hitsAt ht) w ∧
    lineDataProp ht (synd 6).ker (fun x y => hitsAt ht y x) w := by
  classical
  have next (i : Fin 6) : nx ht i = i+1 := by rfl
  have eqv (x y : W 6) : hitsAt ht x y ↔ PNP1040.annihilated x y := by rfl
  have hs : shape ht w ↔ PNP1040.cls6 w := by simp [shape,PNP1040.cls6]
  rw [lineDataProp,lineDataProp,sixFullCard]
  constructor
  · let k := Nat.card {y : (synd 6).ker // PNP1040.annihilated w y.val}
    have h0 : Nonempty {y : (synd 6).ker // PNP1040.annihilated w y.val} :=
      ⟨⟨0,by simp [PNP1040.annihilated]⟩⟩
    have hp : 0<k := Nat.card_pos
    have hh := PNP1040.six w hc hw
    have hx : k = _ := sixKernelCard (PNP1040.annihilated w)
    obtain ⟨r,f,l,er⟩ := six_price _ k hp (hx ▸ hh.1) ((hx ▸ hh.2).trans hs.symm)
    exact ⟨r,f,l,er⟩
  · let k := Nat.card {y : (synd 6).ker // PNP1040.annihilated y.val w}
    have h0 : Nonempty {y : (synd 6).ker // PNP1040.annihilated y.val w} :=
      ⟨⟨0,by simp [PNP1040.annihilated]⟩⟩
    have hp : 0<k := Nat.card_pos
    have hh := PNP1040.six_rev w hc hw
    have hx : k = _ := sixKernelCard (fun x => PNP1040.annihilated x w)
    obtain ⟨r,f,l,er⟩ := six_price _ k hp (hx ▸ hh.1) ((hx ▸ hh.2).trans hs.symm)
    exact ⟨r,f,l,er⟩
end Terminal1040

namespace Terminal1040
open Geometry1040 PNP1040

theorem footprintShape {t : ℕ} (ht : 0<t) (ht3 : 3≤t) [NeZero (3*t)]
    (w : W (3*t)) (hw : w≠0) (hc : isCode w) :
    4 ≤ (pos (finRotate (3*t)) w).card ∧
    ((pos (finRotate (3*t)) w).card = 4 ↔ shape ht w) := by
  let n := 3*t
  let S := support w
  let f := finRotate (3*t)
  have hs : S.Nonempty := by
    by_contra h
    apply hw
    funext i
    by_contra hi
    exact h ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
  have hchk := support_checks w hc
  have move (i : Fin (3*t)) : colour (f i) ≠ colour i := by
    intro h
    apply nx_color ht i
    exact (congrArg Fin.val (by simpa [f,eqRotate ht] using h : colour (nx ht i) = colour i))
  have twice (i : Fin (3*t)) : nx ht (nx ht i) = idx ht (i.val+2) := by
    simpa only [eqRotate ht] using eqRotate2 ht i
  have floor := checkedFootprintFloor (n:=3*t) (by omega) S hs colour hchk move
  refine ⟨floor,?_,?_⟩
  · intro eql
    obtain a|a := classify_small (n:=3*t) (by omega) S hs colour hchk
      (fun i => (rotate_period (n:=3*t) (by omega) i).1)
      (fun i => (rotate_period (n:=3*t) (by omega) i).2) eql.le
    · obtain ⟨j,k,hjk,hh,eq⟩ := a
      refine Or.inl ⟨j,k,hjk,congrArg Fin.val hh,?_⟩
      intro i
      have mem : i∈S ↔ i=j ∨ i=k := by simp [eq]
      simpa [S,support] using mem
    · obtain ⟨j,eq⟩ := a
      refine Or.inr ⟨ht3,j,?_⟩
      intro i
      have mem : i∈S ↔ i=j ∨ i=nx ht j ∨ i=idx ht (j.val+2) := by
        simp only [eq,Finset.mem_insert,Finset.mem_singleton,eqRotate ht,twice]
      simpa [S,support,nx] using mem
  · intro h
    refine le_antisymm ?_ floor
    apply small_of_shape f S
    rcases h with ⟨j,k,_,_,e⟩|⟨_,j,e⟩
    · exact Or.inl ⟨j,k,Finset.ext fun i => by simpa [S,support] using (e i)⟩
    · refine Or.inr ⟨j,Finset.ext ?_⟩
      intro i
      have ee := e i
      change w i ≠ 0 ↔ i=j ∨ i=nx ht j ∨ i=idx ht (j.val+2) at ee
      simpa only [S,support,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
        Finset.mem_singleton,f,eqRotate ht,twice] using ee

theorem price_large {t : ℕ} (ht : 0<t) (ht3 : 3≤t) (w : W (3*t))
    (hw : w≠0) (hc : isCode w) :
    lineDataProp ht (synd _).ker (hitsAt ht) w ∧
    lineDataProp ht (synd _).ker (fun x y => hitsAt ht y x) w := by
  classical
  letI : NeZero (3*t) := ⟨by omega⟩
  let f := finRotate (3*t)
  have ⟨hfloor,shapePos⟩ := footprintShape ht ht3 w hw hc
  have same : (neg f w).card = (pos f w).card := Finset.card_map _
  have ne : t ≠ 2 := by omega
  have pn (y : W (3*t)) : hitsAt ht w y ↔ ∀ i∈neg f w, y i=0 := by
    simpa only [hitsAt,f,eqRotate ht] using neg_hit f w y
  have pp (y : W (3*t)) : hitsAt ht y w ↔ ∀ i∈pos f w, y i=0 := by
    simpa only [hitsAt,f,eqRotate ht] using pos_hit f w y
  have prep (D : Finset (Fin (3*t))) (hcD : D.card = (pos f w).card)
      (T : W (3*t) → W (3*t) → Prop) (conn : ∀ y, T w y ↔ ∀ i∈D, y i=0) :
      lineDataProp ht (synd _).ker T w := by
    have hfour := footprintAtFour ht3 D (hcD ▸ hfloor)
    refine ⟨_,?_,by simpa [ne] using hfour.1,?_⟩
    · have h := footprintCard D
      have sameSet : (fun y : (synd (3*t)).ker => ∀ i∈D, y.val i=0) =
          (fun y : (synd (3*t)).ker => T w y.val) := by
        funext y; exact propext (conn y).symm
      simpa only [sameSet] using h
    · simp only [if_neg ne]
      exact eq_comm.trans (hfour.2.trans ((congrArg (· = 4) hcD).to_iff.trans shapePos))
  exact ⟨prep _ same _ pn,prep _ rfl _ pp⟩

end Terminal1040

private theorem line_card {A : Type*} (a b : A) (hab : a ≠ b)
    (cover : ∀ x, x = a ∨ x = b) : Nat.card A = 2 := by
  apply Nat.card_eq_two_iff.mpr
  refine ⟨a,b,hab,?_⟩
  ext x
  simp [cover x]

private theorem line_hit_card {A B : Type*} [Finite A] [Finite B] (a b : A)
    (hab : a ≠ b) (cover : ∀ x, x = a ∨ x = b)
    (R : A → B → Prop) (base : ∀ y, R a y) :
    Nat.card {w : A × B // R w.1 w.2} =
      Nat.card B + Nat.card {y : B // R b y} := by
  let put : B ⊕ {y : B // R b y} → {w : A × B // R w.1 w.2} :=
    Sum.elim (fun y => ⟨(a,y),base y⟩) (fun y => ⟨(b,y.val),y.property⟩)
  have inj : Function.Injective put := by
    rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (congrArg (fun p => p.val.2) h)
    · exact (hab (congrArg (fun p => p.val.1) h)).elim
    · exact (hab (congrArg (fun p => p.val.1) h).symm).elim
    · exact congrArg Sum.inr (Subtype.ext (congrArg (fun p => p.val.2) h))
  have surj : Function.Surjective put := by
    rintro ⟨⟨x,y⟩,h⟩
    rcases cover x with rfl | rfl
    · exact ⟨Sum.inl y,rfl⟩
    · exact ⟨Sum.inr ⟨y,h⟩,rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective put ⟨inj,surj⟩)).symm.trans Nat.card_sum

private theorem line_hits_above_half {A B : Type*} [Finite A] [Finite B]
    (a b : A) (hab : a ≠ b) (cover : ∀ x, x = a ∨ x = b)
    (R : A → B → Prop) (base : ∀ y, R a y) (extra : ∃ y, R b y) :
    Nat.card A * Nat.card B < 2 * Nat.card {w : A × B // R w.1 w.2} := by
  have : Nonempty {y : B // R b y} := by
    obtain ⟨y,h⟩ := extra
    exact ⟨⟨y,h⟩⟩
  rw [line_hit_card a b hab cover R base, line_card a b hab cover]
  have := Nat.card_pos (α := {y : B // R b y})
  omega
private theorem line_subtype_half {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [Finite W] (P Q : Submodule K W) (w : W) (hw : w ≠ 0)
    (span : ∀ x, x ∈ P ↔ x = 0 ∨ x = w)
    (R : W → W → Prop) (base : ∀ y, R 0 y) (extra : R w 0) :
    Nat.card P * Nat.card Q < 2 * Nat.card {z : P × Q // R z.1.val z.2.val} := by
  have mem : w ∈ P := (span w).2 (Or.inr rfl)
  have hab : (0 : P) ≠ (⟨w,mem⟩ : P) := fun h => hw (congrArg Subtype.val h).symm
  have cover (x : P) : x = 0 ∨ x = (⟨w,mem⟩ : P) := by
    rcases (span x).1 x.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  exact line_hits_above_half (0 : P) ⟨w,mem⟩ hab cover (fun x y => R x.val (y : Q).val)
    (fun y => base y) ⟨0, extra⟩

private theorem hit_swap {A B : Type*} (R : A → B → Prop) :
    Nat.card {z : A × B // R z.1 z.2} = Nat.card {z : B × A // R z.2 z.1} := by
  apply Nat.card_congr
  exact ⟨fun z => ⟨z.val.swap,z.property⟩,fun z => ⟨z.val.swap,z.property⟩,fun _ => rfl,fun _ => rfl⟩



private theorem kernel_price {V U : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] [AddCommGroup U] [Module (ZMod 2) U]
    (f : V →ₗ[ZMod 2] U) :
    Nat.card V = 2 ^ Module.finrank (ZMod 2) (LinearMap.range f) *
      Nat.card (LinearMap.ker f) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker f),
    Nat.card_zmod, ← pow_add, f.finrank_range_add_finrank_ker]

private theorem ratio_at_rank (k r s h size : ℕ) (hs : 0 < s)
    (cardinality : h = (2^r + 1)*s) (total : size = (2*2^r)*s) :
    (2*2^k*h ≤ (2^k+1)*size ↔ k ≤ r) ∧
    (2*2^k*h = (2^k+1)*size ↔ k = r) := by
  subst h size
  constructor
  · rw [←Nat.mul_assoc _ _ s, ←Nat.mul_assoc _ _ s, Nat.mul_le_mul_right_iff hs]
    calc
      _ ↔ (2 : ℕ)^k ≤ 2^r := by constructor <;> intro h <;> nlinarith
      _ ↔ _ := Nat.pow_le_pow_iff_right (by decide : 1 < 2)
  · rw [←Nat.mul_assoc _ _ s, ←Nat.mul_assoc _ _ s, Nat.mul_right_cancel_iff hs]
    constructor
    · intro h
      apply Nat.pow_right_injective (by decide : 2 ≤ 2)
      nlinarith
    · rintro rfl
      ring
private theorem price_threshold (t r h size s : ℕ) (hs : 0 < s)
    (cardinality : h = (2^r+1)*s) (total : size = (2*2^r)*s) :
    ((if t=2 then 16 else 32)*h ≤ (if t=2 then 9 else 17)*size ↔ (if t=2 then 3 else 4) ≤ r) ∧
    ((if t=2 then 16 else 32)*h = (if t=2 then 9 else 17)*size ↔ (if t=2 then 3 else 4) = r) := by
  by_cases ht : t=2
  · simpa [ht] using ratio_at_rank 3 r s h size hs cardinality total
  · simpa [ht] using ratio_at_rank 4 r s h size hs cardinality total

private theorem price_terminal {t size hits : ℕ} {line shaped : Prop}
    (hs : 0 < size) (sub : shaped → line) (wins : line → size < 2*hits)
    (rest : ¬line → 2*hits ≤ size)
    (pricing : line →
      (if t=2 then 16 else 32)*hits ≤ (if t=2 then 9 else 17)*size ∧
      ((if t=2 then 16 else 32)*hits = (if t=2 then 9 else 17)*size ↔ shaped)) :
    (if t=2 then 16 else 32)*hits ≤ (if t=2 then 9 else 17)*size ∧
    (size < 2*hits ↔ line) ∧
    ((if t=2 then 16 else 32)*hits = (if t=2 then 9 else 17)*size ↔ shaped) := by
  by_cases hline : line
  · exact ⟨(pricing hline).1,iff_of_true (wins hline) hline,(pricing hline).2⟩
  · have hr := rest hline
    have hlt : (if t=2 then 16 else 32)*hits < (if t=2 then 9 else 17)*size := by
      by_cases ht : t=2 <;> simp [ht] <;> omega
    exact ⟨hlt.le, iff_of_false (by omega) hline, iff_of_false hlt.ne (hline ∘ sub)⟩
private theorem subtype_line_hit_card {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [Finite W] (P Q : Submodule K W) (w : W) (hw : w ≠ 0)
    (span : ∀ x, x ∈ P ↔ x = 0 ∨ x = w)
    (R : W → W → Prop) (base : ∀ y, R 0 y) :
    Nat.card P = 2 ∧
    Nat.card {z : P × Q // R z.1.val z.2.val} =
        Nat.card Q + Nat.card {y : Q // R w y.val} := by
  have mem : w ∈ P := (span w).2 (Or.inr rfl)
  have hab : (0 : P) ≠ (⟨w,mem⟩ : P) := fun h => hw (congrArg Subtype.val h).symm
  have cover (x : P) : x = 0 ∨ x = (⟨w,mem⟩ : P) := by
    rcases (span x).1 x.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  exact ⟨line_card _ _ hab cover, line_hit_card _ _ hab cover (fun x y => R x.val (y : Q).val)
    (fun y => base y)⟩

private theorem price_left {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [Finite W] (P Q : Submodule K W) (w : W) (hw : w ≠ 0)
    (span : ∀ x, x ∈ P ↔ x = 0 ∨ x = w)
    (R : W → W → Prop) (base : ∀ y, R 0 y) (extra : R w 0)
    (t r : ℕ) (shape : W → Prop)
    (factor : Nat.card Q = 2^r * Nat.card {y : Q // R w y.val})
    (floor : (if t=2 then 3 else 4) ≤ r)
    (extremal : (if t=2 then 3 else 4) = r ↔ shape w) :
    let size := Nat.card P * Nat.card Q
    let hits := Nat.card {z : P × Q // R z.1.val z.2.val}
    (if t=2 then 16 else 32)*hits ≤ (if t=2 then 9 else 17)*size ∧
    ((if t=2 then 16 else 32)*hits = (if t=2 then 9 else 17)*size ↔ shape w) := by
  classical
  let s := Nat.card {y : Q // R w y.val}
  have : Nonempty {y : Q // R w y.val} := ⟨⟨0,extra⟩⟩
  have hs : 0 < s := Nat.card_pos
  obtain ⟨p,h⟩ := subtype_line_hit_card P Q w hw span R base
  dsimp only
  have hcard : Nat.card {z : P × Q // R z.1.val z.2.val} = (2^r+1)*s := by
    rw [h,factor]
    dsimp [s]
    ring
  have sizecard : Nat.card P * Nat.card Q = (2*2^r)*s := by
    rw [p,factor]
    exact (Nat.mul_assoc _ _ _).symm
  obtain ⟨le,eq⟩ := price_threshold t r _ _ s hs hcard sizecard
  exact ⟨le.mpr floor,eq.trans extremal⟩

end PEqualNP.Outside.L_lib_1040_aux

open PEqualNP.Outside.L_lib_1040_aux in
theorem PEqualNP.Outside.L_lib_1040 : (∀ (t : ℕ) (ht : 0 < t), 2 ≤ t →
  let F := ZMod 2
  let n := 3*t
  let W := Fin n → F
  let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 2) ht)⟩ : Fin n)
  let code := fun (x : W) => ∀ e : Fin 2,
    (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0
  let shape := fun (w : W) =>
    (∃ j k : Fin n, j ≠ k ∧ j.val % 3 = k.val % 3 ∧ ∀ i, w i ≠ 0 ↔ i = j ∨ i = k) ∨
    (3 ≤ t ∧ ∃ j : Fin n, ∀ i, w i ≠ 0 ↔ i = j ∨ i = ix (j.val+1) ∨ i = ix (j.val+2))
  let form := fun (U V : Submodule F W) (test : W → Prop) =>
    (∀ y, y ∈ V ↔ code y) ∧ ∃ w : W, w ≠ 0 ∧ test w ∧ ∀ x, x ∈ U ↔ x = 0 ∨ x = w
  ∀ P Q : Submodule F W, (∀ x ∈ P, code x) → (∀ y ∈ Q, code y) →
    n-1 ≤ Module.finrank F P + Module.finrank F Q →
    let size := Nat.card P * Nat.card Q
    let hits := Nat.card {w : P × Q // ∀ i : Fin n,
      w.1.val i * w.2.val i = 0 ∧ w.1.val (ix (i.val+1)) * w.2.val i = 0}
    let num := if t = 2 then 9 else 17
    let den := if t = 2 then 16 else 32
    den*hits ≤ num*size ∧
      (size < 2*hits ↔ form P Q (fun _ => True) ∨ form Q P (fun _ => True)) ∧
      (den*hits = num*size ↔ form P Q shape ∨ form Q P shape)) := by
  intro t ht ht2 F n W ix code shape form P Q hP hQ hdim size hits num den
  classical
  let R (x y : W) := ∀ i : Fin n, x i * y i = 0 ∧ x (ix (i.val+1)) * y i = 0
  have leftZero (y : W) : R 0 y := by simp [R, W]
  have rightZero (x : W) : R x 0 := by simp [R, W]
  have half_rev : form P Q (fun _ => True) ∨ form Q P (fun _ => True) → size < 2*hits := by
    rintro (⟨_,w,hw,_,span⟩ | ⟨_,w,hw,_,span⟩)
    · exact line_subtype_half P Q w hw span R leftZero (rightZero w)
    · have h := line_subtype_half Q P w hw span (fun y x => R x y) rightZero (leftZero w)
      change Nat.card P * Nat.card Q < 2 * Nat.card {z : P × Q // R z.1.val z.2.val}
      rw [Nat.mul_comm (Nat.card P), hit_swap (fun (x : P) (y : Q) => R x.val y.val)]
      exact h
  let R' (y x : W) := R x y
  let data (V : Submodule F W) (T : W → W → Prop) (w : W) := ∃ r : ℕ,
    Nat.card V = 2^r * Nat.card {y : V // T w y.val} ∧
    (if t=2 then 3 else 4) ≤ r ∧ ((if t=2 then 3 else 4) = r ↔ shape w)
  have lineData (V : Submodule F W) (full : ∀ y, y ∈ V ↔ code y) (w : W)
      (hw : w ≠ 0) (hc : code w) : data V R w ∧ data V R' w := by
    have e : V = (Geometry1040.synd n).ker := by
      ext y
      exact (full y).trans (Terminal1040.codeKer y).symm
    subst V
    by_cases e : t=2
    · subst t
      exact Terminal1040.price_six ht w hw hc
    · exact Terminal1040.price_large ht (by omega) w hw hc
  have half_non : ¬(form P Q (fun _ => True) ∨ form Q P (fun _ => True)) → 2*hits ≤ size := by
    intro hn
    have hp : P ≤ (Geometry1040.synd n).ker := fun x hx => (Terminal1040.codeKer x).2 (hP x hx)
    have hq : Q ≤ (Geometry1040.synd n).ker := fun x hx => (Terminal1040.codeKer x).2 (hQ x hx)
    have both : 2 ≤ Module.finrank F P ∧ 2 ≤ Module.finrank F Q := by
      by_contra low
      apply hn
      have lift {U V : Submodule F W} (h : Geometry1040.fullLine U V) : form U V (fun _ => True) := by
        obtain ⟨rfl,w,hw,s⟩ := h
        exact ⟨fun y => Terminal1040.codeKer y,w,hw,trivial,s⟩
      exact (Geometry1040.low_rank_cases ht P Q hp hq hdim low).imp lift lift
    exact Geometry1040.mixed_half ht ht2 P Q hp hq hdim both.1 both.2
  have lp {w : W} (full : ∀ y, y ∈ Q ↔ code y) (hw : w ≠ 0)
      (span : ∀ x, x ∈ P ↔ x=0 ∨ x=w) :
      den*hits ≤ num*size ∧ (den*hits = num*size ↔ shape w) := by
    obtain ⟨r,factor,floor,extremal⟩ := (lineData Q full w hw (hP w ((span w).2 (Or.inr rfl)))).1
    exact price_left P Q w hw span R leftZero (rightZero w) t r shape factor floor extremal
  have rp {w : W} (full : ∀ y, y ∈ P ↔ code y) (hw : w ≠ 0)
      (span : ∀ x, x ∈ Q ↔ x=0 ∨ x=w) :
      den*hits ≤ num*size ∧ (den*hits = num*size ↔ shape w) := by
    obtain ⟨r,factor,floor,extremal⟩ := (lineData P full w hw (hQ w ((span w).2 (Or.inr rfl)))).2
    have he : hits = Nat.card {z : Q × P // R' z.1.val z.2.val} :=
      hit_swap (fun (x : P) (y : Q) => R x.val y.val)
    change den*hits ≤ num*(Nat.card P * Nat.card Q) ∧
      (den*hits = num*(Nat.card P * Nat.card Q) ↔ shape w)
    rw [Nat.mul_comm (Nat.card P) (Nat.card Q), he]
    exact price_left Q P w hw span R' rightZero (leftZero w) t r shape factor floor extremal
  have sub : form P Q shape ∨ form Q P shape → form P Q (fun _ => True) ∨ form Q P (fun _ => True) := by
    rintro (⟨h,w,hw,_,s⟩ | ⟨h,w,hw,_,s⟩)
    · exact Or.inl ⟨h,w,hw,trivial,s⟩
    · exact Or.inr ⟨h,w,hw,trivial,s⟩
  apply price_terminal (t := t) (size := size) (hits := hits) (Nat.mul_pos Nat.card_pos Nat.card_pos) sub half_rev half_non
  intro line
  have eq_of_shape : form P Q shape ∨ form Q P shape → den*hits = num*size := by
    rintro (⟨h,w,hw,hs,s⟩ | ⟨h,w,hw,hs,s⟩)
    · exact (lp h hw s).2.mpr hs
    · exact (rp h hw s).2.mpr hs
  rcases line with ⟨h,w,hw,_,s⟩ | ⟨h,w,hw,_,s⟩
  · obtain ⟨bound,eq⟩ := lp h hw s
    exact ⟨bound, fun he => Or.inl ⟨h,w,hw,eq.mp he,s⟩, eq_of_shape⟩
  · obtain ⟨bound,eq⟩ := rp h hw s
    exact ⟨bound, fun he => Or.inr ⟨h,w,hw,eq.mp he,s⟩, eq_of_shape⟩
