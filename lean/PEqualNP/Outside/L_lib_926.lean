import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_926_aux

namespace SupportGeometry

abbrev F := ZMod 2
abbrev Space (n : Nat) := Fin n → F
def next {n : Nat} (i : Fin n) : Fin n := ⟨(i.val+1)%n,Nat.mod_lt _ ((Nat.zero_le i.val).trans_lt i.isLt)⟩

noncomputable def support {n : Nat} (U : Submodule F (Space n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ x ∈ U, x i ≠ 0)

lemma mem_support {n : Nat} (U : Submodule F (Space n)) (i : Fin n) :
    i ∈ support U ↔ ∃ x ∈ U, x i ≠ 0 := by classical simp [support]

def adjacent {n : Nat} (U : Submodule F (Space n)) :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i

lemma one_of_ne {x : F} (h : x ≠ 0) : x = 1 := by
  have all : ∀ a : F, a ≠ 0 → a = 1 := by decide
  exact all x h

lemma constant_on_pair {n : Nat} {U : Submodule F (Space n)} (h : adjacent U) {i : Fin n}
    (hi : i ∈ support U) (hj : next i ∈ support U) {x : Space n} (hx : x ∈ U) :
    x i = x (next i) := by
  obtain ⟨a,ha,hai⟩ := (mem_support U i).mp hi
  obtain ⟨b,hb,hbj⟩ := (mem_support U (next i)).mp hj
  have ai := one_of_ne hai
  have e := h a ha b hb i
  rw [ai,one_of_ne hbj,one_mul] at e
  have aj : a (next i) ≠ 0 := by
    intro z
    rw [z,zero_mul] at e
    exact one_ne_zero e
  have q := h a ha x hx i
  rw [ai,one_of_ne aj,one_mul,one_mul] at q
  exact q.symm

lemma all_if_forward {n : Nat} (P : Fin n → Prop) (i : Fin n) (hi : P i)
    (forward : ∀ j, P j → P (next j)) : ∀ j, P j := by
  have hn : 0 < n := (Nat.zero_le i.val).trans_lt i.isLt
  have walk : ∀ k : Nat, P ⟨(i.val+k)%n,Nat.mod_lt _ hn⟩ := by
    intro k
    induction k with
    | zero => simpa [Nat.mod_eq_of_lt i.isLt] using hi
    | succ k ih =>
      have eq : next (⟨(i.val+k)%n,Nat.mod_lt _ hn⟩ : Fin n) =
          ⟨(i.val+(k+1))%n,Nat.mod_lt _ hn⟩ := by
        apply Fin.ext
        change ((i.val+k)%n+1)%n = (i.val+(k+1))%n
        rw [Nat.mod_add_mod,Nat.add_assoc]
      exact eq ▸ forward _ ih
  intro j
  have eq : (⟨(i.val+(n-i.val+j.val))%n,Nat.mod_lt _ hn⟩ : Fin n) = j := by
    apply Fin.ext
    change (i.val+(n-i.val+j.val))%n = j.val
    rw [show i.val+(n-i.val+j.val) = n+j.val by omega,Nat.add_mod_left,Nat.mod_eq_of_lt j.isLt]
  exact eq ▸ walk (n-i.val+j.val)

noncomputable def ends {n : Nat} (U : Submodule F (Space n)) :=
  (support U).filter fun i => next i ∉ support U

lemma finrank_le_runs {n : Nat} (U : Submodule F (Space n))
    (h : adjacent U) (proper : support U ≠ Finset.univ) : Module.finrank F U ≤ (ends U).card := by
  classical
  let ev : U →ₗ[F] (↥(ends U) → F) :=
    { toFun := fun x j => (x : Space n) j.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have inj : Function.Injective ev := by
    apply (injective_iff_map_eq_zero ev).mpr
    intro x vanish
    apply Subtype.ext
    funext i
    change (x : Space n) i = 0
    by_contra v
    have onward (j : Fin n) (hj : (x : Space n) j ≠ 0) : (x : Space n) (next j) ≠ 0 := by
      have jmem := (mem_support U j).mpr ⟨x,x.property,hj⟩
      by_cases jm : next j ∈ support U
      · rwa [←constant_on_pair h jmem jm x.property]
      · have member : j ∈ ends U := Finset.mem_filter.mpr ⟨jmem,jm⟩
        have zero := congrFun vanish (⟨j,member⟩ : ↥(ends U))
        exact False.elim (hj zero)
    have all := all_if_forward (fun j => (x : Space n) j ≠ 0) i v onward
    apply proper
    exact Finset.eq_univ_of_forall (fun j => (mem_support U j).mpr ⟨x,x.property,all j⟩)
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using
    LinearMap.finrank_le_finrank_of_injective inj

lemma full_finrank_le_one {n : Nat} (hn : 0 < n) (U : Submodule F (Space n))
    (h : adjacent U) (full : support U = Finset.univ) : Module.finrank F U ≤ 1 := by
  classical
  let start : Fin n := ⟨0,hn⟩
  let ev : U →ₗ[F] F :=
    { toFun := fun x => (x : Space n) start
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have inj : Function.Injective ev := by
    apply (injective_iff_map_eq_zero ev).mpr
    intro x vanish
    apply Subtype.ext
    funext j
    have mem (i : Fin n) : i ∈ support U := full ▸ Finset.mem_univ _
    exact all_if_forward (fun i => (x : Space n) i = 0) start vanish
      (fun i hi => (constant_on_pair h (mem i) (mem (next i)) x.property).symm.trans hi) j
  simpa using LinearMap.finrank_le_finrank_of_injective inj

end SupportGeometry


namespace Census

open PEqualNP.Outside.L_lib_926_aux.SupportGeometry

abbrev V (n : ℕ) := Fin n → ZMod 2
abbrev field := ZMod 2
abbrev Rows {n d : ℕ} (x : Fin n → V d) : Fin d → V n := fun k i => x i k
abbrev colspan {n d : ℕ} (x : Fin n → V d) := Submodule.span field (Set.range (Rows x))
def B (d : ℕ) : ℕ := ∏ i ∈ Finset.range d,(2^d-2^i : ℕ)

def Word {n d : ℕ} (S : Finset (Fin n)) (x : Fin n → V d) :=
  (∀ i, x i ≠ 0 ↔ i∈S) ∧ (∀ i∈S, next i∈S → x i=x (next i))

def synd {n m d : ℕ} (H : Fin n → V m) (x : Fin n → V d) (p : Fin d × Fin m) : field :=
  ∑ i,H i p.2*x i p.1

def Good {n m : ℕ} (d : ℕ) (H : Fin n → V m) (U : Submodule field (V n)) :=
  Module.finrank field U=d ∧ (∀ x∈U,∀ b, (∑ i,H i b*x i)=0) ∧ adjacent U

noncomputable def cells {n m : ℕ} (d : ℕ) (H : Fin n → V m) (S : Finset (Fin n)) : ℕ := by
  classical
  letI : Fintype (Submodule field (V n)) := Fintype.ofFinite _
  exact (Finset.univ.filter (fun U : Submodule field (V n) => Good d H U ∧ support U=S)).card

noncomputable def independentWords {n : ℕ} (d : ℕ) (S : Finset (Fin n)) : Finset (Fin n → V d) := by
  classical
  exact Finset.univ.filter (fun x => Word S x ∧ LinearIndependent field (Rows x))

lemma zero_span {n d : ℕ} (x : Fin n → V d) (L : V n →ₗ[field] field) :
    (∀ y ∈ colspan x, L y = 0) ↔ ∀ k, L (Rows x k)=0 := by
  change Submodule.span field (Set.range (Rows x)) ≤ LinearMap.ker L ↔ _
  rw [Submodule.span_le]
  exact ⟨fun h k => h (Set.mem_range_self k),fun h y ⟨k,e⟩ => e ▸ h k⟩

def coord {n : ℕ} (i : Fin n) : V n →ₗ[field] field := LinearMap.proj i

def checkCol {n m : ℕ} (H : Fin n → V m) (b : Fin m) : V n →ₗ[field] field := ∑ i,H i b • coord i
lemma check_apply {n m : ℕ} (H : Fin n → V m) (b : Fin m) (y : V n) : checkCol H b y = ∑ i,H i b*y i := by simp [checkCol,coord]

lemma active_col {n d : ℕ} (x : Fin n → V d) (i : Fin n) : i∈support (colspan x) ↔ x i≠0 := by
  rw [mem_support]
  constructor
  · rintro ⟨y,hy,he⟩ h
    apply he
    exact (zero_span x (coord i)).mpr (fun k => congrFun h k) y hy
  · intro hn; obtain ⟨k,hk⟩ : ∃ k, x i k ≠ 0 := by simpa [funext_iff] using hn
    exact ⟨Rows x k,Submodule.subset_span (Set.mem_range_self k),hk⟩

lemma good_span {n m d : ℕ} (H : Fin n → V m) (x : Fin n → V d) (S : Finset (Fin n))
    (ind : LinearIndependent field (Rows x)) :
    (Good d H (colspan x) ∧ support (colspan x)=S) ↔ Word S x ∧ synd H x=0 := by
  classical
  have hm (k : Fin d) : Rows x k∈colspan x := Submodule.subset_span (Set.mem_range_self _)
  constructor
  · rintro ⟨⟨_,L,Q⟩,Z⟩
    refine ⟨⟨fun i => (active_col x i).symm.trans (by rw [Z]),?_⟩,?_⟩
    · intro i hi hj; funext k
      exact constant_on_pair Q (Z.symm ▸ hi) (Z.symm ▸ hj) (hm k)
    · funext p; exact L _ (hm p.1) p.2
  · rintro ⟨⟨A,E⟩,L⟩
    have act (i : Fin n) := (active_col x i).trans (A i)
    have vanish {i : Fin n} (hi : i ∉ S) {y : V n} (hy : y∈colspan x) : y i=0 := by
      by_contra h; exact hi ((act i).mp ((mem_support _ _).mpr ⟨y,hy,h⟩))
    refine ⟨⟨by simp [colspan,finrank_span_eq_card ind],?_,?_⟩,Finset.ext act⟩
    · intro y hy b
      rw [←check_apply]
      exact (zero_span x (checkCol H b)).mpr (fun k => by rw [check_apply]; exact congrFun L (k,b)) y hy
    · intro y hy z hz i
      by_cases hi : i∈S
      · by_cases hj : next i∈S
        · have e := (zero_span x (coord i-coord (next i))).mpr (fun k => sub_eq_zero.mpr (congrFun (E i hi hj) k))
          have ey : y i=y (next i) := sub_eq_zero.mp (e y hy)
          have ez : z i=z (next i) := sub_eq_zero.mp (e z hz)
          rw [ey,ez]
        · simp [vanish hj hy,vanish hj hz]
      · simp [vanish hi hy,vanish hi hz]

lemma basis_fibre {n d : ℕ} (U : Submodule field (V n)) (hU : Module.finrank field U=d) :
    Nat.card {x : Fin n → V d // LinearIndependent field (Rows x) ∧ colspan x=U} = B d := by
  classical
  let emb (b : {v : Fin d → U // LinearIndependent field v}) (i : Fin n) (k : Fin d) : field := (b.1 k).1 i
  have ind (b : {v : Fin d → U // LinearIndependent field v}) : LinearIndependent field (Rows (emb b)) :=
    b.2.map' U.subtype (LinearMap.ker_eq_bot.mpr U.subtype_injective)
  have eqU (b : {v : Fin d → U // LinearIndependent field v}) : colspan (emb b) = U := by
    apply Submodule.eq_of_le_of_finrank_le
    · apply Submodule.span_le.mpr
      rintro y ⟨k,rfl⟩; exact (b.1 k).2
    · rw [hU,colspan,finrank_span_eq_card (ind b),Fintype.card_fin]
  let lift (b : {v : Fin d → U // LinearIndependent field v}) : {x : Fin n → V d // LinearIndependent field (Rows x) ∧ colspan x=U} := ⟨emb b,ind b,eqU b⟩
  have bij : Function.Bijective lift := by
    constructor
    · intro a b h; apply Subtype.ext; funext k; apply Subtype.ext; funext i; exact congrFun (congrFun (congrArg Subtype.val h) i) k
    · rintro ⟨t,hi,he⟩
      let b (k : Fin d) : U := ⟨Rows t k,he.le (Submodule.subset_span (Set.mem_range_self k))⟩
      have hb : LinearIndependent field b := LinearIndependent.of_comp U.subtype hi
      exact ⟨⟨b,hb⟩,Subtype.ext rfl⟩
  rw [←Nat.card_congr (Equiv.ofBijective lift bij),B,←Fin.prod_univ_eq_prod_range]
  simpa [hU,field,ZMod.card] using (card_linearIndependent (K:=field) (V:=U) (by omega : d ≤ Module.finrank field U))

open Classical in
lemma count_census {n m : ℕ} (d : ℕ) (H : Fin n → V m) (S : Finset (Fin n)) :
    B d*cells d H S = ((independentWords d S).filter (fun x => synd H x=0)).card := by
  classical
  letI : Fintype (Submodule field (V n)) := Fintype.ofFinite _
  let Q := Finset.univ.filter (fun x : Fin n → V d => LinearIndependent field (Rows x))
  let P := Finset.univ.filter (fun U : Submodule field (V n) => Good d H U ∧ support U = S)
  have hf (U : Submodule field (V n)) (hu : U ∈ P) : (Q.filter (fun x => colspan x=U)).card = B d := by
    have Hdim : Module.finrank field U=d := (Finset.mem_filter.mp hu).2.1.1
    rw [←basis_fibre U Hdim,Nat.card_eq_fintype_card]
    symm; exact Fintype.card_of_subtype _ (fun x => by simp [Q])
  have hQ : Q.filter (fun x => colspan x∈P) = (independentWords d S).filter (fun x => synd H x=0) := by
    ext x; simp only [Q,P,independentWords,Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases h : LinearIndependent field (Rows x)
    · simp [h,good_span H x S h]
    · simp [h]
  change B d * P.card = _
  rw [←hQ,←Finset.sum_card_fiberwise_eq_card_filter Q P colspan,Finset.sum_congr rfl hf]
  simp [Nat.mul_comm]

end Census


namespace Harmonic

def spin (b : ZMod 2) : ℤ := if b=0 then 1 else -1
lemma spin_add (a b : ZMod 2) : spin (a+b)=spin a*spin b := by
  fin_cases a <;> fin_cases b <;> decide
lemma spin_sum {I : Type*} (s : Finset I) (f : I → ZMod 2) : spin (∑ i ∈ s, f i) = ∏ i ∈ s, spin (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [spin]
  | insert i s hi ih => simp [hi,spin_add,ih]
lemma dot_orthogonal {I : Type*} [Fintype I] [DecidableEq I] (v : I → ZMod 2) :
    (∑ a : I → ZMod 2, spin (∑ i, a i*v i)) = if v=0 then (2:ℤ)^Fintype.card I else 0 := by
  classical
  simp_rw [spin_sum]
  rw [← Fintype.prod_sum (fun i a => spin (a*v i))]
  have oneCoord (t : ZMod 2) : (∑ a : ZMod 2, spin (a*t)) = if t=0 then (2:ℤ) else 0 := by
    fin_cases t <;> decide
  simp_rw [oneCoord]
  by_cases hv : v=0
  · simp [hv]
  · simp only [hv, ↓reduceIte]
    obtain ⟨i,hi⟩ : ∃ i, v i≠0 := by simpa [funext_iff] using hv
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

open Classical in
lemma character_filter {X K : Type*} [Fintype K] [DecidableEq K] (T : Finset X) (s : X → K → ZMod 2) :
    (2:ℤ)^Fintype.card K*((T.filter (fun x => s x=0)).card : ℤ) =
      ∑ a : K → ZMod 2, ∑ x ∈ T, spin (∑ k, a k*s x k) := by
  classical
  rw [Finset.sum_comm]
  simp_rw [dot_orthogonal]
  simp [Finset.sum_ite,mul_comm]

end Harmonic


namespace Census

open PEqualNP.Outside.L_lib_926_aux.Harmonic

noncomputable def words {n : ℕ} (d : ℕ) (S : Finset (Fin n)) : Finset (Fin n → V d) := by
  classical
  exact Finset.univ.filter (Word S)

def phase {n m d : ℕ} (H : Fin n → V m) (a : Fin d × Fin m → field) (i : Fin n) (k : Fin d) : field := ∑ b,a (k,b)*H i b

lemma rephase {n m d : ℕ} (H : Fin n → V m) (a : Fin d × Fin m → field) (x : Fin n → V d) :
    ∑ p,a p*synd H x p = ∑ i,∑ k,x i k*phase H a i k := by
  rw [Fintype.sum_prod_type]
  simp only [synd,phase,Finset.mul_sum]
  calc
    _ = ∑ k,∑ i,∑ b,a (k,b)*(H i b*x i k) := Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
    _ = ∑ i,∑ k,∑ b,a (k,b)*(H i b*x i k) := Finset.sum_comm
    _ = _ := by simp_rw [mul_left_comm (x _ _)]; simp [mul_comm,mul_left_comm,mul_assoc]

noncomputable def bias {n m d : ℕ} (H : Fin n → V m) (a : Fin d × Fin m → field) (S : Finset (Fin n)) : ℤ :=
  ∑ x ∈ words d S,spin (∑ i,∑ k,x i k*phase H a i k)

noncomputable def dep {n m : ℕ} (d : ℕ) (H : Fin n → V m) (S : Finset (Fin n)) : ℕ := by
  classical
  exact (((words d S).filter (fun x => synd H x=0)).filter (fun x => ¬ LinearIndependent field (Rows x))).card

open Classical in
lemma ordered_character_census {n m : ℕ} (d : ℕ) (H : Fin n → V m) (S : Finset (Fin n)) :
    (2:ℤ)^(m*d)*(B d:ℤ)*(cells d H S:ℤ) =
      ∑ a : Fin d × Fin m → field, ∑ x ∈ independentWords d S,spin (∑ i,∑ k,x i k*phase H a i k) := by
  have K := character_filter (independentWords d S) (synd H)
  simp_rw [rephase] at K
  have eq : (B d:ℤ)*(cells d H S:ℤ) = (((independentWords d S).filter (fun x => synd H x=0)).card:ℤ) := by exact_mod_cast count_census d H S
  rw [mul_assoc,eq]
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using K

open Classical in
lemma signed_census {n m : ℕ} (d : ℕ) (H : Fin n → V m) (S : Finset (Fin n)) :
    (2:ℤ)^(m*d)*((B d:ℤ)*(cells d H S:ℤ)+(dep d H S:ℤ)) =
      ((words d S).card : ℤ) + ∑ a ∈ (Finset.univ : Finset (Fin d × Fin m → field)).erase 0,bias H a S := by
  classical
  let T := (words d S).filter (fun x => synd H x=0)
  have ei : T.filter (fun x => LinearIndependent field (Rows x)) = (independentWords d S).filter (fun x => synd H x=0) := by
    ext x; simp [T,words,independentWords]; tauto
  have total : B d*cells d H S+dep d H S=T.card := by
    rw [count_census,←ei]; exact Finset.card_filter_add_card_filter_not ..
  have hc := character_filter (words d S) (synd H)
  simp_rw [rephase] at hc
  change (2:ℤ)^Fintype.card (Fin d × Fin m)*(T.card:ℤ) = ∑ a,bias H a S at hc
  have ht : (B d:ℤ)*(cells d H S:ℤ)+(dep d H S:ℤ) = T.card := by exact_mod_cast total
  rw [ht,show m*d=Fintype.card (Fin d × Fin m) by simp [Nat.mul_comm],hc]
  have hz : bias H (0 : Fin d × Fin m → field) S = ((words d S).card:ℤ) := by simp [bias,phase,spin]
  rw [←hz]; exact (Finset.add_sum_erase _ (fun a => bias H a S) (Finset.mem_univ _)).symm

lemma phase_hits {n m d w : ℕ} (H : Fin n → V m)
    (hw : ∀ a : V m, a ≠ 0 → w ≤ (Finset.univ.filter (fun i : Fin n => (∑ b,a b*H i b) ≠ 0)).card)
    (a : Fin d × Fin m → field) (h : a≠0) :
    w ≤ (Finset.univ.filter (fun i => phase H a i ≠ 0)).card := by
  classical
  obtain ⟨⟨k,b⟩,hne⟩ : ∃ p, a p≠0 := by simpa [funext_iff] using h
  have hr : (fun b => a (k,b)) ≠ 0 := fun h => hne (congrFun h b)
  refine (hw _ hr).trans (Finset.card_le_card ?_)
  intro i hi; simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
  exact fun h => hi (congrFun h k)

end Census


section Part1

variable {I : Type*} (N : I → I) (S : Finset I) (ht : ∀ i, ∃ k : ℕ, N^[k] i ∉ S)

open Classical in
noncomputable def dist (i : I) := Nat.find (ht i)

lemma out_dist (i : I) : N^[dist N S ht i] i ∉ S := by
  classical
  exact Nat.find_spec (ht i)

lemma in_before {i : I} {k : ℕ} (hk : k < dist N S ht i) : N^[k] i ∈ S := by
  classical
  exact not_not.mp (Nat.find_min (ht i) hk)

lemma dist_zero {i : I} (hi : i ∉ S) : dist N S ht i = 0 := by
  classical
  exact Nat.eq_zero_of_le_zero (Nat.find_min' (ht i) (show N^[0] i ∉ S from hi))

lemma dist_step {i : I} (hi : i ∈ S) : dist N S ht i = dist N S ht (N i) + 1 := by
  classical
  have hpos : 0 < dist N S ht i := by
    by_contra! h
    have H := out_dist N S ht i
    rw [Nat.eq_zero_of_le_zero h] at H
    exact H hi
  have h := out_dist N S ht i
  have hnext : N^[dist N S ht i - 1] (N i) ∉ S := by
    rw [← Function.iterate_succ_apply, show (dist N S ht i - 1).succ = dist N S ht i by omega]
    exact h
  have hl : dist N S ht (N i) ≤ dist N S ht i - 1 := Nat.find_min' (ht (N i)) hnext
  have hr : dist N S ht i ≤ dist N S ht (N i) + 1 := Nat.find_min' (ht i) (by
    rw [Function.iterate_succ_apply]; exact out_dist N S ht (N i))
  omega

noncomputable def finish (i : I) := N^[dist N S ht i - 1] i

lemma finish_end {i : I} (hi : i ∈ S) : finish N S ht i ∈ S ∧ N (finish N S ht i) ∉ S := by
  have H := dist_step N S ht hi
  constructor
  · exact in_before N S ht (by omega)
  · change N (N^[dist N S ht i - 1] i) ∉ S
    rw [← Function.iterate_succ_apply' N (dist N S ht i - 1) i, show (dist N S ht i - 1).succ = dist N S ht i by omega]
    exact out_dist N S ht i

lemma finish_last {i : I} (hi : i ∈ S) (hn : N i ∉ S) : finish N S ht i = i := by
  simp [finish,dist_step N S ht hi,dist_zero N S ht hn]

lemma finish_next {i : I} (hi : i ∈ S) (hn : N i ∈ S) : finish N S ht i = finish N S ht (N i) := by
  have h := dist_step N S ht hn
  simp only [finish,dist_step N S ht hi,Nat.add_sub_cancel]
  rw [← Function.iterate_succ_apply, show (dist N S ht (N i) - 1).succ = dist N S ht (N i) by omega]

lemma constant_to_end {C : Type*} (c : I → C)
    (hc : ∀ i ∈ S, N i ∈ S → c i = c (N i)) {i : I} (hi : i ∈ S) : c i = c (finish N S ht i) := by
  have h := dist_step N S ht hi
  suffices H : ∀ k, k < dist N S ht i → c i = c (N^[k] i) from H _ (by omega)
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro hk
    rw [Function.iterate_succ_apply']
    have hk' : k < dist N S ht i := by omega
    exact (ih hk').trans (hc _ (in_before N S ht hk') (Function.iterate_succ_apply' N k i ▸ in_before N S ht hk))

abbrev EndSite := {i : I // i ∈ S ∧ N i ∉ S}

abbrev Words (C : Type*) [Zero C] :=
  {x : I → C // (∀ i, x i ≠ 0 ↔ i ∈ S) ∧ ∀ i ∈ S, N i ∈ S → x i = x (N i)}

noncomputable def colourEquiv (C : Type*) [Zero C] :
    Words N S C ≃ (EndSite N S → {c : C // c ≠ 0}) := by
  classical
  let f (i : I) (hi : i ∈ S) : EndSite N S := ⟨finish N S ht i, finish_end N S ht hi⟩
  let word (y : EndSite N S → {c : C // c ≠ 0}) (i : I) := if hi : i ∈ S then (y (f i hi)).val else 0
  refine {
    toFun := fun x j => ⟨x.val j, (x.2.1 j).mpr j.2.1⟩
    invFun := fun y => ⟨word y, ?_, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro i
    by_cases h : i ∈ S
    · simpa only [word,dite_eq_left h,iff_true_intro h,iff_true] using (y (f i h)).2
    · simp [word,h]
  · intro i hi hn
    have H : f i hi = f (N i) hn := Subtype.ext (finish_next N S ht hi hn)
    simp [word,hi,hn,H]
  · intro x
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · simpa only [word,dite_eq_left hi] using (constant_to_end N S ht x.val x.2.2 hi).symm
    · simp only [word,dite_eq_right hi]
      exact Eq.symm (not_ne_iff.mp (fun h => hi ((x.2.1 i).mp h)))
  · intro y
    funext j
    apply Subtype.ext
    have H : f j.1 j.2.1 = j := Subtype.ext (finish_last N S ht j.2.1 j.2.2)
    simp [word,j.2.1,H]

include ht in
lemma word_count (C : Type*) [Zero C] [Finite C] [Finite I] :
    Nat.card (Words N S C) = (Nat.card {c : C // c ≠ 0}) ^ Nat.card (EndSite N S) := by
  rw [Nat.card_congr (colourEquiv N S ht C), Nat.card_fun]

abbrev F := ZMod 2
abbrev V (d : ℕ) := Fin d → F
def spin (b : F) : ℤ := if b=0 then 1 else -1
lemma spin_add (a b : F) : spin (a+b)=spin a*spin b := by
  fin_cases a <;> fin_cases b <;> decide
lemma spin_sum {I : Type*} (s : Finset I) (f : I → F) : spin (∑ i ∈ s, f i) = ∏ i ∈ s, spin (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [spin]
  | insert i s hi ih => simp [hi, spin_add, ih]
lemma dot_orthogonal {I : Type*} [Fintype I] [DecidableEq I] (v : I → F) :
    (∑ a : I → F, spin (∑ i, a i*v i)) = if v=0 then (2:ℤ)^(Fintype.card I) else 0 := by
  classical
  simp_rw [spin_sum]
  rw [← Fintype.prod_sum (fun i a => spin (a*v i))]
  have oneCoord (t : F) : (∑ a : F, spin (a*t)) = if t=0 then (2:ℤ) else 0 := by
    fin_cases t <;> decide
  simp_rw [oneCoord]
  by_cases hv : v=0
  · simp [hv]
  · simp only [hv, ↓reduceIte]
    obtain ⟨i,hi⟩ : ∃ i, v i≠0 := by simpa [funext_iff] using hv
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
lemma colour_character {d : ℕ} (v : V d) :
    (∑ a : {x : V d // x ≠ 0}, spin (∑ i, (a.1 i)*v i)) = if v=0 then (2:ℤ)^d-1 else -1 := by
  classical
  let f (x : V d) := spin (∑ i, x i*v i)
  have ha := Finset.add_sum_erase (Finset.univ : Finset (V d)) f (Finset.mem_univ 0)
  rw [Finset.sum_subtype _ (p:=fun x : V d => x ≠ 0) (by simp) f] at ha
  have h0 : f 0 = 1 := by simp [f,spin]
  have h := dot_orthogonal v
  rw [h0] at ha
  change 1 + _ = (∑ x : V d, spin (∑ i, x i*v i)) at ha
  rw [h,Fintype.card_fin] at ha
  change (1:ℤ) + (∑ a : {x : V d // x ≠ 0}, spin (∑ i, (a.1 i)*v i)) = (if v=0 then (2:ℤ)^d else 0) at ha
  by_cases hv : v=0 <;> simp only [hv, ↓reduceIte] at ha ⊢ <;> omega

def runLabel {I J : Type*} [Fintype I] [DecidableEq J] {d : ℕ}
    (p : I → J) (a : I → V d) (j : J) : V d := fun k => ∑ i ∈ Finset.univ.filter (fun t => p t=j), a i k

lemma run_character {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J] {d : ℕ}
    (p : I → J) (a : I → V d) :
    (∑ u : J → {x : V d // x ≠ 0}, spin (∑ i, ∑ k, (u (p i)).1 k * a i k)) =
      ∏ j, (if runLabel p a j=0 then (2:ℤ)^d-1 else -1) := by
  classical
  let val (j : J) (c : {x : V d // x ≠ 0}) := spin (∑ k, c.1 k*runLabel p a j k)
  have factor (u : J → {x : V d // x ≠ 0}) : spin (∑ i, ∑ k, (u (p i)).1 k*a i k) = ∏ j, val j (u j) := by
    rw [← Finset.sum_fiberwise Finset.univ p (fun i => ∑ k, (u (p i)).1 k * a i k),spin_sum]
    apply Finset.prod_congr rfl
    intro j _
    unfold val
    congr 1
    simp only [runLabel,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  simp_rw [factor]
  rw [← Fintype.prod_sum val]
  exact Finset.prod_congr rfl (fun j _ => colour_character (runLabel p a j))

noncomputable def owner (i : S) : EndSite N S := ⟨finish N S ht i, finish_end N S ht i.2⟩

open Classical in
lemma word_character [Fintype I] {d : ℕ} (a : I → V d) :
    (∑ x : Words N S (V d), spin (∑ i, ∑ k, x.val i k * a i k)) =
      ∏ j, (if runLabel (owner N S ht) (fun i : S => a i) j = 0 then (2:ℤ)^d-1 else -1) := by
  classical
  let e := colourEquiv N S ht (V d)
  let score (x : Words N S (V d)) := spin (∑ i, ∑ k, x.val i k*a i k)
  have H (u : EndSite N S → {x : V d // x ≠ 0}) : score (e.symm u) = spin (∑ i : S, ∑ k, (u (owner N S ht i)).1 k * a i k) := by
    unfold score
    congr 1
    let g (i : I) := ∑ k, (e.symm u).1 i k*a i k
    change (∑ i, g i) = _
    calc
      _ = ∑ i ∈ S, g i := by
        symm; apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hx : (e.symm u).1 i = 0 := by by_contra h; exact hi (((e.symm u).2.1 i).mp h)
        simp [g,hx]
      _ = ∑ i : S, g i := Finset.sum_subtype S (fun _ => Iff.rfl) g
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        have hx : (e.symm u).1 i = (u (owner N S ht i)).1 := by simp [e,colourEquiv,owner,i.2]
        simp only [g,hx]
  change ∑ x, score x = _
  rw [← e.symm.sum_comp score]
  simp_rw [H]
  exact run_character (owner N S ht) (fun i : S => a i)

lemma owner_single {i j : S} (h : ∀ t ∈ S, N t ≠ i.val) (eq : (owner N S ht j).val=i.val) : j = i := by
  let k := dist N S ht j.1 - 1
  change N^[k] j.val = i.val at eq
  by_cases hk : k=0
  · apply Subtype.ext; simpa only [hk,Function.iterate_zero_apply] using eq
  · have hd := dist_step N S ht j.2
    have hb : k-1 < dist N S ht j.val := by dsimp [k]; omega
    exfalso
    apply h _ (in_before N S ht hb)
    rw [← Function.iterate_succ_apply' N (k-1) j.val,show (k-1).succ=k by omega]
    exact eq

end Part1


namespace Hyper
abbrev F := ZMod 2
abbrev V (n : ℕ) := Fin n → F

def functional {d : ℕ} (a : V d) : V d →ₗ[F] F := {
  toFun := fun x => ∑ i,a i*x i
  map_add' := by intro x y; simp [mul_add,Finset.sum_add_distrib]
  map_smul' := by intro c x; simp [Finset.mul_sum,mul_left_comm] }

lemma kernel_card {d : ℕ} (a : V d) (ha : a≠0) : Nat.card (functional a).ker = 2^(d-1) := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, a j≠0 := by simpa [funext_iff] using ha
  have sur : Function.Surjective (functional a) := by
    intro y; refine ⟨Pi.single j (y/a j),?_⟩
    change (∑ i, a i * Pi.single (M:=fun _ : Fin d => F) j (y/a j) i) = y
    rw [Finset.sum_eq_single j] <;> simp_all; field_simp
  have h := (functional a).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr sur,finrank_top,Module.finrank_self,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at h
  rw [Module.natCard_eq_pow_finrank (K:=F),Nat.card_eq_fintype_card,ZMod.card,show Module.finrank F (functional a).ker=d-1 by omega]

lemma nonzero_card (X : Type*) [Zero X] [Finite X] : Nat.card {x : X // x ≠ 0} = Nat.card X - 1 := by
  classical
  have := Fintype.ofFinite X
  simp [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]

lemma dependent_witness {I : Type*} {d : ℕ} (x : I → V d) :
    ¬ LinearIndependent F (fun k : Fin d => fun i => x i k) ↔
    ∃ a : V d, a≠0 ∧ ∀ i, x i∈(functional a).ker := by
  rw [Fintype.not_linearIndependent_iff]
  constructor
  · rintro ⟨a,hs,k,hk⟩
    refine ⟨a,fun e => hk (congrFun e k),?_⟩
    intro i; change (∑ k,a k*x i k)=0; simpa [Finset.sum_apply] using congrFun hs i
  · rintro ⟨a,h,ha⟩
    obtain ⟨k,hk⟩ : ∃ k,a k≠0 := by simpa [funext_iff] using h
    exact ⟨a,funext (fun i => by simpa [Finset.sum_apply] using (show (∑ k,a k*x i k)=0 from ha i)),k,hk⟩

end Hyper


section Part2

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

def energy (v : Fin 2 → ℝ) := v 0 ^ 2 + v 1 ^ 2

def block (r : ℝ) (b : Bool) : Mat :=
  if b then !![2,2*r;2*r,1+r^2] else !![1,r;r,1]

noncomputable def gain (r : ℝ) (b : Bool) : ℝ :=
  if b then (1+r)^2*(1-1/(4*(1+r))) else 1+r

lemma marked {r : ℝ} (hr : 5/3 ≤ r) (x y : ℝ) :
    (2*x+2*r*y)^2+(2*r*x+(1+r^2)*y)^2 ≤ (gain r true)^2*(x^2+y^2) := by
  have hL : 0 < 1+r := by linarith
  let C := (1+r)^2-(1+r)/4
  have e : gain r true = C := by dsimp [gain,C]; field_simp [hL.ne']
  rw [e]
  have a : 2+8*r/3 ≤ C := by dsimp [C]; nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ r+3/4 by linarith)]
  have b : 1+r^2+3*r/2 ≤ C := by dsimp [C]; linarith
  have r0 : 0 ≤ r := by linarith
  have c0 : 0 ≤ C := by linarith
  have s1 : (2*x+2*r*y)^2 ≤ (2+8*r/3)*(2*x^2+3*r/2*y^2) := by
    nlinarith [mul_nonneg r0 (sq_nonneg (4*x-3*y))]
  have s2 : (2*r*x+(1+r^2)*y)^2 ≤ (1+r^2+3*r/2)*(8*r/3*x^2+(1+r^2)*y^2) := by
    nlinarith [mul_nonneg (mul_nonneg r0 (show 0 ≤ 1+r^2 by positivity)) (sq_nonneg (4*x-3*y))]
  have s := add_le_add (s1.trans (mul_le_mul_of_nonneg_right a (by positivity)))
    (s2.trans (mul_le_mul_of_nonneg_right b (by positivity)))
  have t := add_le_add (mul_le_mul_of_nonneg_right a (sq_nonneg x)) (mul_le_mul_of_nonneg_right b (sq_nonneg y))
  nlinarith [mul_le_mul_of_nonneg_left t c0]

lemma step {r : ℝ} (hr : 5/3 ≤ r) (b : Bool) (v : Fin 2 → ℝ) :
    energy ((block r b).mulVec v) ≤ (gain r b)^2*energy v := by
  cases b
  · simp [block, gain, energy, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [mul_nonneg (show 0 ≤ r by linarith) (sq_nonneg (v 0-v 1))]
  · simpa [block, gain, energy, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using marked hr (v 0) (v 1)

lemma total {r : ℝ} (hr : 5/3 ≤ r) (s : List Bool) (v : Fin 2 → ℝ) :
    energy (((s.map (block r)).prod).mulVec v) ≤ ((s.map (gain r)).prod)^2*energy v := by
  induction s with
  | nil => simp
  | cons b s ih =>
    simp only [List.map_cons,List.prod_cons,← Matrix.mulVec_mulVec,mul_pow]
    exact (step hr b _).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ih (sq_nonneg (gain r b)))

lemma trace_of_energy {M : Mat} {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ v, energy (M.mulVec v) ≤ s^2*energy v) : |M.trace| ≤ 2*s := by
  have h₀ := h (Pi.single 0 1)
  have h₁ := h (Pi.single 1 1)
  simp [energy] at h₀ h₁
  have h0 : |M 0 0| ≤ s := (sq_le_sq₀ (abs_nonneg _) hs).mp (by rw [sq_abs]; linarith [sq_nonneg (M 1 0)])
  have h1 : |M 1 1| ≤ s := (sq_le_sq₀ (abs_nonneg _) hs).mp (by rw [sq_abs]; linarith [sq_nonneg (M 0 1)])
  rw [Matrix.trace_fin_two]
  exact (abs_add_le ..).trans (by linarith)

lemma marked_trace {r : ℝ} (hr : 5/3 ≤ r) (s : List Bool) :
    |((s.map (block r)).prod).trace| ≤
      2*(1+r)^(s.length+s.count true)*(1-1/(4*(1+r)))^(s.count true) := by
  have hL : 0 < 1+r := by linarith
  have he : 0 ≤ 1-1/(4*(1+r)) := sub_nonneg.mpr ((div_le_iff₀ (by positivity)).mpr (by linarith))
  have scale : (s.map (gain r)).prod = (1+r)^(s.length+s.count true)*(1-1/(4*(1+r)))^(s.count true) := by
    induction s with
    | nil => simp
    | cons b s ih => cases b <;> simp [gain,ih,pow_add,pow_succ] <;> ring
  rw [mul_assoc, ← scale]
  exact trace_of_energy (by rw [scale]; positivity) (total hr s)

def width : List Bool → ℕ
  | [] => 0
  | false::s => width s + 1
  | true::s => width s + 2

def localWeight (r : ℝ) (x u z : Fin 2) : ℝ :=
  if x=0 ∧ u=1 ∧ z=0 then 1 else block r false x u * block r false u z

lemma local_sum (r : ℝ) (x z : Fin 2) : (∑ u, localWeight r x u z)=block r true x z := by
  fin_cases x <;> fin_cases z <;> simp [localWeight,block,Fin.sum_univ_two] <;> ring

def walk (r : ℝ) : (s : List Bool) → Fin 2 → (Fin (width s) → Fin 2) → Fin 2 → ℝ
  | [], x, _, y => if x=y then 1 else 0
  | false::s, x, v, y => block r false x (v (0 : Fin (width s+1)))*walk r s (v (0 : Fin (width s+1))) (Fin.tail v) y
  | true::s, x, v, y => localWeight r x (v (0 : Fin (width s+2))) (Fin.tail v 0)*walk r s (Fin.tail v 0) (Fin.tail (Fin.tail v)) y

lemma sum_head {n : ℕ} (f : (Fin (n+1) → Fin 2) → ℝ) :
    (∑ v, f v) = ∑ x, ∑ v, f (Fin.cons x v) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Fin 2)).sum_comp f,Fintype.sum_prod_type]
  rfl

lemma walk_entries (r : ℝ) (s : List Bool) (x y : Fin 2) :
    (∑ v, walk r s x v y) = (s.map (block r)).prod x y := by
  induction s generalizing x y with
  | nil => change (∑ _ : Fin 0 → Fin 2, if x=y then (1:ℝ) else 0) = _; simp [Matrix.one_apply]
  | cons b s ih =>
    cases b
    · change (∑ v : Fin (width s+1) → Fin 2, _) = _
      rw [sum_head]
      simp only [walk,Fin.cons_zero,Fin.tail_cons,← Finset.mul_sum,ih,List.map_cons,List.prod_cons,Matrix.mul_apply]
    · change (∑ v : Fin ((width s+1)+1) → Fin 2, _) = _
      rw [sum_head]
      simp only [walk,Fin.cons_zero,Fin.tail_cons]
      simp_rw [sum_head (n:=width s),Fin.cons_zero,Fin.tail_cons,← Finset.mul_sum,ih]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul,local_sum]
      rfl

lemma closed_walk (r : ℝ) (s : List Bool) :
    (∑ x, ∑ v, walk r s x v x) = ((s.map (block r)).prod).trace := by
  simp only [walk_entries,Matrix.trace,Matrix.diag_apply]

def marks : List Bool → Finset ℕ
  | [] => ∅
  | false::s => (marks s).image (·+1)
  | true::s => insert 1 ((marks s).image (·+2))
lemma marks_card (s : List Bool) : (marks s).card = s.count true := by
  induction s with
  | nil => simp [marks]
  | cons b s ih => cases b <;> simp [marks,Finset.card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h),ih]
lemma width_correct (s : List Bool) : width s=s.length+s.count true := by
  induction s with
  | nil => simp [width]
  | cons b s ih => cases b <;> simp [width,ih] <;> omega
lemma make_tiling (n : ℕ) (B : Finset ℕ) (hr : ∀ j ∈ B, 0 < j ∧ j < n)
    (ha : ∀ j ∈ B, j+1 ∉ B) : ∃ t, width t=n ∧ marks t=B := by
  induction n using Nat.strong_induction_on generalizing B with
  | ind n ih =>
    by_cases hz : n=0
    · refine ⟨[],hz.symm,?_⟩
      apply Finset.eq_empty_iff_forall_notMem.mpr ?_ |>.symm
      intro j hj; have := hr j hj; omega
    by_cases h : 1 ∈ B
    · have h2 := hr 1 h
      let C := (Finset.range (n-2)).filter (fun j => j+2 ∈ B)
      have hc (j : ℕ) : j∈C ↔ j < n-2 ∧ j+2 ∈ B := by simp [C]
      obtain ⟨t,hw,hm⟩ := ih (n-2) (by omega) C (by
        intro j hj; obtain ⟨hj,hB⟩ := (hc j).mp hj; refine ⟨?_,hj⟩
        by_contra! h0; have he : j=0 := by omega
        subst j; exact ha 1 h hB) (by
        intro j hj h'; exact ha (j+2) ((hc j).mp hj).2 ((hc (j+1)).mp h').2)
      refine ⟨true::t, by simp [width,hw]; omega,?_⟩
      ext j; simp only [marks,hm,Finset.mem_insert,Finset.mem_image]
      constructor
      · rintro (rfl|⟨k,hk,rfl⟩); exact h; exact ((hc k).mp hk).2
      · intro hj; have r := hr j hj
        by_cases he : j=1
        · exact Or.inl he
        · right; refine ⟨j-2,(hc _).mpr ⟨by omega,?_⟩,by omega⟩; convert hj using 1; omega
    · let C := (Finset.range (n-1)).filter (fun j => j+1 ∈ B)
      have hc (j : ℕ) : j∈C ↔ j < n-1 ∧ j+1 ∈ B := by simp [C]
      obtain ⟨t,hw,hm⟩ := ih (n-1) (by omega) C (by
        intro j hj; obtain ⟨hj,hB⟩ := (hc j).mp hj; refine ⟨?_,hj⟩
        by_contra! h0; have he : j=0 := by omega
        subst j; exact h hB) (by
        intro j hj h'; exact ha (j+1) ((hc j).mp hj).2 ((hc (j+1)).mp h').2)
      refine ⟨false::t,by simp [width,hw]; omega,?_⟩
      ext j; simp only [marks,hm,Finset.mem_image]
      constructor
      · rintro ⟨k,hk,rfl⟩; exact ((hc k).mp hk).2
      · intro hj; have r := hr j hj; refine ⟨j-1,(hc _).mpr ⟨by omega,?_⟩,by omega⟩; convert hj using 1; omega

noncomputable def fee (r : ℝ) (x u z : Fin 2) := if x=0 ∧ u=1 ∧ z=0 then 1/r^2 else 1
lemma local_fee {r : ℝ} (hr : r ≠ 0) (x u z : Fin 2) : localWeight r x u z = block r false x u * block r false u z * fee r x u z := by
  by_cases h : x=0 ∧ u=1 ∧ z=0
  · obtain ⟨rfl,rfl,rfl⟩ := h; simp [localWeight,fee,block]; field_simp [hr]
  · simp [localWeight,fee,h]

def edgeProd (r : ℝ) (n : ℕ) (f : ℕ → Fin 2) := ∏ k ∈ Finset.range n, block r false (f k) (f (k+1))
def sh (f : ℕ → Fin 2) (n : ℕ) := fun j => f (j+n)
lemma edge_step (r : ℝ) (n : ℕ) (f : ℕ → Fin 2) : edgeProd r (n+1) f = block r false (f 0) (f 1)*edgeProd r n (sh f 1) := by
  simp [edgeProd,sh,Finset.prod_range_succ',mul_comm,Nat.add_assoc]

noncomputable def fees (r : ℝ) (n : ℕ) (f : ℕ → Fin 2) := fee r (f (n-1)) (f n) (f (n+1))
lemma marks_pos (s : List Bool) (i : ℕ) (hi : i∈marks s) : 0 < i := by
  cases s with
  | nil => simp [marks] at hi
  | cons b s => cases b <;> simp [marks] at hi <;> omega
lemma fees_shift {r : ℝ} (f : ℕ → Fin 2) (j k : ℕ) (hj : 0 < j) : fees r (j+k) f = fees r j (sh f k) := by
  unfold fees sh; congr 2 <;> omega

lemma walk_factor {r : ℝ} (hr : r ≠ 0) (s : List Bool) (f : ℕ → Fin 2) :
    walk r s (f 0) (fun i => f (i.val+1)) (f (width s)) =
      edgeProd r (width s) f * ∏ j ∈ marks s, fees r j f := by
  induction s generalizing f with
  | nil => simp [walk,width,edgeProd,marks]
  | cons b s ih =>
    have shift (k : ℕ) : (∏ j ∈ (marks s).image (·+k), fees r j f) = ∏ j ∈ marks s, fees r j (sh f k) := by
      rw [Finset.prod_image (fun _ _ _ _ h => Nat.add_right_cancel h)]
      exact Finset.prod_congr rfl fun j hj => fees_shift f j k (marks_pos s j hj)
    cases b
    · change block r false (f 0) (f 1)*walk r s (sh f 1 0) (fun i => sh f 1 (i.val+1)) (sh f 1 (width s)) = _
      rw [ih]; simp only [width,edge_step,marks,shift,mul_assoc]
    · change localWeight r (f 0) (f 1) (f 2)*walk r s (sh f 2 0) (fun i => sh f 2 (i.val+1)) (sh f 2 (width s)) = _
      have hn : 1 ∉ (marks s).image (·+2) := by
        intro h; obtain ⟨j,_,he⟩ := Finset.mem_image.mp h; omega
      rw [ih,local_fee hr]
      change _ = edgeProd r ((width s+1)+1) f * ∏ j ∈ insert 1 ((marks s).image (·+2)), fees r j f
      rw [Finset.prod_insert hn,shift,edge_step r (width s+1) f,edge_step r (width s) (sh f 1)]
      change _ = (block r false (f 0) (f 1)*(block r false (f 1) (f 2)*edgeProd r (width s) (sh f 2)))*(fee r (f 0) (f 1) (f 2)*_)
      ring

lemma walk_nonneg {r : ℝ} (hr : 0 ≤ r) (s : List Bool) (x : Fin 2) (v : Fin (width s) → Fin 2) (y : Fin 2) : 0 ≤ walk r s x v y := by
  have hT (i j : Fin 2) : 0 ≤ block r false i j := by fin_cases i <;> fin_cases j <;> simp [block,hr]
  induction s generalizing x y with
  | nil => simp [walk]; split <;> norm_num
  | cons b s ih => cases b
                   · exact mul_nonneg (hT ..) (ih ..)
                   · apply mul_nonneg _ (ih ..)
                     unfold localWeight; split
                     · norm_num
                     · exact mul_nonneg (hT ..) (hT ..)

def boundary {I : Type*} [Fintype I] [DecidableEq I] (N : I → I) (S : Finset I) := Finset.univ.filter (fun i => ¬(i ∈ S ↔ N i ∈ S))
lemma boundary_card {I : Type*} [Fintype I] [DecidableEq I] (N : Equiv.Perm I) (S : Finset I) :
    (boundary N S).card = 2*(S.filter (fun i => N i ∉ S)).card := by
  let T := S.map N.symm.toEmbedding
  have ht (i : I) : i ∈ T ↔ N i ∈ S := by simp [T]
  have he : boundary N S = (S \ T) ∪ (T \ S) := by
    ext i; simp only [boundary,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,Finset.mem_sdiff,ht]
    tauto
  have hS : S.filter (fun i => N i ∉ S) = S \ T := by ext i; simp [ht]
  have hd : Disjoint (S \ T) (T \ S) := by apply Finset.disjoint_left.mpr; intro i hi hj; exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  rw [he,hS,Finset.card_union_of_disjoint hd]
  have h := Finset.card_sdiff_add_card_inter S T
  have h' := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at h'
  have ht' : T.card=S.card := Finset.card_map _
  omega

def pos {n : ℕ} (hn : 0 < n) (i : ℕ) : Fin n := ⟨i%n,Nat.mod_lt _ hn⟩
def bits {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (k : ℕ) : Fin 2 := if pos hn k ∈ S then 1 else 0
lemma pos_val {n : ℕ} (hn : 0 < n) (i : Fin n) : pos hn i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
lemma bits_cycle {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) : bits hn S n=bits hn S 0 := by
  have h : pos hn n = pos hn 0 := Fin.ext (by simp [pos]); simp [bits,h]
lemma pos_rot {n : ℕ} (hn : 1 < n) (i : Fin n) : pos (by omega : 0 < n) (i.val+1) = finRotate n i := by
  let _ : NeZero n := ⟨by omega⟩
  apply Fin.ext
  rw [finRotate_apply]
  change (i.val+1)%n = (i.val+(1:Fin n).val)%n
  rw [show (1 : Fin n).val=1 from Nat.mod_eq_of_lt hn]
lemma edge_mask {n : ℕ} (hn : 1 < n) (S : Finset (Fin n)) (r : ℝ) :
    edgeProd r n (bits (by omega) S) = r^(boundary (finRotate n) S).card := by
  have hn0 : 0 < n := by omega
  rw [edgeProd,← Fin.prod_univ_eq_prod_range]
  have he (i : Fin n) : block r false (bits hn0 S i.val) (bits hn0 S (i.val+1)) = if i∈boundary (finRotate n) S then r else 1 := by
    by_cases h : i∈S <;> by_cases h' : finRotate n i∈S <;> simp [bits,pos_val,pos_rot hn,boundary,h,h',block,-finRotate_apply]
  simp_rw [he]
  rw [Finset.prod_ite]
  simp

def encBits {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) : Fin 2 × (Fin n → Fin 2) := (bits hn S 0,fun j => bits hn S (j.val+1))
lemma encBits_inj {n : ℕ} (hn : 0 < n) : Function.Injective (encBits hn) := by
  intro S T eq
  have eq0 : bits hn S 0=bits hn T 0 := congrArg Prod.fst eq
  have eq1 (i : Fin n) : bits hn S (i.val+1)=bits hn T (i.val+1) := congrFun (congrArg Prod.snd eq) i
  ext i
  have h : bits hn S i.val = bits hn T i.val := by
    cases e : i.val with
    | zero => exact eq0
    | succ k => exact eq1 ⟨k,by have := i.isLt; omega⟩
  by_cases hs : i∈S <;> by_cases ht : i∈T <;> simp [bits,pos_val,hs,ht] at h ⊢
lemma sum_masks {n : ℕ} (hn : 0 < n) (G : Fin 2 → (Fin n → Fin 2) → ℝ) (hG : ∀ x v, 0 ≤ G x v) :
    (∑ S, G (bits hn S 0) (fun j => bits hn S (j.val+1))) ≤ ∑ x, ∑ v, G x v := by
  let g (z : Fin 2 × (Fin n → Fin 2)) := G z.1 z.2
  change (∑ S, g (encBits hn S)) ≤ _
  calc
    _ = ∑ z ∈ Finset.univ.image (encBits hn), g z := (Finset.sum_image (encBits_inj hn).injOn).symm
    _ ≤ ∑ z, g z := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun z _ _ => hG z.1 z.2)
    _ = _ := Fintype.sum_prod_type g

def isolated {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (B : Finset ℕ) :=
  B.filter (fun j => bits hn S (j-1)=0 ∧ bits hn S j=1 ∧ bits hn S (j+1)=0)

lemma tiled_envelope (t : List Bool) (hn : 1 < width t) {r : ℝ} (hr : 5/3 ≤ r) :
    (∑ S : Finset (Fin (width t)), (r^2)^(S.filter (fun i => finRotate _ i ∉ S)).card *
      (1/r^2)^(isolated (by omega) S (marks t)).card) ≤
      2*(1+r)^(width t)*(1-1/(4*(1+r)))^(t.count true) := by
  have hn0 : 0 < width t := by omega
  have hr0 : 0 < r := by linarith
  have eqS (S : Finset (Fin (width t))) : (r^2)^(S.filter (fun i => finRotate _ i ∉ S)).card *
      (1/r^2)^(isolated hn0 S (marks t)).card = walk r t (bits hn0 S 0) (fun i => bits hn0 S (i.val+1)) (bits hn0 S 0) := by
    have H := walk_factor hr0.ne' t (bits hn0 S)
    rw [bits_cycle,edge_mask hn,boundary_card,pow_mul] at H
    rw [H]
    congr 1
    simp [isolated,fees,fee,Finset.prod_ite]
  simp_rw [eqS]
  calc
    _ ≤ ∑ x, ∑ v, walk r t x v x := sum_masks hn0 (fun x v => walk r t x v x) (fun x v => walk_nonneg hr0.le t x v x)
    _ = _ := closed_walk r t
    _ ≤ |((t.map (block r)).prod).trace| := le_abs_self _
    _ ≤ _ := by simpa only [width_correct] using marked_trace hr t

lemma support_envelope {n : ℕ} (hn : 1 < n) {r : ℝ} (hr : 5/3 ≤ r) (B : Finset ℕ)
    (hB : ∀ j ∈ B, 0 < j ∧ j < n) (hsep : ∀ j ∈ B, j+1 ∉ B) :
    (∑ S : Finset (Fin n), (r^2)^(S.filter (fun i => finRotate _ i ∉ S)).card *
       (1/r^2)^(isolated (by omega) S B).card) ≤ 2*(1+r)^n*(1-1/(4*(1+r)))^B.card := by
  obtain ⟨t,hw,hb⟩ := make_tiling n B hB hsep
  subst n; subst B
  simpa only [marks_card] using tiled_envelope t hn hr

end Part2

section Part3
lemma packed_hits {n : ℕ} (H : Finset (Fin n)) :
    ∃ B : Finset (Fin n), B ⊆ H ∧ H.card/2 ≤ B.card ∧
      (∀ i ∈ B, i.val ≠ 0) ∧ (∀ i ∈ B, ∀ j ∈ B, i.val+1 ≠ j.val) := by
  classical
  let D := H.filter (fun i => i.val ≠ 0)
  let E := D.filter (fun i => i.val % 2=0)
  let O := D.filter (fun i => i.val % 2≠0)
  have hEO : E.card+O.card=D.card := Finset.card_filter_add_card_filter_not ..
  have hdrop : H.card ≤ D.card+1 := by
    have hsplit : D.card + (H.filter (fun i => ¬i.val ≠ 0)).card = H.card := Finset.card_filter_add_card_filter_not ..
    have hsmall : (H.filter (fun i => ¬i.val ≠ 0)).card ≤ 1 := Finset.card_le_one.mpr (by
      intro i hi j hj
      simp only [Finset.mem_filter,not_not] at hi hj
      exact Fin.ext (hi.2.trans hj.2.symm))
    omega
  by_cases h : E.card ≤ O.card
  · refine ⟨O,?_,by omega,?_,?_⟩
    · intro i hi; exact ((Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1)
    · intro i hi; exact ((Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2)
    · intro i hi j hj; have hi' := (Finset.mem_filter.mp hi).2; have hj' := (Finset.mem_filter.mp hj).2; omega
  · refine ⟨E,?_,by omega,?_,?_⟩
    · intro i hi; exact ((Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1)
    · intro i hi; exact ((Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2)
    · intro i hi j hj; have hi' := (Finset.mem_filter.mp hi).2; have hj' := (Finset.mem_filter.mp hj).2; omega
end Part3

section Part4
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma boundary_inj (N : I → I) (j : I) (hc : ∀ i, ∃ k, N^[k] j=i) :
    Function.Injective (fun S : Finset I => (decide (j ∈ S),boundary N S)) := by
  intro S T he
  have base : j ∈ S ↔ j ∈ T := by simpa using congrArg Prod.fst he
  have eq := congrArg Prod.snd he
  have step (i : I) (h : i ∈ S ↔ i ∈ T) : N i ∈ S ↔ N i ∈ T := by
    have g : i ∈ boundary N S ↔ i ∈ boundary N T := by rw [show boundary N S = boundary N T from eq]
    simp only [boundary,Finset.mem_filter,Finset.mem_univ,true_and] at g
    tauto
  have allK (k : ℕ) : N^[k] j ∈ S ↔ N^[k] j ∈ T := by
    induction k with
    | zero => exact base
    | succ k ih => rw [Function.iterate_succ_apply']; exact step _ ih
  ext i
  obtain ⟨k,rfl⟩ := hc i
  exact allK k

lemma base_sum (N : Equiv.Perm I) (j : I) (hc : ∀ i, ∃ k, N^[k] j=i) {r : ℝ} (hr : 0 ≤ r) :
    (∑ S : Finset I, (r^2)^(S.filter (fun i => N i ∉ S)).card) ≤ 2*(1+r)^Fintype.card I := by
  classical
  let enc (S : Finset I) := (decide (j∈S),boundary N S)
  let f (z : Bool × Finset I) := r^z.2.card
  have inj : Function.Injective enc := boundary_inj N j hc
  have H (S : Finset I) : (r^2)^(S.filter (fun i => N i ∉ S)).card = f (enc S) := by rw [←pow_mul,←boundary_card]
  have hp : (∑ t : Finset I, r^t.card) = (1+r)^Fintype.card I := by
    simpa [add_comm] using Fintype.sum_pow_mul_eq_add_pow I r (1:ℝ)
  simp_rw [H]
  calc
    _ = ∑ z ∈ Finset.univ.image enc, f z := (Finset.sum_image inj.injOn).symm
    _ ≤ ∑ z, f z := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by dsimp [f]; positivity)
    _ = _ := by rw [Fintype.sum_prod_type]; simp [f,hp,two_mul]

end Part4

section Part5
lemma flagged_product {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {d : ℕ} (hd : 1 ≤ d)
    (p : I → J) (a : I → V d) (B : Finset I) (hn : ∀ i ∈ B, a i ≠ 0)
    (hiso : ∀ i ∈ B, ∀ j, p j=p i → j=i) :
    |∏ j, (if runLabel p a j=0 then (2:ℤ)^d-1 else -1)| ≤ ((2:ℤ)^d-1)^(Fintype.card J - B.card) := by
  classical
  let E := B.image p
  have hcard : E.card=B.card := Finset.card_image_of_injOn (fun i hi j _ e => (hiso _ hi _ e.symm).symm)
  have he (j : J) (hj : j ∈ E) : runLabel p a j ≠ 0 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    have H : (Finset.univ.filter (fun t => p t=p i)) = {i} := by
      ext t; simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      exact ⟨hiso i hi t,fun h => congrArg p h⟩
    have hl : runLabel p a (p i) = a i := by ext k; simp [runLabel,H]
    exact hl ▸ hn i hi
  have qle : (1:ℤ) ≤ 2^d-1 := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) hd
    norm_num at h; omega
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ j : J, if j ∈ E then (1:ℤ) else 2^d-1 := by
      apply Finset.prod_le_prod₀ (fun j _ => abs_nonneg _)
      intro j _
      by_cases hj : j ∈ E
      · simp [hj,he j hj]
      · by_cases h : runLabel p a j=0 <;> simp [hj,h,abs_of_nonneg (by omega : (0:ℤ) ≤ 2^d-1),qle]
    _ = _ := by
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one,one_mul,Finset.prod_const]
      congr 1
      rw [← hcard]
      have H : Finset.univ.filter (fun j => j ∉ E) = Finset.univ \ E := by ext; simp
      rw [H,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
end Part5

namespace Join
open SupportGeometry

lemma reach {n : ℕ} (S : Finset (Fin n)) (h : S ≠ Finset.univ) (i : Fin n) :
    ∃ k : ℕ, next^[k] i ∉ S := by
  by_contra! h'
  apply h
  apply Finset.eq_univ_of_forall
  intro j
  obtain ⟨k,hk⟩ := all_if_forward (fun j => ∃ k : ℕ, next^[k] i=j) i ⟨0,rfl⟩
    (fun j ⟨k,hk⟩ => ⟨k+1,by rw [Function.iterate_succ_apply',hk]⟩) j
  exact hk ▸ h' k

noncomputable def runs {n : ℕ} (S : Finset (Fin n)) := (S.filter (fun i => next i ∉ S)).card

lemma ends_card {n : ℕ} (S : Finset (Fin n)) : Nat.card (EndSite next S) = runs S := by
  classical
  let e : EndSite next S ≃ ↥(S.filter (fun i => next i ∉ S)) :=
    Equiv.subtypeEquivRight (fun i => by simp)
  exact (Nat.card_congr e).trans (Nat.card_eq_finsetCard _)

lemma word_card {n d : ℕ} (S : Finset (Fin n)) (h : S≠Finset.univ) :
    (Census.words d S).card = (2^d-1)^runs S := by
  classical
  have hw := word_count next S (reach S h) (V d)
  rw [ends_card,Hyper.nonzero_card] at hw
  calc
    (Census.words d S).card = Nat.card (Words next S (V d)) := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
      apply congrArg Finset.card
      ext x
      simp [Census.words,Census.Word]
    _ = _ := by simpa [V,Nat.card_eq_fintype_card,ZMod.card] using hw

open Classical in
noncomputable def cut {n d : ℕ} (S : Finset (Fin n)) (a : V d) :=
  (Census.words d S).filter (fun x => ∀ i,x i∈(Hyper.functional a).ker)

lemma cut_le {n d : ℕ} (S : Finset (Fin n)) (h : S≠Finset.univ) (a : V d) (ha : a≠0) :
    (cut S a).card ≤ (2^(d-1)-1)^runs S := by
  classical
  let K := (Hyper.functional a).ker
  let lift (z : ↥(cut S a)) (i : Fin n) : K := ⟨z.val i,(Finset.mem_filter.mp z.prop).2 i⟩
  have hz (z : ↥(cut S a)) : Census.Word S z.val :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp z.prop).1).2
  let f (z : ↥(cut S a)) : Words next S K := ⟨lift z,by
    constructor
    · intro i
      rw [←(hz z).1 i]
      exact not_congr Subtype.coe_inj.symm
    · intro i hi hj
      exact Subtype.ext ((hz z).2 i hi hj)⟩
  have fi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    funext i
    exact congrArg (fun v : Words next S K => (v.val i).val) he
  have hh := Nat.card_le_card_of_injective f fi
  rw [Nat.card_eq_finsetCard, word_count next S (reach S h), ends_card, Hyper.nonzero_card, Hyper.kernel_card a ha] at hh
  exact hh

lemma dep_le {n m d : ℕ} (H : Fin n → V m) (S : Finset (Fin n)) (hs : S≠Finset.univ) :
    Census.dep d H S ≤ (2^d-1) * (2^(d-1)-1)^runs S := by
  classical
  let A := (Finset.univ : Finset (V d)).erase 0
  have sub : ((Census.words d S).filter (fun x => Census.synd H x=0)).filter (fun x => ¬ LinearIndependent F (Census.Rows x)) ⊆ A.biUnion (cut S) := by
    intro x hx
    obtain ⟨hx,hdep⟩ := Finset.mem_filter.mp hx
    obtain ⟨a,ha,ha'⟩ := (Hyper.dependent_witness x).mp hdep
    exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_erase.mpr ⟨ha,Finset.mem_univ _⟩, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,ha'⟩⟩
  have num : A.card=2^d-1 := by simp [A,Finset.card_erase_of_mem,V,ZMod.card]
  calc
    Census.dep d H S ≤ (A.biUnion (cut S)).card := Finset.card_le_card sub
    _ ≤ ∑ a ∈ A, (cut S a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, (2^(d-1)-1)^runs S := Finset.sum_le_sum (fun a ha => cut_le S hs a (Finset.ne_of_mem_erase ha))
    _ = _ := by simp [num]

end Join

namespace Join
open SupportGeometry (next)

noncomputable def q (d : ℕ) : ℝ := 2^d-1
noncomputable def L (d : ℕ) : ℝ := 1+Real.sqrt (q d)
noncomputable def M (m d : ℕ) : ℝ := 2^(m*d)
noncomputable def t (d : ℕ) : ℝ := 1-1/(4*L d)

lemma q_cast (d : ℕ) : ((2^d-1 : ℕ):ℝ)=q d := by
  have h : 0 < (2:ℕ)^d := by positivity
  rw [Nat.cast_sub (by omega : 1 ≤ (2:ℕ)^d)]
  norm_num [q]

lemma q_nn (d : ℕ) : 0 ≤ q d := q_cast d ▸ Nat.cast_nonneg _
lemma rot_eq {n : ℕ} (hn : 1<n) : ((finRotate n) : Fin n → Fin n) = next := (funext (pos_rot hn)).symm

lemma dep_sum {n m d : ℕ} (hn : 1<n) (H : Fin n → V m) :
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase Finset.univ, (Census.dep d H S : ℝ)) ≤ 2*q d*(L (d-1))^n := by
  classical
  let A := (Finset.univ : Finset (Finset (Fin n))).erase Finset.univ
  have sub (S : Finset (Fin n)) (h : S∈A) : (Census.dep d H S : ℝ) ≤ q d*(q (d-1))^runs S := by
    rw [← q_cast d,← q_cast (d-1)]
    exact_mod_cast dep_le H S (Finset.ne_of_mem_erase h)
  let j : Fin n := ⟨0,by omega⟩
  have hc : ∀ i : Fin n, ∃ k : ℕ, (finRotate n)^[k] j=i := by
    rw [rot_eq hn]
    exact SupportGeometry.all_if_forward (fun i => ∃ k : ℕ, next^[k] j=i) j ⟨0,rfl⟩
      (fun i ⟨k,hk⟩ => ⟨k+1,by rw [Function.iterate_succ_apply',hk]⟩)
  have base := base_sum (finRotate n) j hc (Real.sqrt_nonneg (q (d-1)))
  rw [Real.sq_sqrt (q_nn _),Fintype.card_fin] at base
  simp only [rot_eq hn] at base
  change (∑ S : Finset (Fin n), q (d-1)^runs S) ≤ 2*(L (d-1))^n at base
  calc
    _ ≤ ∑ S∈A, q d*(q (d-1))^runs S := Finset.sum_le_sum sub
    _ ≤ ∑ S : Finset (Fin n), q d*(q (d-1))^runs S :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => mul_nonneg (q_nn _) (pow_nonneg (q_nn _) _))
    _ = q d*∑ S : Finset (Fin n), (q (d-1))^runs S := (Finset.mul_sum ..).symm
    _ ≤ q d*(2*(L (d-1))^n) := mul_le_mul_of_nonneg_left base (q_nn d)
    _ = _ := by ring

end Join

namespace Join
open SupportGeometry (next)

lemma bias_prod {n m d : ℕ} (H : Fin n → V m) (a : Fin d × Fin m → F)
    (S : Finset (Fin n)) (hs : S≠Finset.univ) :
    Census.bias H a S = ∏ j, (if runLabel (owner next S (reach S hs)) (fun i : S => Census.phase H a i) j = 0 then (2:ℤ)^d-1 else -1) := by
  classical
  change (∑ x ∈ Census.words d S,spin (∑ i,∑ k,x i k*Census.phase H a i k)) = _
  rw [Finset.sum_subtype (Census.words d S) (p:=Census.Word S) (fun x => by simp [Census.words])]
  convert! word_character next S (reach S hs) (Census.phase H a) using 1 <;> congr! 4

lemma next_pos {n : ℕ} (hn : 0<n) (j : ℕ) : next (pos hn j) = pos hn (j+1) := by
  apply Fin.ext
  exact Nat.mod_add_mod j n 1

lemma mask_bound {n m d : ℕ} (hn : 1<n) (hd : 1≤d) (H : Fin n → V m) (a : Fin d × Fin m → F)
    (B : Finset ℕ) (hB : ∀ j ∈ B, 0<j ∧ j<n ∧ Census.phase H a (pos (by omega) j) ≠ 0)
    (S : Finset (Fin n)) (hs : S≠Finset.univ) :
    |(Census.bias H a S : ℝ)| ≤ ((2:ℝ)^d-1)^runs S * (1/((2:ℝ)^d-1))^(isolated (by omega) S B).card := by
  classical
  let hn0 : 0<n := by omega
  let J := isolated hn0 S B
  have jB (z : ↥J) : z.val ∈ B := (Finset.mem_filter.mp z.prop).1
  have jb (z : ↥J) : bits hn0 S (z.val-1)=0 ∧ bits hn0 S z.val=1 ∧ bits hn0 S (z.val+1)=0 :=
    (Finset.mem_filter.mp z.prop).2
  have mem (z : ↥J) : pos hn0 z.val ∈ S := by
    by_contra v
    simpa [bits,v] using (jb z).2.1
  have miss (k : ℕ) (hk : bits hn0 S k=0) : pos hn0 k ∉ S := by
    intro hk'
    simpa [bits,hk'] using hk
  let e : ↥J ↪ ↥S := ⟨fun z => ⟨pos hn0 z.val,mem z⟩,by
    intro x y he
    have he' := congrArg (fun z : ↥S => z.val.val) he
    apply Subtype.ext
    simpa [pos,Nat.mod_eq_of_lt (hB _ (jB x)).2.1,Nat.mod_eq_of_lt (hB _ (jB y)).2.1] using he'⟩
  let D := J.attach.map e
  let p := owner next S (reach S hs)
  have pred (z : ↥J) (t : Fin n) (ht : t∈S) : next t ≠ pos hn0 z.val := by
    intro eq
    have eq' : next (pos hn0 (z.val-1)) = pos hn0 z.val := by
      rw [next_pos, Nat.sub_add_cancel (hB _ (jB z)).1]
    have inj : Function.Injective (@next n) := by
      have hh : (@next n) = (finRotate n) := funext (pos_rot hn)
      rw [hh]
      exact (finRotate n).injective
    exact miss _ (jb z).1 (inj (eq.trans eq'.symm) ▸ ht)
  have iso (i : ↥S) (hi : i∈D) (j : ↥S) (eq : p j=p i) : j=i := by
    obtain ⟨z,_,rfl⟩ := Finset.mem_map.mp hi
    apply owner_single next S (reach S hs) (pred z)
    have last : (p (e z)).val=pos hn0 z.val :=
      finish_last next S (reach S hs) (mem z) (by change next (pos hn0 z.val) ∉ S; rw [next_pos]; exact miss _ (jb z).2.2)
    exact (congrArg Subtype.val eq).trans last
  have hz (i : ↥S) (hi : i∈D) : Census.phase H a i ≠ 0 := by
    obtain ⟨z,_,rfl⟩ := Finset.mem_map.mp hi
    exact (hB _ (jB z)).2.2
  have hp := flagged_product hd p (fun i : ↥S => Census.phase H a i) D hz iso
  have hh : Fintype.card (EndSite next S) = runs S := by simpa [Nat.card_eq_fintype_card] using ends_card S
  have hD : D.card=J.card := by simp [D]
  have le : J.card ≤ runs S := by
    have size : (D.image p).card=D.card := Finset.card_image_of_injOn (fun i hi j _ hij => (iso _ hi j hij.symm).symm)
    rw [←hD,←size,←hh]; exact Finset.card_le_univ _
  rw [←bias_prod H a S hs, hh,hD] at hp
  have hp' : |(Census.bias H a S:ℝ)| ≤ ((2:ℝ)^d-1)^(runs S-J.card) := by exact_mod_cast hp
  have hq : (0:ℝ)<2^d-1 := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hd
    norm_num at h; linarith
  calc
    _ ≤ _ := hp'
    _ = _ := by
      change _ = ((2:ℝ)^d-1)^runs S * (1/((2:ℝ)^d-1))^J.card
      have he := pow_add ((2:ℝ)^d-1) (runs S-J.card) J.card
      rw [Nat.sub_add_cancel le] at he
      rw [he,one_div,inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hq.ne'),mul_one]

end Join

namespace Join

lemma bias_sum {n m d w : ℕ} (hn : 1<n) (hd : 2≤d) (H : Fin n → V m)
    (hw : ∀ a : V m, a ≠ 0 → w ≤ (Finset.univ.filter (fun i : Fin n => (∑ b,a b*H i b) ≠ 0)).card)
    (a : Fin d × Fin m → F) (ha : a≠0) :
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase Finset.univ, |(Census.bias H a S : ℝ)|) ≤
      2*(L d)^n*(t d)^(w/2) := by
  classical
  let hit := Finset.univ.filter (fun i : Fin n => Census.phase H a i ≠ 0)
  have nh : w≤hit.card := Census.phase_hits H hw a ha
  obtain ⟨B,sub,card,posB,sep⟩ := packed_hits hit
  let e : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
  let C := B.map e
  let hn0 : 0<n := by omega
  have marksB (j : ℕ) (hj : j∈C) : 0<j ∧ j<n ∧ Census.phase H a (pos hn0 j) ≠ 0 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    exact ⟨Nat.pos_of_ne_zero (posB _ hi),i.isLt,(pos_val hn0 i).symm ▸ (Finset.mem_filter.mp (sub hi)).2⟩
  have dis (j : ℕ) (hj : j∈C) : j+1∉C := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    intro hk
    obtain ⟨k,hk,h⟩ := Finset.mem_map.mp hk
    exact sep i hi k hk h.symm
  let A := (Finset.univ : Finset (Finset (Fin n))).erase Finset.univ
  have rbound : (5:ℝ)/3≤ Real.sqrt (q d) := by
    apply Real.le_sqrt_of_sq_le
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hd
    norm_num at h; unfold q; linarith
  have env := support_envelope hn rbound C (fun j hj => ⟨(marksB j hj).1,(marksB j hj).2.1⟩) dis
  rw [Real.sq_sqrt (q_nn d)] at env
  simp only [rot_eq hn] at env
  have hc : C.card=B.card := Finset.card_map _
  rw [hc] at env
  change (∑ S : Finset (Fin n), q d ^ runs S * (1/q d)^(isolated hn0 S C).card) ≤ 2*(L d)^n*(t d)^B.card at env
  have hL : 1≤L d := by unfold L; linarith [Real.sqrt_nonneg (q d)]
  have ht : 0≤t d := by
    unfold t
    have : 1/(4*L d) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  have ht' : t d≤1 := by
    unfold t
    have ht0 : 0≤1/(4*L d) := by positivity
    linarith
  calc
    _ ≤ ∑ S ∈ A, q d^runs S*(1/q d)^(isolated hn0 S C).card :=
      Finset.sum_le_sum (fun S h => mask_bound hn (by omega) H a C marksB S (Finset.ne_of_mem_erase h))
    _ ≤ ∑ S : Finset (Fin n), q d^runs S*(1/q d)^(isolated hn0 S C).card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => mul_nonneg (pow_nonneg (q_nn _) _) (pow_nonneg (div_nonneg zero_le_one (q_nn _)) _))
    _ ≤ _ := env
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht ht' (by omega : w/2 ≤ B.card)) (by positivity)

end Join

namespace Join

open Classical in
noncomputable def chars (d m : ℕ) := (Finset.univ : Finset (Fin d × Fin m → F)).erase 0

lemma num_chars (d m : ℕ) : ((chars d m).card:ℝ) = M m d-1 := by
  classical
  have hh : (chars d m).card=2^(m*d)-1 := by simp [chars,Finset.card_erase_of_mem,ZMod.card,Nat.mul_comm]
  rw [hh,q_cast]
  rfl

lemma error_le {n m d : ℕ} (H : Fin n → V m) (S : Finset (Fin n)) (hs : S≠Finset.univ) :
    |M m d*(Census.B d:ℝ)*(Census.cells d H S:ℝ)-(q d)^runs S| ≤
      (∑ a ∈ chars d m, |(Census.bias H a S : ℝ)|) + M m d*(Census.dep d H S:ℝ) := by
  classical
  have id' : (2:ℝ)^(m*d)*((Census.B d:ℝ)*(Census.cells d H S:ℝ)+(Census.dep d H S:ℝ)) =
      ((Census.words d S).card:ℝ) + ∑ a∈chars d m, (Census.bias H a S:ℝ) := by
    exact_mod_cast Census.signed_census d H S
  rw [word_card S hs,Nat.cast_pow,q_cast] at id'
  have id : M m d*(Census.B d:ℝ)*(Census.cells d H S:ℝ)-(q d)^runs S =
      (∑ a∈chars d m, (Census.bias H a S:ℝ)) - M m d*(Census.dep d H S:ℝ) := by
    unfold M; linear_combination id'
  rw [id]
  let z := ∑ a∈chars d m, (Census.bias H a S:ℝ)
  let e := M m d*(Census.dep d H S:ℝ)
  have he : 0 ≤ e := by dsimp [e,M]; positivity
  calc
    |z-e| ≤ |z|+|e| := by simpa [sub_eq_add_neg] using abs_add_le z (-e)
    _ ≤ _ := by rw [abs_of_nonneg he]; exact add_le_add_left (Finset.abs_sum_le_sum_abs _ _) _

lemma full_error {n m d : ℕ} (hn : 0<n) (hd : 2≤d) (H : Fin n → V m) :
    |M m d*(Census.B d:ℝ)*(Census.cells d H Finset.univ:ℝ)-(q d)^runs (Finset.univ : Finset (Fin n))| = 1 := by
  classical
  have cell : Census.cells d H Finset.univ=0 := by
    unfold Census.cells
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro U hu
    obtain ⟨_,hg,hfull⟩ := Finset.mem_filter.mp hu
    have r := SupportGeometry.full_finrank_le_one hn U hg.2.2 hfull
    change Module.finrank Census.field U ≤ 1 at r
    have rk := hg.1
    omega
  simp [cell,runs]

end Join

namespace Join

noncomputable def proper (n : ℕ) := (Finset.univ : Finset (Finset (Fin n))).erase Finset.univ
noncomputable def err {n m : ℕ} (d : ℕ) (H : Fin n → V m) (S : Finset (Fin n)) :=
  |M m d*(Census.B d:ℝ)*(Census.cells d H S:ℝ)-(q d)^runs S|
noncomputable def biasAbs {n m d : ℕ} (H : Fin n → V m) (a : Fin d × Fin m → F) (S : Finset (Fin n)) :=
  |(Census.bias H a S:ℝ)|
noncomputable def mass {n m : ℕ} (d : ℕ) (H : Fin n → V m) (S : Finset (Fin n)) : ℝ := Census.dep d H S

lemma combine_local {n m d : ℕ} (H : Fin n → V m) :
    ∑ S ∈ proper n, err d H S ≤
      (∑ a∈chars d m, ∑ S∈proper n, biasAbs H a S) + M m d*(∑ S∈proper n,mass d H S) := by
  calc
    _ ≤ ∑ S ∈ proper n, ((∑ a∈chars d m, biasAbs H a S) + M m d*mass d H S) :=
      Finset.sum_le_sum (fun S h => error_le H S (Finset.ne_of_mem_erase h))
    _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_comm,Finset.mul_sum]

lemma combine_bias {n m d w : ℕ} (hn : 3≤n) (hd : 2≤d) (H : Fin n → V m)
    (hw : ∀ a : V m, a ≠ 0 → w ≤ (Finset.univ.filter (fun i : Fin n => (∑ b,a b*H i b) ≠ 0)).card) :
    (∑ a∈chars d m, ∑ S∈proper n, biasAbs H a S) ≤ (M m d-1)*(2*(L d)^n*(t d)^(w/2)) := by
  calc
    _ ≤ ∑ _a∈chars d m, 2*(L d)^n*(t d)^(w/2) := Finset.sum_le_sum (fun a ha => bias_sum (w:=w) (m:=m) (n:=n) (d:=d) (by omega) hd H hw a (Finset.ne_of_mem_erase ha))
    _ = _ := by simp [num_chars]

lemma total_bound {n m d w : ℕ} (hn : 3≤n) (hd : 2≤d) (H : Fin n → V m)
    (hw : ∀ a : V m, a ≠ 0 → w ≤ (Finset.univ.filter (fun i : Fin n => (∑ b,a b*H i b) ≠ 0)).card) :
    (∑ S : Finset (Fin n), err d H S) ≤
     1+2*(M m d-1)*(L d)^n*(t d)^(w/2)+2*M m d*q d*(L (d-1))^n := by
  have hM : 0 ≤ M m d := by unfold M; positivity
  have hd' : (∑ S∈proper n,mass d H S) ≤ 2*q d*(L (d-1))^n := dep_sum (by omega) H
  have pr := (combine_local (d:=d) H).trans (add_le_add (combine_bias hn hd H hw) (mul_le_mul_of_nonneg_left hd' hM))
  have f : err d H Finset.univ=1 := full_error (by omega) hd H
  have split := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin n))) (err d H) (Finset.mem_univ Finset.univ)
  change (∑ S∈proper n,err d H S)+err d H Finset.univ=∑ S,err d H S at split
  rw [←split,f]
  calc
    _ ≤ ((M m d-1)*(2*(L d)^n*(t d)^(w/2))+M m d*(2*q d*(L (d-1))^n))+1 := add_le_add pr le_rfl
    _ = _ := by ring

end Join

end PEqualNP.Outside.L_lib_926_aux

theorem PEqualNP.Outside.L_lib_926 : (∀ (n m d w : ℕ), 3 ≤ n → 2 ≤ d →
  ∀ H : Fin n → Fin m → ZMod 2,
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let W := Fin n → F
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  let next := fun i : Fin n =>
    (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
  let runs := fun S : Finset (Fin n) => (S.filter (fun i => next i ∉ S)).card
  let supp := fun U : Submodule F W =>
    Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
  let good := fun U : Submodule F W =>
    Module.finrank F U = d ∧
    (∀ x ∈ U, ∀ b : Fin m, (∑ i, H i b * x i) = 0) ∧
    (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
  let cells := fun S : Finset (Fin n) =>
    (Finset.univ.filter (fun U : Submodule F W => good U ∧ supp U = S)).card
  let B := ∏ i ∈ Finset.range d, (2^d-2^i : ℕ)
  let q := (2 : ℝ)^d-1
  let L := 1 + Real.sqrt q
  let Lprev := 1 + Real.sqrt ((2 : ℝ)^(d-1)-1)
  let M := (2 : ℝ)^(m*d)
  (∀ a : Fin m → F, a ≠ 0 →
    w ≤ (Finset.univ.filter (fun i : Fin n => (∑ b, a b * H i b) ≠ 0)).card) →
  (∑ S : Finset (Fin n), |M * (B : ℝ) * (cells S : ℝ) - q^(runs S)|) ≤
    1 + 2*(M-1)*L^n*(1-1/(4*L))^(w/2) + 2*M*q*Lprev^n) := by
  intro n m d w hn hd H F W N runs supp good cells B q L Lprev M hw
  classical
  have hw' : ∀ a : PEqualNP.Outside.L_lib_926_aux.V m, a ≠ 0 →
      w ≤ (Finset.univ.filter (fun i : Fin n => (∑ b, a b * H i b) ≠ 0)).card := by
    intro a ha
    convert! hw a ha using 1 <;> congr! 5
  have hsupp (U : Submodule F W) : supp U = PEqualNP.Outside.L_lib_926_aux.SupportGeometry.support U := by
    ext i
    simp only [supp,PEqualNP.Outside.L_lib_926_aux.SupportGeometry.support,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor <;> rintro ⟨x,hx,hi⟩ <;> exact ⟨x,hx,hi⟩
  have hc (S : Finset (Fin n)) : cells S = PEqualNP.Outside.L_lib_926_aux.Census.cells d H S := by
    apply congrArg Finset.card
    ext U
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hsupp]
    rfl
  have hr (S : Finset (Fin n)) : runs S = PEqualNP.Outside.L_lib_926_aux.Join.runs S := by
    apply congrArg Finset.card
    congr! 4
  have he (S : Finset (Fin n)) : |M*(B:ℝ)*(cells S:ℝ)-q^runs S| = PEqualNP.Outside.L_lib_926_aux.Join.err d H S := by
    rw [hc,hr]
    rfl
  calc
    _ = ∑ S, PEqualNP.Outside.L_lib_926_aux.Join.err d H S := Finset.sum_congr rfl (fun S _ => he S)
    _ ≤ _ := PEqualNP.Outside.L_lib_926_aux.Join.total_bound hn hd H hw'
