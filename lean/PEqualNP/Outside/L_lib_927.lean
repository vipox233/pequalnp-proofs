import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_927_aux

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

open PEqualNP.Outside.L_lib_927_aux.SupportGeometry

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

noncomputable def cellsSet {n m : ℕ} (d : ℕ) (H : Fin n → V m) (S : Finset (Fin n)) :
    Finset (Submodule field (V n)) := by
  classical
  letI : Fintype (Submodule field (V n)) := Fintype.ofFinite _
  exact Finset.univ.filter (fun U : Submodule field (V n) => Good d H U ∧ support U=S)

lemma mem_cellsSet {n m : ℕ} (d : ℕ) (H : Fin n → V m) (S : Finset (Fin n)) (U : Submodule field (V n)) :
    U ∈ cellsSet d H S ↔ Good d H U ∧ support U = S := by
  classical
  simp [cellsSet]

noncomputable def cells {n m : ℕ} (d : ℕ) (H : Fin n → V m) (S : Finset (Fin n)) : ℕ :=
  (cellsSet d H S).card

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

open PEqualNP.Outside.L_lib_927_aux.Harmonic

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
    unfold Census.cells Census.cellsSet
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


namespace DualWeight
open SupportGeometry (F)

def hCode (t : ℕ) (i : Fin (6 * t)) (b : Fin 4) : F :=
  if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
  then (1 : F) else 0

lemma h2a_aux (x y : F) (hxy : x ≠ 0 ∨ y ≠ 0) :
    2 ≤ (Finset.univ.filter fun r : Fin 3 =>
      (if r.val = 0 then x else if r.val = 1 then y else x + y) ≠ 0).card := by
  classical
  fin_cases x <;> fin_cases y
  · exfalso; exact Or.elim hxy (fun h => h rfl) (fun h => h rfl)
  · have hsub : ({1, 2} : Finset (Fin 3)) ⊆ Finset.univ.filter fun r : Fin 3 =>
        (if r.val = 0 then (0 : F) else if r.val = 1 then 1 else 0 + 1) ≠ 0 := by
      intro r hr; fin_cases r <;> simp_all
    exact le_trans (by decide : 2 ≤ ({1, 2} : Finset (Fin 3)).card) (Finset.card_le_card hsub)
  · have hsub : ({0, 2} : Finset (Fin 3)) ⊆ Finset.univ.filter fun r : Fin 3 =>
        (if r.val = 0 then (1 : F) else if r.val = 1 then 0 else 1 + 0) ≠ 0 := by
      intro r hr; fin_cases r <;> simp_all
    exact le_trans (by decide : 2 ≤ ({0, 2} : Finset (Fin 3)).card) (Finset.card_le_card hsub)
  · have hsub : ({0, 1} : Finset (Fin 3)) ⊆ Finset.univ.filter fun r : Fin 3 =>
        (if r.val = 0 then (1 : F) else if r.val = 1 then 1 else (1 : F) + 1) ≠ 0 := by
      intro r hr; fin_cases r <;> simp_all
    exact le_trans (by decide : 2 ≤ ({0, 1} : Finset (Fin 3)).card) (Finset.card_le_card hsub)

lemma hCode_weight (t : ℕ) (a : Fin 4 → F) (ha : a ≠ 0) :
    2 * t ≤ (Finset.univ.filter (fun i : Fin (6 * t) => (∑ b : Fin 4, a b * hCode t i b) ≠ 0)).card := by
  have hcases : (a 0 ≠ 0 ∨ a 1 ≠ 0) ∨ (a 2 ≠ 0 ∨ a 3 ≠ 0) := by
    by_contra h
    apply ha
    funext b
    fin_cases b <;> simp_all
  let p : ℕ := if a 0 ≠ 0 ∨ a 1 ≠ 0 then 0 else 1
  let idx (k : Fin t) (r : Fin 3) : Fin (6 * t) :=
    ⟨6 * k.val + 2 * r.val + p, by have := k.isLt; have := r.isLt; dsimp [p]; split_ifs <;> omega⟩
  have idx_inj : ∀ k₁ r₁ k₂ r₂, idx k₁ r₁ = idx k₂ r₂ → k₁ = k₂ ∧ r₁ = r₂ := by
    intro k₁ r₁ k₂ r₂ h
    have hv := congrArg Fin.val h
    change 6 * k₁.val + 2 * r₁.val + p = 6 * k₂.val + 2 * r₂.val + p at hv
    have hr1 := r₁.isLt; have hr2 := r₂.isLt
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  let hits (k : Fin t) : Finset (Fin (6 * t)) :=
    (Finset.univ.filter fun r : Fin 3 => (∑ b : Fin 4, a b * hCode t (idx k r) b) ≠ 0).image (idx k)
  have hsub : Finset.univ.biUnion hits ⊆
      Finset.univ.filter (fun i : Fin (6 * t) => (∑ b : Fin 4, a b * hCode t i b) ≠ 0) := by
    intro i hi
    rcases Finset.mem_biUnion.mp hi with ⟨k, _, hki⟩
    rcases Finset.mem_image.mp hki with ⟨r, hr, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2⟩
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin t)) hits := by
    intro k₁ _ k₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    rcases Finset.mem_image.mp hi₁ with ⟨r₁, _, rfl⟩
    rcases Finset.mem_image.mp hi₂ with ⟨r₂, _, heq⟩
    exact hne (idx_inj k₂ r₂ k₁ r₁ heq).1.symm
  have hcard (k : Fin t) : 2 ≤ (hits k).card := by
    rw [Finset.card_image_of_injective _ (fun r₁ r₂ h => (idx_inj k r₁ k r₂ h).2)]
    have hsum (r : Fin 3) : (∑ b : Fin 4, a b * hCode t (idx k r) b) =
        if p = 0 then (if r.val = 0 then a 0 else if r.val = 1 then a 1 else a 0 + a 1)
        else (if r.val = 0 then a 2 else if r.val = 1 then a 3 else a 2 + a 3) := by
      have hm1 : (idx k r).val % 2 = p := by
        change (6 * k.val + 2 * r.val + p) % 2 = p
        dsimp [p]; split_ifs <;> omega
      have hm2 : (idx k r).val / 2 % 3 = r.val := by
        have := r.isLt
        change (6 * k.val + 2 * r.val + p) / 2 % 3 = r.val
        dsimp [p]; split_ifs <;> omega
      rw [Fin.sum_univ_four]
      dsimp [hCode]
      rw [hm1, hm2]
      by_cases hp0 : p = 0
      · rw [hp0]; fin_cases r <;> simp
      · have hp1 : p = 1 := by dsimp [p] at hp0 ⊢; split_ifs at hp0 ⊢ <;> omega
        rw [hp1]; fin_cases r <;> simp
    by_cases h01 : a 0 ≠ 0 ∨ a 1 ≠ 0
    · have hp0 : p = 0 := if_pos h01
      simpa only [hsum, hp0, ↓reduceIte] using h2a_aux (a 0) (a 1) h01
    · have hp1 : p = 1 := if_neg h01
      have h23 : a 2 ≠ 0 ∨ a 3 ≠ 0 := by tauto
      simpa only [hsum, hp1, one_ne_zero, ↓reduceIte] using h2a_aux (a 2) (a 3) h23
  calc
    2 * t = ∑ _k : Fin t, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ k : Fin t, (hits k).card := Finset.sum_le_sum fun k _ => hcard k
    _ = (Finset.univ.biUnion hits).card := by
      rw [Finset.card_biUnion (fun k₁ hk₁ k₂ hk₂ hne => hdisj hk₁ hk₂ hne)]
    _ ≤ _ := Finset.card_le_card hsub

end DualWeight


namespace HostDim
open SupportGeometry

def prev {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

lemma prev_next {n : ℕ} (i : Fin n) : prev (next i) = i := by
  apply Fin.ext
  have hn : 0 < n := (Nat.zero_le _).trans_lt i.isLt
  have hi := i.isLt
  change ((i.val + 1) % n + n - 1) % n = i.val
  by_cases h : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt h, show i.val + 1 + n - 1 = n + i.val by omega, Nat.add_mod_left, Nat.mod_eq_of_lt hi]
  · have he : i.val + 1 = n := by omega
    rw [he, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    omega

lemma next_prev {n : ℕ} (i : Fin n) : next (prev i) = i := by
  apply Fin.ext
  have hi := i.isLt
  have hn : 0 < n := (Nat.zero_le _).trans_lt hi
  change ((i.val + n - 1) % n + 1) % n = i.val
  by_cases h : i.val = 0
  · rw [h, Nat.zero_add, Nat.mod_eq_of_lt (by omega : n - 1 < n),
      show n - 1 + 1 = n by omega, Nat.mod_self]
  · have hlt : i.val - 1 < n := by omega
    rw [show i.val + n - 1 = n + (i.val - 1) by omega, Nat.add_mod_left, Nat.mod_eq_of_lt hlt,
      show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt hi]

lemma prev_inj {n : ℕ} : Function.Injective (@prev n) :=
  fun x y h => by rw [← next_prev x, ← next_prev y, h]

lemma next_inj {n : ℕ} : Function.Injective (@next n) :=
  fun x y h => by rw [← prev_next x, ← prev_next y, h]

lemma prev_next_iter {n : ℕ} (k : ℕ) (i : Fin n) : prev^[k] (next^[k] i) = i := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply', prev_next, ih]

lemma prev_reaches {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (j : Fin n) :
    ∃ k : ℕ, prev^[k] j ∈ S := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨k, hk⟩ := all_if_forward (fun u => ∃ k : ℕ, next^[k] s = u) s ⟨0, rfl⟩
    (fun u ⟨k, hk⟩ => ⟨k + 1, by rw [Function.iterate_succ_apply', hk]⟩) j
  refine ⟨k, ?_⟩
  rw [← hk, prev_next_iter]
  exact hs

noncomputable def zdist {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (j : Fin n) : ℕ :=
  Nat.find (prev_reaches S hS j)

lemma zdist_spec {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (j : Fin n) :
    prev^[zdist S hS j] j ∈ S := by
  classical
  exact Nat.find_spec (prev_reaches S hS j)

lemma zdist_lt {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) {j : Fin n} {k : ℕ}
    (hk : k < zdist S hS j) : prev^[k] j ∉ S := by
  classical
  exact Nat.find_min (prev_reaches S hS j) hk

lemma zdist_eq_zero {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (j : Fin n) :
    zdist S hS j = 0 ↔ j ∈ S := by
  classical
  constructor
  · intro h; simpa [h] using zdist_spec S hS j
  · intro hj; exact Nat.eq_zero_of_le_zero (Nat.find_min' (prev_reaches S hS j) hj)

lemma zdist_step {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) {j : Fin n} (hj : j ∉ S) :
    zdist S hS j = zdist S hS (prev j) + 1 := by
  classical
  have hpos : 0 < zdist S hS j := by
    by_contra! h
    exact hj ((zdist_eq_zero S hS j).mp (Nat.eq_zero_of_le_zero h))
  have h1 : prev^[zdist S hS j - 1] (prev j) ∈ S := by
    rw [← Function.iterate_succ_apply, show (zdist S hS j - 1).succ = zdist S hS j by omega]
    exact zdist_spec S hS j
  have hl : zdist S hS (prev j) ≤ zdist S hS j - 1 := Nat.find_min' (prev_reaches S hS (prev j)) h1
  have hr : zdist S hS j ≤ zdist S hS (prev j) + 1 := Nat.find_min' (prev_reaches S hS j) (by
    rw [Function.iterate_succ_apply]; exact zdist_spec S hS (prev j))
  omega

noncomputable def oddZSet {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j => j ∉ S ∧ zdist S hS j % 2 = 1

lemma runs_le_oddZSet {n : ℕ} (S T : Finset (Fin n)) (hS : S.Nonempty)
    (hST : S ⊆ T) (hT : T ≠ Finset.univ) : Join.runs T ≤ (oddZSet S hS).card := by
  classical
  let W := (T.filter fun i => next i ∉ T).image next
  have hWcard : W.card = Join.runs T :=
    Finset.card_image_of_injective _ next_inj
  have hWout : ∀ w ∈ W, w ∉ T := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
    exact (Finset.mem_filter.mp hu).2
  have hWnoAdj : ∀ w ∈ W, next w ∉ W := by
    intro w hw hnw
    rcases Finset.mem_image.mp hnw with ⟨v, hv, heq⟩
    have hv' : v = w := next_inj heq
    rw [hv'] at hv
    exact hWout w hw (Finset.mem_filter.mp hv).1
  let f : Fin n → Fin n := fun w => if zdist S hS w % 2 = 1 then w else prev w
  have hfMem : ∀ w ∈ W, f w ∈ oddZSet S hS := by
    intro w hw
    have hwS : w ∉ S := fun h => hWout w hw (hST h)
    dsimp only [f]
    split_ifs with hodd
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwS, hodd⟩
    · have hpos : 0 < zdist S hS w := by
        by_contra! h0
        exact hwS ((zdist_eq_zero S hS w).mp (Nat.eq_zero_of_le_zero h0))
      have hge2 : 2 ≤ zdist S hS w := by omega
      have hprevS : prev w ∉ S := by
        intro hp
        have := zdist_step S hS hwS
        rw [(zdist_eq_zero S hS (prev w)).mpr hp] at this
        omega
      have hstep := zdist_step S hS hwS
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprevS, by omega⟩
  have hfInj : Set.InjOn f (W : Set (Fin n)) := by
    intro w₁ hw₁ w₂ hw₂ heq
    dsimp only [f] at heq
    split_ifs at heq with h₁ h₂
    · exact heq
    · have : w₂ = next w₁ := by rw [heq, next_prev]
      exact absurd (this ▸ hw₂) (hWnoAdj w₁ hw₁)
    · have : w₁ = next w₂ := by rw [← heq, next_prev]
      exact absurd (this ▸ hw₁) (hWnoAdj w₂ hw₂)
    · exact prev_inj heq
  rw [← hWcard]
  exact Finset.card_le_card_of_injOn f hfMem hfInj

noncomputable def Tstar {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) : Finset (Fin n) := by
  classical
  exact S ∪ Finset.univ.filter fun j => j ∉ S ∧ next j ∉ S ∧ zdist S hS j % 2 = 0

lemma Tstar_ne_univ {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (hSne : S ≠ Finset.univ) :
    Tstar S hS ≠ Finset.univ := by
  classical
  have ⟨s, hs⟩ := hS
  let k := Nat.find (Join.reach S hSne s)
  have hk : next^[k] s ∉ S := Nat.find_spec (Join.reach S hSne s)
  have hkpos : 0 < k := by
    by_contra! h0
    have : k = 0 := by omega
    rw [this] at hk
    exact hk hs
  let e := next^[k - 1] s
  have he : e ∈ S := by
    by_contra he'
    exact Nat.find_min (Join.reach S hSne s) (by omega : k - 1 < k) he'
  have hne : next e ∉ S := by
    change next (next^[k - 1] s) ∉ S
    rw [← Function.iterate_succ_apply' next (k - 1) s, show (k - 1).succ = k by omega]
    exact hk
  have hz : zdist S hS (next e) = 1 := by
    rw [zdist_step S hS hne, prev_next, (zdist_eq_zero S hS e).mpr he]
  intro hEq
  have hmem : next e ∈ Tstar S hS := hEq ▸ Finset.mem_univ _
  rcases Finset.mem_union.mp hmem with h1 | h2
  · exact hne h1
  · have hz0 := (Finset.mem_filter.mp h2).2.2.2
    rw [hz] at hz0
    omega

lemma ends_Tstar_card {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Join.runs (Tstar S hS) = (oddZSet S hS).card := by
  classical
  apply Finset.card_bij (fun i _ => next i)
  · intro i hi
    obtain ⟨hiT, hniT⟩ := Finset.mem_filter.mp hi
    have hniS : next i ∉ S := fun h => hniT (Finset.mem_union_left _ h)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hniS, ?_⟩
    by_contra hnot
    have hzd : zdist S hS (next i) % 2 = 0 := by omega
    have hpos : 0 < zdist S hS (next i) := by
      by_contra! h0; exact hniS ((zdist_eq_zero S hS (next i)).mp (Nat.eq_zero_of_le_zero h0))
    have hiS : i ∉ S := by
      intro hiS
      have := zdist_step S hS hniS
      rw [prev_next, (zdist_eq_zero S hS i).mpr hiS] at this
      omega
    rcases Finset.mem_union.mp hiT with h | h
    · exact hiS h
    · have hst := zdist_step S hS hniS
      rw [prev_next] at hst
      have := (Finset.mem_filter.mp h).2.2.2
      omega
  · intro _ _ _ _ h; exact next_inj h
  · intro j hj
    obtain ⟨_, hjS, hjodd⟩ := Finset.mem_filter.mp hj
    refine ⟨prev j, Finset.mem_filter.mpr ⟨?_, ?_⟩, next_prev j⟩
    · by_cases hpS : prev j ∈ S
      · exact Finset.mem_union_left _ hpS
      · have hst := zdist_step S hS hjS
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hpS, by rw [next_prev]; exact hjS, by omega⟩)
    · rw [next_prev]
      intro hjT
      rcases Finset.mem_union.mp hjT with h | h
      · exact hjS h
      · have := (Finset.mem_filter.mp h).2.2.2
        omega

noncomputable def Vstar {n : ℕ} (T : Finset (Fin n)) : Submodule F (Space n) where
  carrier := {x : Space n | (∀ i ∉ T, x i = 0) ∧ (∀ i ∈ T, next i ∈ T → x i = x (next i))}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩; add_mem' := by
    intro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun i hi => by simp [hx1 i hi, hy1 i hi], fun i hi hni => by simp [hx2 i hi hni, hy2 i hi hni]⟩
  smul_mem' := by
    intro c x ⟨hx1, hx2⟩
    refine ⟨fun i hi => by simp [hx1 i hi], fun i hi hni => by simp [hx2 i hi hni]⟩

lemma Vstar_adjacent {n : ℕ} (T : Finset (Fin n)) : adjacent (Vstar T) := by
  intro x hx y hy i
  by_cases hi : i ∈ T
  · by_cases hni : next i ∈ T
    · rw [hx.2 i hi hni, hy.2 i hi hni]
    · simp [hx.1 _ hni, hy.1 _ hni]
  · simp [hx.1 i hi, hy.1 i hi]

lemma Vstar_finrank {n : ℕ} (T : Finset (Fin n)) (hT : T ≠ Finset.univ) :
    Module.finrank F (Vstar T) = Join.runs T := by
  classical
  have ht := Join.reach T hT
  let toFun : Vstar T →ₗ[F] (EndSite next T → F) :=
    { toFun := fun x j => x.1 j.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let invFun : (EndSite next T → F) → Vstar T := fun y =>
    ⟨fun i => if hi : i ∈ T then y ⟨finish next T ht i, finish_end next T ht hi⟩ else 0,
     fun i hi => by simp [hi],
     fun i hi hni => by
       have H : (⟨finish next T ht i, finish_end next T ht hi⟩ : EndSite next T) =
           ⟨finish next T ht (next i), finish_end next T ht hni⟩ :=
         Subtype.ext (finish_next next T ht hi hni)
       simp [hi, hni, H]⟩
  have e : Vstar T ≃ₗ[F] (EndSite next T → F) :=
    { toFun := toFun
      invFun := invFun
      left_inv := fun x => by
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ T
        · simp only [invFun, toFun, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_left hi]
          exact (constant_to_end next T ht x.1 x.2.2 hi).symm
        · simp only [invFun, toFun, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_right hi]
          exact (x.2.1 i hi).symm
      right_inv := fun y => by
        funext j
        have H : (⟨finish next T ht j.1, finish_end next T ht j.2.1⟩ : EndSite next T) = j :=
          Subtype.ext (finish_last next T ht j.2.1 j.2.2)
        simp [toFun, invFun, j.2.1, H]
      map_add' := toFun.map_add'
      map_smul' := toFun.map_smul' }
  rw [LinearEquiv.finrank_eq e, Module.finrank_fintype_fun_eq_card]
  rw [← Nat.card_eq_fintype_card]
  exact Join.ends_card T

lemma U_le_Vstar {n : ℕ} (U : Submodule F (Space n)) (hU : adjacent U) (hS : (support U).Nonempty) :
    U ≤ Vstar (Tstar (support U) hS) := by
  intro x hx
  let S := support U
  refine ⟨fun i hi => ?_, fun i hi hni => ?_⟩
  · have hiS : i ∉ S := fun h => hi (Finset.mem_union_left _ h)
    by_contra hne
    exact hiS ((mem_support U i).mpr ⟨x, hx, hne⟩)
  · have vanish (u : Fin n) (hu : u ∉ S) : x u = 0 := by
      by_contra hne; exact hu ((mem_support U u).mpr ⟨x, hx, hne⟩)
    by_cases hiS : i ∈ S
    · have hniS : next i ∈ S := by
        by_contra hniS
        have hz : zdist S hS (next i) = 1 := by
          rw [zdist_step S hS hniS, prev_next, (zdist_eq_zero S hS i).mpr hiS]
        rcases Finset.mem_union.mp hni with h | h
        · exact hniS h
        · have hz0 := (Finset.mem_filter.mp h).2.2.2
          rw [hz] at hz0
          omega
      exact constant_on_pair hU hiS hniS hx
    · have hniS : next i ∉ S := by
        rcases Finset.mem_union.mp hi with h | h
        · exact absurd h hiS
        · exact (Finset.mem_filter.mp h).2.2.1
      rw [vanish i hiS, vanish (next i) hniS]

open Classical in
lemma host_bounds {n m d : ℕ} (hm : m = 4) (hd : 2 ≤ d) (H : Fin n → Space m)
    (U : Submodule F (Space n)) (hU : Census.Good d H U) (hS : (support U).Nonempty) :
    let S := support U
    let spaces := (Finset.univ : Finset (Submodule F (Space n))).filter
      (fun E => (∀ x ∈ E, ∀ b : Fin m, (∑ i, H i b * x i) = 0) ∧ adjacent E)
    (oddZSet S hS).card - 4 ≤
      (spaces.filter (fun E => U ≤ E)).sup (fun E => Module.finrank F E) ∧
    (spaces.filter (fun E => U ≤ E)).sup (fun E => Module.finrank F E) ≤
      (oddZSet S hS).card := by
  classical
  subst hm
  dsimp only
  let S := support U
  have hUd : Module.finrank F U = d := hU.1
  have hn : 0 < n := by obtain ⟨s, hs⟩ := hS; exact (Nat.zero_le _).trans_lt s.isLt
  have hSne : S ≠ Finset.univ := by
    intro hfull
    have r : Module.finrank F U ≤ 1 := full_finrank_le_one hn U hU.2.2 hfull
    omega
  constructor
  · let T := Tstar S hS
    have hTne : T ≠ Finset.univ := Tstar_ne_univ S hS hSne
    let checkMap : Space n →ₗ[F] (Fin 4 → F) :=
      { toFun := fun x b => ∑ i, H i b * x i
        map_add' := fun x y => by ext b; simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun c x => by ext b; simp [Finset.mul_sum, mul_left_comm] }
    let res := checkMap.domRestrict (Vstar T)
    let E : Submodule F (Space n) := Vstar T ⊓ LinearMap.ker checkMap
    have hUE : U ≤ E := le_inf (U_le_Vstar U hU.2.2 hS) (fun x hx => by ext b; exact hU.2.1 x hx b)
    have hEgood : (∀ x ∈ E, ∀ b : Fin 4, (∑ i, H i b * x i) = 0) ∧ adjacent E := by
      refine ⟨fun x hx b => ?_, fun x hx y hy i => Vstar_adjacent T x hx.1 y hy.1 i⟩
      exact congrFun hx.2 b
    have hEmem : E ∈ ((Finset.univ : Finset (Submodule F (Space n))).filter
        (fun E => (∀ x ∈ E, ∀ b : Fin 4, (∑ i, H i b * x i) = 0) ∧ adjacent E)).filter (fun E => U ≤ E) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEgood⟩, hUE⟩
    have hker : E = (LinearMap.ker res).map (Vstar T).subtype := by
      ext x
      simp only [E, res, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_map,
        LinearMap.domRestrict_apply, Submodule.coe_subtype]
      constructor
      · rintro ⟨hxV, hxk⟩
        exact ⟨⟨x, hxV⟩, hxk, rfl⟩
      · rintro ⟨⟨y, hyV⟩, hyk, rfl⟩
        exact ⟨hyV, hyk⟩
    have hdimE : Module.finrank F E = Module.finrank F (LinearMap.ker res) := by
      rw [hker]
      exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (Vstar T).subtype (Submodule.injective_subtype _) _).symm
    have hrk := LinearMap.finrank_range_add_finrank_ker res
    have hrng : Module.finrank F (LinearMap.range res) ≤ 4 := by
      have hle := Submodule.finrank_le (LinearMap.range res)
      simpa [Module.finrank_fintype_fun_eq_card] using hle
    have hVdim : Module.finrank F (Vstar T) = (oddZSet S hS).card := by
      rw [Vstar_finrank T hTne, ends_Tstar_card S hS]
    have hle : (oddZSet S hS).card - 4 ≤ Module.finrank F E := by omega
    exact hle.trans (Finset.le_sup (f := fun (E : Submodule F (Space n)) => Module.finrank F E) hEmem)
  · apply Finset.sup_le
    intro E hE
    obtain ⟨hE1, hUE⟩ := Finset.mem_filter.mp hE
    obtain ⟨_, hEgood⟩ := Finset.mem_filter.mp hE1
    have hST : S ⊆ support E := by
      intro i hi
      obtain ⟨x, hxU, hxi⟩ := (mem_support U i).mp hi
      exact (mem_support E i).mpr ⟨x, hUE hxU, hxi⟩
    have hTne : support E ≠ Finset.univ := by
      intro hfull
      have r : Module.finrank F E ≤ 1 := full_finrank_le_one hn E hEgood.2 hfull
      have rd : d ≤ Module.finrank F E := by
        rw [← hUd]
        exact Submodule.finrank_mono hUE
      omega
    exact (finrank_le_runs E hEgood.2 hTne).trans (runs_le_oddZSet S (support E) hS hST hTne)

lemma filter_card_congr {α : Type*} (s : Finset α) (p : α → Prop)
    (d1 d2 : DecidablePred p) :
    (@Finset.filter α p d1 s).card = (@Finset.filter α p d2 s).card :=
  congrArg Finset.card (Finset.ext fun _ => by simp only [Finset.mem_filter])

open Classical in
lemma host_bounds_pred {n d : ℕ} (hd : 2 ≤ d) (H : Fin n → Space 4)
    (U : Submodule F (Space n)) (hU : Census.Good d H U) (hS : (support U).Nonempty)
    (sp : Finset (Submodule F (Space n)))
    (hsp : ∀ E, E ∈ sp ↔ (∀ x ∈ E, ∀ b : Fin 4, (∑ i, H i b * x i) = 0) ∧ adjacent E)
    (dUE : DecidablePred (fun E => U ≤ E)) :
    (oddZSet (support U) hS).card - 4 ≤
      (@Finset.filter _ (fun E => U ≤ E) dUE sp).sup (fun E => Module.finrank F E) ∧
    (@Finset.filter _ (fun E => U ≤ E) dUE sp).sup (fun E => Module.finrank F E) ≤
      (oddZSet (support U) hS).card := by
  have hbase := host_bounds (n := n) (m := 4) (d := d) rfl hd H U hU hS
  have heq : @Finset.filter _ (fun E => U ≤ E) dUE sp =
      @Finset.filter _ (fun E => U ≤ E) (fun E => Classical.propDecidable (U ≤ E))
        ((Finset.univ : Finset (Submodule F (Space n))).filter
          (fun E => (∀ x ∈ E, ∀ b : Fin 4, (∑ i, H i b * x i) = 0) ∧ adjacent E)) := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsp]
  rw [heq]
  exact hbase

end HostDim


namespace Transfer
open SupportGeometry (next)
open HostDim (prev prev_next next_prev prev_next_iter prev_inj next_inj zdist zdist_spec zdist_lt zdist_eq_zero zdist_step oddZSet)

def bit {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : Fin 2 :=
  if i ∈ S then 1 else 0

def bitEquiv (n : ℕ) : Finset (Fin n) ≃ (Fin n → Fin 2) where
  toFun := bit
  invFun x := Finset.univ.filter fun i => x i = 1
  left_inv S := by
    ext i
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, bit]
    by_cases h : i ∈ S <;> simp [h]
  right_inv x := by
    funext i
    simp only [bit, Finset.mem_filter, Finset.mem_univ, true_and]
    have hx : x i = 0 ∨ x i = 1 := by omega
    rcases hx with h | h <;> simp [h]

def A (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, r; r, 1]

lemma A_pow (r : ℝ) (k : ℕ) :
    A r ^ k = (1 / 2 : ℝ) •
      !![(1 + r) ^ k + (1 - r) ^ k, (1 + r) ^ k - (1 - r) ^ k;
         (1 + r) ^ k - (1 - r) ^ k, (1 + r) ^ k + (1 - r) ^ k] := by
  induction k with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> norm_num
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

noncomputable def wt {n : ℕ} (r : ℝ) (S : Finset (Fin n)) : ℝ :=
  ∏ i : Fin n, A r (bit S i) (bit S (next i))

lemma wt_eq_q_pow_runs {n d : ℕ} (hn : 1 < n) (S : Finset (Fin n)) :
    wt (Real.sqrt (Join.q d)) S = Join.q d ^ Join.runs S := by
  let r := Real.sqrt (Join.q d)
  have hnxt (u : Fin n) : next u = finRotate n u := (congrFun (Join.rot_eq hn) u).symm
  have he (i : Fin n) : A r (bit S i) (bit S (next i)) =
      if i ∈ boundary (finRotate n) S then r else 1 := by
    rw [hnxt i]
    by_cases h1 : i ∈ S <;> by_cases h2 : finRotate n i ∈ S <;> simp only [bit, h1, h2, ↓reduceIte]
    · have hb : i ∉ boundary (finRotate n) S := fun hm =>
        (Finset.mem_filter.mp hm).2 (iff_of_true h1 h2)
      rw [if_neg hb]; simp [A]
    · have hb : i ∈ boundary (finRotate n) S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => h2 (h.mp h1)⟩
      rw [if_pos hb]; simp [A]
    · have hb : i ∈ boundary (finRotate n) S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => h1 (h.mpr h2)⟩
      rw [if_pos hb]; simp [A]
    · have hb : i ∉ boundary (finRotate n) S := fun hm =>
        (Finset.mem_filter.mp hm).2 (iff_of_false h1 h2)
      rw [if_neg hb]; simp [A]
  rw [wt]
  refine (Finset.prod_congr rfl fun i _ => he i).trans ?_
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
  have hfin : (Finset.univ.filter fun x => x ∈ boundary (finRotate n) S) =
      boundary (finRotate n) S := by
    ext x
    rw [Finset.mem_filter]
    exact and_iff_right (Finset.mem_univ x)
  rw [hfin, boundary_card, Join.rot_eq hn, pow_mul, Real.sq_sqrt (Join.q_nn d)]
  unfold Join.runs
  congr 2

lemma path_sum {m : ℕ} : ∀ (M : Fin m → Matrix (Fin 2) (Fin 2) ℝ) (a b : Fin 2),
    (∑ x : Fin (m + 1) → Fin 2,
      if x 0 = a ∧ x (Fin.last m) = b then ∏ i : Fin m, M i (x i.castSucc) (x i.succ) else 0) =
      ((List.ofFn M).prod) a b := by
  induction m with
  | zero =>
    intro M a b
    have hc : (∑ x : Fin 1 → Fin 2, if x 0 = a ∧ x 0 = b then (1 : ℝ) else 0) =
        if a = b then 1 else 0 := by
      let e : (Fin 1 → Fin 2) ≃ Fin 2 := ⟨fun x => x 0, fun c _ => c,
        fun x => funext fun i => by rw [Fin.eq_zero i], fun _ => rfl⟩
      rw [← e.symm.sum_comp]
      change (∑ c : Fin 2, if c = a ∧ c = b then (1 : ℝ) else 0) = _
      split_ifs with hab
      · subst hab; rw [Finset.sum_eq_single a (fun c _ hc => by simp [hc]) (fun h => absurd (Finset.mem_univ _) h)]; simp
      · simp [hab]
    simpa [List.ofFn_zero, Matrix.one_apply] using hc
  | succ m ih =>
    intro M a b
    rw [List.ofFn_succ, List.prod_cons]
    let e : Fin 2 × (Fin (m + 1) → Fin 2) ≃ (Fin (m + 2) → Fin 2) :=
      Fin.consEquiv (fun _ : Fin (m + 2) => Fin 2)
    rw [← e.sum_comp, Fintype.sum_prod_type]
    have hsplit (c : Fin 2) (y : Fin (m + 1) → Fin 2) :
        (if e (c, y) 0 = a ∧ e (c, y) (Fin.last (m + 1)) = b then
          ∏ i : Fin (m + 1), M i (e (c, y) i.castSucc) (e (c, y) i.succ) else 0) =
        if c = a then M 0 c (y 0) *
          (if y (Fin.last m) = b then
            ∏ i : Fin m, M i.succ (y i.castSucc) (y i.succ) else 0) else 0 := by
      have hL : e (c, y) (Fin.last (m + 1)) = y (Fin.last m) := rfl
      have h0 : e (c, y) 0 = c := rfl
      have hp : (∏ i : Fin (m + 1), M i (e (c, y) i.castSucc) (e (c, y) i.succ)) =
          M 0 c (y 0) * ∏ i : Fin m, M i.succ (y i.castSucc) (y i.succ) := by
        rw [Fin.prod_univ_succ]
        rfl
      rw [h0, hL, hp]
      by_cases hca : c = a <;> by_cases hyb : y (Fin.last m) = b <;> simp [hca, hyb]
    simp_rw [hsplit]
    rw [Finset.sum_eq_single a (fun c _ hca => by simp [hca]) (fun h => absurd (Finset.mem_univ _) h)]
    simp only [↓reduceIte]
    have hpart (d : Fin 2) :
        (∑ y : Fin (m + 1) → Fin 2, if y 0 = d then M 0 a d *
          (if y (Fin.last m) = b then ∏ i : Fin m, M i.succ (y i.castSucc) (y i.succ) else 0) else 0) =
        M 0 a d * ((List.ofFn (fun i : Fin m => M i.succ)).prod d b) := by
      rw [← ih (fun i => M i.succ) d b, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy0 : y 0 = d <;> by_cases hyb : y (Fin.last m) = b <;> simp [hy0, hyb]
    have hgroup : (∑ y : Fin (m + 1) → Fin 2, M 0 a (y 0) *
        (if y (Fin.last m) = b then ∏ i : Fin m, M i.succ (y i.castSucc) (y i.succ) else 0)) =
        ∑ d : Fin 2, ∑ y : Fin (m + 1) → Fin 2, if y 0 = d then M 0 a d *
          (if y (Fin.last m) = b then ∏ i : Fin m, M i.succ (y i.castSucc) (y i.succ) else 0) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_eq_single (y 0) (fun d _ hd => by simp [hd.symm]) (fun h => absurd (Finset.mem_univ _) h)]
      simp
    rw [hgroup]
    simp_rw [hpart]
    rw [Matrix.mul_apply]

lemma cycle_sum {n : ℕ} (hn : 0 < n) (M : Fin n → Matrix (Fin 2) (Fin 2) ℝ) :
    (∑ x : Fin n → Fin 2, ∏ i : Fin n, M i (x i) (x (next i))) =
      ((List.ofFn M).prod).trace := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let ext (x : Fin (m + 1) → Fin 2) : Fin (m + 2) → Fin 2 :=
    Fin.snoc (α := fun _ => Fin 2) x (x 0)
  have hprod (x : Fin (m + 1) → Fin 2) :
      (∏ i : Fin (m + 1), M i (x i) (x (next i))) =
      ∏ i : Fin (m + 1), M i (ext x i.castSucc) (ext x i.succ) := by
    apply Finset.prod_congr rfl
    intro i _
    have h1 : ext x i.castSucc = x i := by dsimp [ext]; rw [Fin.snoc_castSucc]
    have h2 : ext x i.succ = x (next i) := by
      by_cases hi : i.val + 1 < m + 1
      · let j : Fin (m + 1) := ⟨i.val + 1, hi⟩
        have he1 : i.succ = j.castSucc := Fin.ext rfl
        have he2 : next i = j := Fin.ext (Nat.mod_eq_of_lt hi)
        rw [he1]
        change Fin.snoc (α := fun _ => Fin 2) x (x 0) j.castSucc = x (next i)
        rw [Fin.snoc_castSucc, he2]
      · have hil : i.val = m := by have := i.isLt; omega
        have he1 : i.succ = Fin.last (m + 1) := Fin.ext (by simp [hil])
        have he2 : next i = 0 := Fin.ext (by change (i.val + 1) % (m + 1) = 0; rw [hil, Nat.mod_self])
        rw [he1]
        change Fin.snoc (α := fun _ => Fin 2) x (x 0) (Fin.last (m + 1)) = x (next i)
        rw [Fin.snoc_last, he2]
    rw [h1, h2]
  have hsum_a (a : Fin 2) :
      (∑ x : Fin (m + 1) → Fin 2, if x 0 = a then ∏ i : Fin (m + 1), M i (x i) (x (next i)) else 0) =
      ((List.ofFn M).prod) a a := by
    rw [← path_sum M a a]
    let emb : (Fin (m + 1) → Fin 2) ↪ (Fin (m + 2) → Fin 2) :=
      ⟨ext, fun x y h => funext fun i => by
        have := congrFun h i.castSucc
        change ext x i.castSucc = ext y i.castSucc at this
        simpa [ext] using this⟩
    have hmem (y : Fin (m + 2) → Fin 2) (hy : y 0 = a ∧ y (Fin.last (m + 1)) = a) :
        y ∈ Finset.univ.map emb := by
      refine Finset.mem_map.mpr ⟨Fin.init y, Finset.mem_univ _, funext fun i => ?_⟩
      induction i using Fin.lastCases with
      | last =>
        change Fin.snoc (α := fun _ => Fin 2) (Fin.init y) (Fin.init y 0) (Fin.last (m + 1)) = y (Fin.last (m + 1))
        rw [Fin.snoc_last]
        change y (Fin.castSucc 0) = y (Fin.last (m + 1))
        exact hy.1.trans hy.2.symm
      | cast i =>
        change Fin.snoc (α := fun _ => Fin 2) (Fin.init y) (Fin.init y 0) i.castSucc = y i.castSucc
        rw [Fin.snoc_castSucc]
        rfl
    have hsub : (∑ y : Fin (m + 2) → Fin 2,
          if y 0 = a ∧ y (Fin.last (m + 1)) = a then ∏ i : Fin (m + 1), M i (y i.castSucc) (y i.succ) else 0) =
        ∑ y ∈ Finset.univ.map emb,
          if y 0 = a ∧ y (Fin.last (m + 1)) = a then ∏ i : Fin (m + 1), M i (y i.castSucc) (y i.succ) else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      split_ifs with hc
      · exfalso; exact hy (hmem y hc)
      · rfl
    rw [hsub, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro x _
    change (if x 0 = a then ∏ i : Fin (m + 1), M i (x i) (x (next i)) else 0) =
      if ext x 0 = a ∧ ext x (Fin.last (m + 1)) = a then
        ∏ i : Fin (m + 1), M i (ext x i.castSucc) (ext x i.succ) else 0
    have h0 : ext x 0 = x 0 := by
      change Fin.snoc (α := fun _ => Fin 2) x (x 0) (Fin.castSucc 0) = x 0
      rw [Fin.snoc_castSucc]
    have hL : ext x (Fin.last (m + 1)) = x 0 := by
      change Fin.snoc (α := fun _ => Fin 2) x (x 0) (Fin.last (m + 1)) = x 0
      rw [Fin.snoc_last]
    rw [h0, hL, hprod]
    by_cases hx : x 0 = a <;> simp [hx]
  have hgroup : (∑ x : Fin (m + 1) → Fin 2, ∏ i : Fin (m + 1), M i (x i) (x (next i))) =
      ∑ a : Fin 2, ∑ x : Fin (m + 1) → Fin 2,
        if x 0 = a then ∏ i : Fin (m + 1), M i (x i) (x (next i)) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_eq_single (x 0) (fun b _ hb => by simp [hb.symm]) (fun h => absurd (Finset.mem_univ _) h)]
    simp
  rw [hgroup]
  simp_rw [hsum_a]
  rfl

lemma cycle_sum_finset {n : ℕ} (hn : 0 < n) (M : Fin n → Matrix (Fin 2) (Fin 2) ℝ) :
    (∑ S : Finset (Fin n), ∏ i : Fin n, M i (bit S i) (bit S (next i))) =
      ((List.ofFn M).prod).trace := by
  change (∑ S : Finset (Fin n), (fun x => ∏ i : Fin n, M i (x i) (x (next i))) (bitEquiv n S)) = _
  rw [(bitEquiv n).sum_comp (fun x => ∏ i : Fin n, M i (x i) (x (next i)))]
  exact cycle_sum hn M

lemma trace_prod_rotate {n : ℕ} (M : Fin n → Matrix (Fin 2) (Fin 2) ℝ) :
    ((List.ofFn M).prod).trace = ((List.ofFn (fun i => M (next i))).prod).trace := by
  cases n with
  | zero => simp
  | succ m =>
    have hL : List.ofFn M = M 0 :: List.ofFn (fun i : Fin m => M i.succ) := List.ofFn_succ
    have hR : List.ofFn (fun i : Fin (m + 1) => M (next i)) =
        List.ofFn (fun i : Fin m => M i.succ) ++ [M 0] := by
      apply List.ext_getElem
      · simp
      · intro j hj1 hj2
        simp only [List.length_ofFn] at hj1
        rw [List.getElem_ofFn]
        by_cases hj : j < m
        · rw [List.getElem_append_left (by simp [hj]), List.getElem_ofFn]
          congr 1
          apply Fin.ext
          change (j + 1) % (m + 1) = j + 1
          exact Nat.mod_eq_of_lt (by omega)
        · have hjm : j = m := by omega
          rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_ofFn, hjm, Nat.sub_self, List.getElem_cons_zero]
          congr 1
          apply Fin.ext
          change (m + 1) % (m + 1) = 0
          exact Nat.mod_self _
    rw [hL, hR, List.prod_cons, List.prod_append, List.prod_singleton, Matrix.trace_mul_comm]

lemma trace_prod_rotate_iter {n : ℕ} (k : ℕ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℝ) :
    ((List.ofFn M).prod).trace = ((List.ofFn (fun i => M (next^[k] i))).prod).trace := by
  induction k generalizing M with
  | zero => rfl
  | succ k ih =>
    rw [trace_prod_rotate M, ih (fun i => M (next i))]
    congr 2
    apply List.ofFn_inj.mpr
    funext i
    rw [Function.iterate_succ_apply']

lemma list_prod_replicate {n : ℕ} (X : Matrix (Fin 2) (Fin 2) ℝ) :
    (List.replicate n X).prod = X ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.prod_cons, ih, pow_succ']

lemma sum_wt {n : ℕ} (hn : 0 < n) (r : ℝ) :
    (∑ S : Finset (Fin n), wt r S) = (1 + r) ^ n + (1 - r) ^ n := by
  have h1 : (∑ S : Finset (Fin n), wt r S) = ((List.ofFn (fun _ : Fin n => A r)).prod).trace :=
    cycle_sum_finset hn (fun _ => A r)
  rw [h1, List.ofFn_const, list_prod_replicate, A_pow]
  simp [Matrix.trace_fin_two]
  ring

def nonBdry {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => next i ∈ S ↔ i ∈ S).card

lemma two_runs_add_nonBdry {n : ℕ} (hn : 1 < n) (S : Finset (Fin n)) :
    2 * Join.runs S + nonBdry S = n := by
  have hb := boundary_card (finRotate n) S
  have hrun : (S.filter fun i => finRotate n i ∉ S).card = Join.runs S := by
    rw [Join.rot_eq hn]; rfl
  rw [hrun] at hb
  have hcomp : (boundary (finRotate n) S).card + nonBdry S = n := by
    have hdisj : Disjoint (boundary (finRotate n) S)
        (Finset.univ.filter fun i : Fin n => next i ∈ S ↔ i ∈ S) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      have h1 := (Finset.mem_filter.mp hi1).2
      have h2 := (Finset.mem_filter.mp hi2).2
      rw [Join.rot_eq hn] at h1
      exact h1 h2.symm
    have hunion : boundary (finRotate n) S ∪
        (Finset.univ.filter fun i : Fin n => next i ∈ S ↔ i ∈ S) = Finset.univ := by
      ext i
      simp only [Finset.mem_union, boundary, Finset.mem_filter, Finset.mem_univ, true_and,
        Join.rot_eq hn, iff_true]
      tauto
    unfold nonBdry
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  omega

lemma next_iter_eq {n : ℕ} (hn : 0 < n) (i : Fin n) (k : ℕ) :
    (next^[k] i).val = (i.val + k) % n := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change ((next^[k] i).val + 1) % n = (i.val + (k + 1)) % n
    rw [ih, Nat.mod_add_mod, Nat.add_assoc]

lemma next_reach_offset {n : ℕ} (i j : Fin n) :
    ∃ k < n, next^[k] i = j := by
  have hn : 0 < n := (Nat.zero_le _).trans_lt i.isLt
  refine ⟨(j.val + n - i.val) % n, Nat.mod_lt _ hn, Fin.ext ?_⟩
  rw [next_iter_eq hn, Nat.add_mod_mod]
  have h1 : i.val + (j.val + n - i.val) = n + j.val := by omega
  rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt j.isLt]

lemma next_iter_inj {n : ℕ} (k : ℕ) : Function.Injective (@next n)^[k] :=
  fun x y h => by rw [← prev_next_iter k x, ← prev_next_iter k y, h]

lemma sum_wt_nonBdry_one {n : ℕ} (hn : 0 < n) (r : ℝ) (i₀ : Fin n) :
    (∑ S : Finset (Fin n), wt r S * (if next i₀ ∈ S ↔ i₀ ∈ S then (1 : ℝ) else 0)) =
      (1 + r) ^ (n - 1) + (1 - r) ^ (n - 1) := by
  let M : Fin n → Matrix (Fin 2) (Fin 2) ℝ := fun i => if i = i₀ then 1 else A r
  have hid (S : Finset (Fin n)) :
      wt r S * (if next i₀ ∈ S ↔ i₀ ∈ S then (1 : ℝ) else 0) =
      ∏ i : Fin n, M i (bit S i) (bit S (next i)) := by
    have hfactor (i : Fin n) : M i (bit S i) (bit S (next i)) =
        A r (bit S i) (bit S (next i)) * (if i = i₀ then (if next i₀ ∈ S ↔ i₀ ∈ S then 1 else 0) else 1) := by
      by_cases hi : i = i₀
      · subst hi
        by_cases h1 : i ∈ S <;> by_cases h2 : next i ∈ S <;> simp [M, bit, A, h1, h2]
      · simp [M, hi]
    simp_rw [hfactor, Finset.prod_mul_distrib, wt]
    congr 1
    rw [Finset.prod_eq_single i₀ (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ _) h)]
    simp
  simp_rw [hid]
  rw [cycle_sum_finset hn M]
  obtain ⟨k, _, hk⟩ := next_reach_offset (⟨0, hn⟩ : Fin n) i₀
  rw [trace_prod_rotate_iter k M]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hk0 : next^[k] (0 : Fin (m + 1)) = i₀ := hk
  have hM0 : M (next^[k] (0 : Fin (m + 1))) = 1 := by simp [M, hk0]
  have hMs (j : Fin m) : M (next^[k] j.succ) = A r := by
    have hne : next^[k] j.succ ≠ i₀ := by
      rw [← hk0]
      exact fun h => Fin.succ_ne_zero j (next_iter_inj k h)
    simp [M, hne]
  rw [List.ofFn_succ, hM0, show (fun i : Fin m => M (next^[k] i.succ)) = fun _ => A r from funext hMs,
    List.ofFn_const, List.prod_cons, list_prod_replicate, one_mul, A_pow]
  simp [Matrix.trace_fin_two]
  ring

lemma sum_wt_nonBdry_two {n : ℕ} (hn : 1 < n) (r : ℝ) {i₀ i₁ : Fin n} (hne : i₀ ≠ i₁) :
    (∑ S : Finset (Fin n), wt r S *
        (if next i₀ ∈ S ↔ i₀ ∈ S then (1 : ℝ) else 0) *
        (if next i₁ ∈ S ↔ i₁ ∈ S then (1 : ℝ) else 0)) =
      (1 + r) ^ (n - 2) + (1 - r) ^ (n - 2) := by
  have hn0 : 0 < n := by omega
  let M : Fin n → Matrix (Fin 2) (Fin 2) ℝ := fun i => if i = i₀ ∨ i = i₁ then 1 else A r
  have hid (S : Finset (Fin n)) :
      wt r S * (if next i₀ ∈ S ↔ i₀ ∈ S then (1 : ℝ) else 0) *
        (if next i₁ ∈ S ↔ i₁ ∈ S then (1 : ℝ) else 0) =
      ∏ i : Fin n, M i (bit S i) (bit S (next i)) := by
    have hfactor (i : Fin n) : M i (bit S i) (bit S (next i)) =
        A r (bit S i) (bit S (next i)) *
          (if i = i₀ then (if next i₀ ∈ S ↔ i₀ ∈ S then 1 else 0) else 1) *
          (if i = i₁ then (if next i₁ ∈ S ↔ i₁ ∈ S then 1 else 0) else 1) := by
      by_cases hi0 : i = i₀
      · subst hi0
        have hi1 : i ≠ i₁ := hne
        by_cases h1 : i ∈ S <;> by_cases h2 : next i ∈ S <;> simp [M, bit, A, hi1, h1, h2]
      · by_cases hi1 : i = i₁
        · subst hi1
          by_cases h1 : i ∈ S <;> by_cases h2 : next i ∈ S <;> simp [M, bit, A, hi0, h1, h2]
        · simp [M, hi0, hi1]
    simp_rw [hfactor, Finset.prod_mul_distrib, wt]
    have p0 : (∏ i : Fin n, if i = i₀ then (if next i₀ ∈ S ↔ i₀ ∈ S then (1 : ℝ) else 0) else 1) =
        if next i₀ ∈ S ↔ i₀ ∈ S then 1 else 0 := by
      rw [Finset.prod_eq_single i₀ (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ _) h)]
      simp
    have p1 : (∏ i : Fin n, if i = i₁ then (if next i₁ ∈ S ↔ i₁ ∈ S then (1 : ℝ) else 0) else 1) =
        if next i₁ ∈ S ↔ i₁ ∈ S then 1 else 0 := by
      rw [Finset.prod_eq_single i₁ (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ _) h)]
      simp
    rw [p0, p1]
  simp_rw [hid]
  rw [cycle_sum_finset hn0 M]
  obtain ⟨k, hk_lt, hk⟩ := next_reach_offset (⟨0, hn0⟩ : Fin n) i₀
  rw [trace_prod_rotate_iter k M]
  let M' : Fin n → Matrix (Fin 2) (Fin 2) ℝ := fun i => M (next^[k] i)
  obtain ⟨t, ht_lt, ht⟩ := next_reach_offset (⟨0, hn0⟩ : Fin n) i₁
  let s : Fin n := ⟨(t + n - k) % n, Nat.mod_lt _ hn0⟩
  have hs : next^[k] s = i₁ := by
    apply Fin.ext
    rw [next_iter_eq hn0, Nat.mod_add_mod]
    have htv := congrArg Fin.val ht
    rw [next_iter_eq hn0, Nat.zero_add, Nat.mod_eq_of_lt ht_lt] at htv
    have hmod : (t + n - k + k) % n = t := by
      rw [show t + n - k + k = n + t by omega, Nat.add_mod_left, Nat.mod_eq_of_lt ht_lt]
    rw [hmod]
    exact htv
  have hs0 : s ≠ ⟨0, hn0⟩ := by
    intro h0
    rw [h0] at hs
    exact hne (hk.symm.trans hs)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0.ne'
  have hk0 : next^[k] (0 : Fin (m + 1)) = i₀ := hk
  have hM0 : M' 0 = 1 := by simp [M', M, hk0]
  have hMs : M' s = 1 := by simp [M', M, hs]
  have hMrest : ∀ i : Fin (m + 1), i ≠ 0 → i ≠ s → M' i = A r := by
    intro i hi0 his
    have h1 : next^[k] i ≠ i₀ := fun h => hi0 (next_iter_inj k (h.trans hk0.symm))
    have h2 : next^[k] i ≠ i₁ := fun h => his (next_iter_inj k (h.trans hs.symm))
    simp [M', M, h1, h2]
  have hs_pos : 0 < s.val := Nat.pos_of_ne_zero (fun h => hs0 (Fin.ext h))
  have hL : List.ofFn M' = [1] ++ List.replicate (s.val - 1) (A r) ++ [1] ++ List.replicate (m - s.val) (A r) := by
    apply List.ext_getElem
    · simp; omega
    · intro j hj1 hj2
      simp only [List.length_ofFn] at hj1
      rw [List.getElem_ofFn]
      by_cases hj0 : j = 0
      · subst hj0; simp [hM0]
      · by_cases hjs : j < s.val
        · have hne' : (⟨j, hj1⟩ : Fin (m + 1)) ≠ 0 ∧ (⟨j, hj1⟩ : Fin (m + 1)) ≠ s :=
            ⟨fun h => hj0 (congrArg Fin.val h), fun h => by have hv := congrArg Fin.val h; change j = s.val at hv; omega⟩
          rw [hMrest _ hne'.1 hne'.2]
          have hp : j < ([1] ++ List.replicate (s.val - 1) (A r)).length := by simp; omega
          rw [List.getElem_append_left (by simp; omega), List.getElem_append_left hp,
            List.getElem_append_right (by simp; omega)]
          simp
        · by_cases hje : j = s.val
          · subst hje
            have hseq : (⟨s.val, hj1⟩ : Fin (m + 1)) = s := Fin.ext rfl
            rw [hseq, hMs]
            have hp1 : ([1] ++ List.replicate (s.val - 1) (A r)).length ≤ s.val := by
              rw [List.length_append, List.length_singleton, List.length_replicate]; omega
            have hp2 : s.val < ([1] ++ List.replicate (s.val - 1) (A r) ++ [1]).length := by
              simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
              omega
            rw [List.getElem_append_left hp2, List.getElem_append_right hp1]
            simp
          · have hne' : (⟨j, hj1⟩ : Fin (m + 1)) ≠ 0 ∧ (⟨j, hj1⟩ : Fin (m + 1)) ≠ s :=
              ⟨fun h => hj0 (congrArg Fin.val h), fun h => by have hv := congrArg Fin.val h; change j = s.val at hv; omega⟩
            rw [hMrest _ hne'.1 hne'.2]
            have hp : ([1] ++ List.replicate (s.val - 1) (A r) ++ [1]).length ≤ j := by simp; omega
            rw [List.getElem_append_right hp]
            simp
  change (List.ofFn M').prod.trace = _
  rw [hL]
  simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one, one_mul, list_prod_replicate]
  rw [← pow_add, show s.val - 1 + (m - s.val) = m + 1 - 2 by omega, A_pow]
  simp [Matrix.trace_fin_two]
  ring

lemma sum_wt_X0 {n : ℕ} (hn : 0 < n) (r : ℝ) :
    (∑ S : Finset (Fin n), wt r S * (nonBdry S : ℝ)) =
      n * ((1 + r) ^ (n - 1) + (1 - r) ^ (n - 1)) := by
  classical
  have hcast (S : Finset (Fin n)) :
      (nonBdry S : ℝ) = ∑ i : Fin n, if next i ∈ S ↔ i ∈ S then (1 : ℝ) else 0 := by
    simp [nonBdry]
  simp_rw [hcast, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_wt_nonBdry_one hn r]
  simp [mul_add]

lemma sum_wt_X0_sq {n : ℕ} (hn : 1 < n) (r : ℝ) :
    (∑ S : Finset (Fin n), wt r S * (nonBdry S : ℝ) ^ 2) =
      n * ((1 + r) ^ (n - 1) + (1 - r) ^ (n - 1)) +
      n * (n - 1) * ((1 + r) ^ (n - 2) + (1 - r) ^ (n - 2)) := by
  classical
  have hn0 : 0 < n := by omega
  have hcast (S : Finset (Fin n)) :
      (nonBdry S : ℝ) ^ 2 = ∑ i₀ : Fin n, ∑ i₁ : Fin n,
        (if next i₀ ∈ S ↔ i₀ ∈ S then (1 : ℝ) else 0) *
        (if next i₁ ∈ S ↔ i₁ ∈ S then (1 : ℝ) else 0) := by
    have h1 : (nonBdry S : ℝ) = ∑ i : Fin n, if next i ∈ S ↔ i ∈ S then (1 : ℝ) else 0 := by
      simp [nonBdry, Finset.sum_ite]
    rw [h1, sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i₀ _
    rw [Finset.mul_sum]
  simp_rw [hcast, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hswap : (∑ i₀ : Fin n, ∑ S : Finset (Fin n), ∑ i₁ : Fin n,
      wt r S * ((if next i₀ ∈ S ↔ i₀ ∈ S then (1 : ℝ) else 0) *
        (if next i₁ ∈ S ↔ i₁ ∈ S then (1 : ℝ) else 0))) =
      ∑ i₀ : Fin n, ∑ i₁ : Fin n, ∑ S : Finset (Fin n),
        wt r S * (if next i₀ ∈ S ↔ i₀ ∈ S then (1 : ℝ) else 0) *
          (if next i₁ ∈ S ↔ i₁ ∈ S then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro i₀ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i₁ _
    apply Finset.sum_congr rfl
    intro S _
    ring
  rw [hswap]
  have hsplit (i₀ : Fin n) :
      (∑ i₁ : Fin n, ∑ S : Finset (Fin n),
        wt r S * (if next i₀ ∈ S ↔ i₀ ∈ S then (1 : ℝ) else 0) *
          (if next i₁ ∈ S ↔ i₁ ∈ S then (1 : ℝ) else 0)) =
      ((1 + r) ^ (n - 1) + (1 - r) ^ (n - 1)) +
        ((n : ℝ) - 1) * ((1 + r) ^ (n - 2) + (1 - r) ^ (n - 2)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have hdiag : (∑ S : Finset (Fin n), wt r S *
        (if next i₀ ∈ S ↔ i₀ ∈ S then (1 : ℝ) else 0) *
        (if next i₀ ∈ S ↔ i₀ ∈ S then (1 : ℝ) else 0)) =
        (1 + r) ^ (n - 1) + (1 - r) ^ (n - 1) := by
      rw [← sum_wt_nonBdry_one hn0 r i₀]
      apply Finset.sum_congr rfl
      intro S _
      split_ifs <;> ring
    have hoff : (∑ i₁ ∈ Finset.univ.erase i₀, ∑ S : Finset (Fin n),
        wt r S * (if next i₀ ∈ S ↔ i₀ ∈ S then (1 : ℝ) else 0) *
          (if next i₁ ∈ S ↔ i₁ ∈ S then (1 : ℝ) else 0)) =
        ((n : ℝ) - 1) * ((1 + r) ^ (n - 2) + (1 - r) ^ (n - 2)) := by
      have hconst : ∀ i₁ ∈ Finset.univ.erase i₀,
          (∑ S : Finset (Fin n), wt r S *
            (if next i₀ ∈ S ↔ i₀ ∈ S then (1 : ℝ) else 0) *
            (if next i₁ ∈ S ↔ i₁ ∈ S then (1 : ℝ) else 0)) =
          (1 + r) ^ (n - 2) + (1 - r) ^ (n - 2) := by
        intro i₁ hi₁
        exact sum_wt_nonBdry_two hn r (Finset.ne_of_mem_erase hi₁).symm
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      congr 1
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hdiag, hoff]
  simp_rw [hsplit, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

def patAt {n : ℕ} (w : List Bool) (S : Finset (Fin n)) (j : Fin n) : Bool :=
  (List.finRange w.length).all fun s => decide ((next^[s.val] j ∈ S) = w.get s)

def patCount {n : ℕ} (w : List Bool) (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun j : Fin n => patAt w S j = true).card

def patBit (w : List Bool) (s : ℕ) : Fin 2 :=
  if w.getD s false then 1 else 0

def unitMat (a b : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun x y => if x = a ∧ y = b then 1 else 0

def patMat (r : ℝ) (a b : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  (A r a b) • unitMat a b

noncomputable def patW (r : ℝ) (w : List Bool) : ℝ :=
  ∏ s : Fin (w.length - 1), A r (patBit w s.val) (patBit w (s.val + 1))

lemma unitMat_mul (a b c : Fin 2) : unitMat a b * unitMat b c = unitMat a c := by
  ext x y
  fin_cases x <;> fin_cases y <;> fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [unitMat, Matrix.mul_apply, Fin.sum_univ_two]

lemma unitMat_mul_trace (a b : Fin 2) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    (unitMat a b * X).trace = X b a := by
  fin_cases a <;> fin_cases b <;>
    simp [unitMat, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma unitMat_mul_quad_trace (a b : Fin 2) (X Y : Matrix (Fin 2) (Fin 2) ℝ) :
    (unitMat a b * X * unitMat a b * Y).trace = X b a * Y b a := by
  fin_cases a <;> fin_cases b <;>
    simp [unitMat, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma next_iter_inj_small {n : ℕ} (j : Fin n) {a b : ℕ} (ha : a < n) (hb : b < n)
    (heq : next^[a] j = next^[b] j) : a = b := by
  have hn : 0 < n := (Nat.zero_le _).trans_lt j.isLt
  have h := congrArg Fin.val heq
  rw [next_iter_eq hn, next_iter_eq hn] at h
  have hmod (x : ℕ) (hx : x < 2 * n) : x % n = if x < n then x else x - n := by
    split_ifs with hc
    · exact Nat.mod_eq_of_lt hc
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hmod (j.val + a) (by have := j.isLt; omega), hmod (j.val + b) (by have := j.isLt; omega)] at h
  split_ifs at h <;> omega

lemma patProd_aux (r : ℝ) (f : ℕ → Fin 2) : ∀ k : ℕ, 1 ≤ k →
    (List.ofFn (fun s : Fin k => patMat r (f s.val) (f (s.val + 1)))).prod =
    (∏ s : Fin k, A r (f s.val) (f (s.val + 1))) • unitMat (f 0) (f k) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      simp [patMat, List.ofFn_succ, List.ofFn_zero]
    | succ k =>
      have hk1 : 1 ≤ k + 1 := by omega
      have hL : List.ofFn (fun s : Fin (k + 2) => patMat r (f s.val) (f (s.val + 1))) =
          List.ofFn (fun s : Fin (k + 1) => patMat r (f s.val) (f (s.val + 1))) ++
            [patMat r (f (k + 1)) (f (k + 2))] := by
        apply List.ext_getElem
        · simp
        · intro j hj1 _
          simp only [List.length_ofFn] at hj1
          by_cases hj : j < k + 1
          · rw [List.getElem_ofFn, List.getElem_append_left (by simp [hj]), List.getElem_ofFn]
          · have hjk : j = k + 1 := by omega
            rw [List.getElem_ofFn, List.getElem_append_right (by simp; omega)]
            simp [hjk]
      rw [hL, List.prod_append, List.prod_singleton, ih hk1, patMat, smul_mul_smul_comm,
        unitMat_mul]
      congr 1
      symm
      rw [Fin.prod_univ_castSucc]
      simp [Fin.val_castSucc]

lemma patAt_iff {n : ℕ} (w : List Bool) (hw : 2 ≤ w.length) (S : Finset (Fin n)) (j : Fin n) :
    patAt w S j = true ↔ ∀ s : Fin (w.length - 1),
      bit S (next^[s.val] j) = patBit w s.val ∧ bit S (next^[s.val + 1] j) = patBit w (s.val + 1) := by
  have hbit (u : Fin n) (b : Bool) : (bit S u = if b then 1 else 0) ↔ ((u ∈ S) = b) := by
    by_cases hu : u ∈ S <;> cases b <;> simp [bit, hu]
  simp only [patAt, List.all_eq_true, List.mem_finRange, decide_eq_true_eq, patBit, hbit,
    List.getD_eq_getElem?_getD]
  constructor
  · intro h s
    have h1 := h ⟨s.val, by omega⟩ trivial
    have h2 := h ⟨s.val + 1, by omega⟩ trivial
    simp only [List.get_eq_getElem, List.getElem?_eq_getElem (by omega : s.val < w.length),
      List.getElem?_eq_getElem (by omega : s.val + 1 < w.length), Option.getD_some] at h1 h2 ⊢
    exact ⟨h1, h2⟩
  · intro h s _
    by_cases hs : s.val < w.length - 1
    · have := (h ⟨s.val, hs⟩).1
      simpa [List.get_eq_getElem, List.getElem?_eq_getElem s.isLt] using this
    · have hsm : s.val = (w.length - 2) + 1 := by omega
      have hs' : w.length - 2 < w.length - 1 := by omega
      have := (h ⟨w.length - 2, hs'⟩).2
      have hlt : w.length - 2 + 1 < w.length := by omega
      simp only [List.getElem?_eq_getElem hlt, Option.getD_some] at this
      simpa [List.get_eq_getElem, hsm] using this

lemma sum_wt_pat_one {n : ℕ} (r : ℝ) (w : List Bool) (hw : 2 ≤ w.length) (hwn : w.length ≤ n)
    (j : Fin n) :
    (∑ S : Finset (Fin n), wt r S * (if patAt w S j = true then 1 else 0)) =
      patW r w * (A r ^ (n - (w.length - 1))) (patBit w (w.length - 1)) (patBit w 0) := by
  classical
  let m := w.length - 1
  have hm1 : 1 ≤ m := by omega
  have hmn : m < n := by omega
  have hn0 : 0 < n := by omega
  let stepIdx (s : ℕ) : Fin n := next^[s] j
  have step_inj : ∀ s₁ s₂ : Fin m, stepIdx s₁.val = stepIdx s₂.val → s₁ = s₂ := by
    intro s₁ s₂ heq
    exact Fin.ext (next_iter_inj_small j (lt_trans s₁.isLt hmn) (lt_trans s₂.isLt hmn) heq)
  let M : Fin n → Matrix (Fin 2) (Fin 2) ℝ := fun i =>
    if h : ∃ s : Fin m, stepIdx s.val = i then
      let s := Classical.choose h
      patMat r (patBit w s.val) (patBit w (s.val + 1))
    else A r
  have hMs (s : Fin m) : M (stepIdx s.val) = patMat r (patBit w s.val) (patBit w (s.val + 1)) := by
    have h : ∃ s' : Fin m, stepIdx s'.val = stepIdx s.val := ⟨s, rfl⟩
    simp only [M, dif_pos h]
    have hs : Classical.choose h = s := step_inj _ _ (Classical.choose_spec h)
    rw [hs]
  have hid (S : Finset (Fin n)) :
      wt r S * (if patAt w S j = true then 1 else 0) =
      ∏ i : Fin n, M i (bit S i) (bit S (next i)) := by
    by_cases hpat : patAt w S j = true
    · rw [if_pos hpat, mul_one, wt]
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : ∃ s : Fin m, stepIdx s.val = i
      · rcases h with ⟨s, rfl⟩
        rw [hMs s]
        have hs := ((patAt_iff w hw S j).mp hpat) s
        have hns : next (stepIdx s.val) = next^[s.val + 1] j := (Function.iterate_succ_apply' next s.val j).symm
        change A r (bit S (stepIdx s.val)) (bit S (next (stepIdx s.val))) =
          patMat r (patBit w s.val) (patBit w (s.val + 1)) (bit S (stepIdx s.val)) (bit S (next (stepIdx s.val)))
        rw [hns, hs.1, hs.2]
        simp [patMat, unitMat]
      · simp [M, h]
    · rw [if_neg hpat, mul_zero]
      have hnot : ∃ s : Fin m, ¬ (bit S (next^[s.val] j) = patBit w s.val ∧
          bit S (next^[s.val + 1] j) = patBit w (s.val + 1)) := by
        by_contra hall
        push_neg at hall
        exact hpat ((patAt_iff w hw S j).mpr hall)
      rcases hnot with ⟨s, hs⟩
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ (stepIdx s.val))
      rw [hMs s]
      have hns : next (stepIdx s.val) = next^[s.val + 1] j := (Function.iterate_succ_apply' next s.val j).symm
      rw [hns]
      simp only [patMat, Matrix.smul_apply, smul_eq_mul, unitMat]
      split_ifs with hc
      · exfalso; exact hs ⟨hc.1, hc.2⟩
      · simp
  simp_rw [hid]
  rw [cycle_sum_finset hn0 M]
  obtain ⟨k, _, hk⟩ := next_reach_offset (⟨0, hn0⟩ : Fin n) j
  rw [trace_prod_rotate_iter k M]
  let M' : Fin n → Matrix (Fin 2) (Fin 2) ℝ := fun i => M (next^[k] i)
  have hstep (u : ℕ) (hu : u < n) : next^[k] ⟨u, hu⟩ = next^[u] j := by
    have h0 : (⟨u, hu⟩ : Fin n) = next^[u] ⟨0, hn0⟩ := by
      apply Fin.ext; rw [next_iter_eq hn0, Nat.zero_add, Nat.mod_eq_of_lt hu]
    rw [h0, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hk]
  have hM' (i : Fin n) : M' i =
      if h : i.val < m then patMat r (patBit w i.val) (patBit w (i.val + 1)) else A r := by
    by_cases hi : i.val < m
    · rw [dif_pos hi]
      change M (next^[k] i) = _
      rw [hstep i.val i.isLt]
      exact hMs ⟨i.val, hi⟩
    · rw [dif_neg hi]
      have hno : ¬ ∃ s : Fin m, stepIdx s.val = next^[k] i := by
        rintro ⟨s, hs⟩
        dsimp [stepIdx] at hs
        rw [← hstep s.val (lt_trans s.isLt hmn)] at hs
        have hval := congrArg Fin.val (next_iter_inj k hs.symm)
        change i.val = s.val at hval
        omega
      simp [M', M, hno]
  have hL : List.ofFn M' =
      List.ofFn (fun s : Fin m => patMat r (patBit w s.val) (patBit w (s.val + 1))) ++
        List.replicate (n - m) (A r) := by
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 _
      simp only [List.length_ofFn] at hi1
      rw [List.getElem_ofFn, hM']
      by_cases hi : i < m
      · rw [dite_eq_left_iff.mpr fun h => by exact absurd h (not_not.mpr hi),
          List.getElem_append_left (by simp [hi]), List.getElem_ofFn]
      · rw [dite_eq_right_iff.mpr fun h => by exact absurd h hi,
          List.getElem_append_right (by simp; omega)]
        simp
  change (List.ofFn M').prod.trace = _
  rw [hL, List.prod_append, patProd_aux r (patBit w) m hm1, list_prod_replicate,
    smul_mul_assoc, Matrix.trace_smul, unitMat_mul_trace]
  rfl

lemma sum_wt_pat_two {n : ℕ} (r : ℝ) (w : List Bool) (hw : 2 ≤ w.length)
    (j : Fin n) (d₁ d₂ : ℕ) (hd : d₁ + d₂ + 2 * (w.length - 1) = n) :
    let m := w.length - 1
    let k := next^[m + d₁] j
    (∑ S : Finset (Fin n), wt r S *
        (if patAt w S j = true then 1 else 0) *
        (if patAt w S k = true then 1 else 0)) =
      (patW r w) ^ 2 * (A r ^ d₁) (patBit w m) (patBit w 0) * (A r ^ d₂) (patBit w m) (patBit w 0) := by
  classical
  intro m k
  have hm1 : 1 ≤ m := by omega
  have hmn : m < n := by omega
  have hn0 : 0 < n := by omega
  let stepJ (s : ℕ) : Fin n := next^[s] j
  let stepK (s : ℕ) : Fin n := next^[s] k
  have step_inj : ∀ u : Fin n, ∀ s₁ s₂ : Fin m, next^[s₁.val] u = next^[s₂.val] u → s₁ = s₂ := by
    intro u s₁ s₂ heq
    exact Fin.ext (next_iter_inj_small u (lt_trans s₁.isLt hmn) (lt_trans s₂.isLt hmn) heq)
  have hdisj : ∀ s₁ s₂ : Fin m, stepJ s₁.val ≠ stepK s₂.val := by
    intro s₁ s₂ heq
    have h1 : stepK s₂.val = next^[m + d₁ + s₂.val] j := by
      dsimp [stepK, k]
      rw [← Function.iterate_add_apply, Nat.add_comm s₂.val (m + d₁)]
    rw [h1] at heq
    have := next_iter_inj_small j (by have := s₁.isLt; omega) (by have := s₂.isLt; omega) heq
    have hs1 := s₁.isLt
    omega
  let M : Fin n → Matrix (Fin 2) (Fin 2) ℝ := fun i =>
    if h1 : ∃ s : Fin m, stepJ s.val = i then
      let s := Classical.choose h1
      patMat r (patBit w s.val) (patBit w (s.val + 1))
    else if h2 : ∃ s : Fin m, stepK s.val = i then
      let s := Classical.choose h2
      patMat r (patBit w s.val) (patBit w (s.val + 1))
    else A r
  have hMsJ (s : Fin m) : M (stepJ s.val) = patMat r (patBit w s.val) (patBit w (s.val + 1)) := by
    have h : ∃ s' : Fin m, stepJ s'.val = stepJ s.val := ⟨s, rfl⟩
    simp only [M, dif_pos h]
    rw [step_inj j _ _ (Classical.choose_spec h)]
  have hMsK (s : Fin m) : M (stepK s.val) = patMat r (patBit w s.val) (patBit w (s.val + 1)) := by
    have hno : ¬ ∃ s' : Fin m, stepJ s'.val = stepK s.val := fun ⟨s', hs'⟩ => hdisj s' s hs'
    have h : ∃ s' : Fin m, stepK s'.val = stepK s.val := ⟨s, rfl⟩
    simp only [M, dif_neg hno, dif_pos h]
    rw [step_inj k _ _ (Classical.choose_spec h)]
  have hid (S : Finset (Fin n)) :
      wt r S * (if patAt w S j = true then 1 else 0) * (if patAt w S k = true then 1 else 0) =
      ∏ i : Fin n, M i (bit S i) (bit S (next i)) := by
    by_cases hj : patAt w S j = true
    · by_cases hk : patAt w S k = true
      · rw [if_pos hj, if_pos hk, mul_one, mul_one, wt]
        apply Finset.prod_congr rfl
        intro i _
        by_cases h1 : ∃ s : Fin m, stepJ s.val = i
        · rcases h1 with ⟨s, rfl⟩
          rw [hMsJ s]
          have hs := ((patAt_iff w hw S j).mp hj) s
          have hns : next (stepJ s.val) = next^[s.val + 1] j := (Function.iterate_succ_apply' next s.val j).symm
          change A r (bit S (stepJ s.val)) (bit S (next (stepJ s.val))) =
            patMat r (patBit w s.val) (patBit w (s.val + 1)) (bit S (stepJ s.val)) (bit S (next (stepJ s.val)))
          rw [hns, hs.1, hs.2]; simp [patMat, unitMat]
        · by_cases h2 : ∃ s : Fin m, stepK s.val = i
          · rcases h2 with ⟨s, rfl⟩
            rw [hMsK s]
            have hs := ((patAt_iff w hw S k).mp hk) s
            have hns : next (stepK s.val) = next^[s.val + 1] k := (Function.iterate_succ_apply' next s.val k).symm
            change A r (bit S (stepK s.val)) (bit S (next (stepK s.val))) =
              patMat r (patBit w s.val) (patBit w (s.val + 1)) (bit S (stepK s.val)) (bit S (next (stepK s.val)))
            rw [hns, hs.1, hs.2]; simp [patMat, unitMat]
          · simp [M, h1, h2]
      · rw [if_neg hk, mul_zero]
        have hnot : ∃ s : Fin m, ¬ (bit S (next^[s.val] k) = patBit w s.val ∧
            bit S (next^[s.val + 1] k) = patBit w (s.val + 1)) := by
          by_contra hall; push_neg at hall; exact hk ((patAt_iff w hw S k).mpr hall)
        rcases hnot with ⟨s, hs⟩
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ (stepK s.val))
        rw [hMsK s]
        have hns : next (stepK s.val) = next^[s.val + 1] k := (Function.iterate_succ_apply' next s.val k).symm
        rw [hns]; simp only [patMat, Matrix.smul_apply, smul_eq_mul, unitMat]
        split_ifs with hc
        · exfalso; exact hs ⟨hc.1, hc.2⟩
        · simp
    · rw [if_neg hj, mul_zero, zero_mul]
      have hnot : ∃ s : Fin m, ¬ (bit S (next^[s.val] j) = patBit w s.val ∧
          bit S (next^[s.val + 1] j) = patBit w (s.val + 1)) := by
        by_contra hall; push_neg at hall; exact hj ((patAt_iff w hw S j).mpr hall)
      rcases hnot with ⟨s, hs⟩
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ (stepJ s.val))
      rw [hMsJ s]
      have hns : next (stepJ s.val) = next^[s.val + 1] j := (Function.iterate_succ_apply' next s.val j).symm
      rw [hns]; simp only [patMat, Matrix.smul_apply, smul_eq_mul, unitMat]
      split_ifs with hc
      · exfalso; exact hs ⟨hc.1, hc.2⟩
      · simp
  simp_rw [hid]
  rw [cycle_sum_finset hn0 M]
  obtain ⟨r₀, _, hr₀⟩ := next_reach_offset (⟨0, hn0⟩ : Fin n) j
  rw [trace_prod_rotate_iter r₀ M]
  let M' : Fin n → Matrix (Fin 2) (Fin 2) ℝ := fun i => M (next^[r₀] i)
  let P := List.ofFn (fun s : Fin m => patMat r (patBit w s.val) (patBit w (s.val + 1)))
  have hL : List.ofFn M' = P ++ List.replicate d₁ (A r) ++ P ++ List.replicate d₂ (A r) := by
    apply List.ext_getElem
    · simp [P]; omega
    · intro i hi1 _
      simp only [List.length_ofFn] at hi1
      rw [List.getElem_ofFn]
      have hstep (u : ℕ) (hu : u < n) : next^[r₀] ⟨u, hu⟩ = next^[u] j := by
        have h0 : (⟨u, hu⟩ : Fin n) = next^[u] ⟨0, hn0⟩ := by
          apply Fin.ext; rw [next_iter_eq hn0, Nat.zero_add, Nat.mod_eq_of_lt hu]
        rw [h0, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hr₀]
      by_cases c1 : i < m
      · have : M' ⟨i, hi1⟩ = patMat r (patBit w i) (patBit w (i + 1)) := by
          change M (next^[r₀] ⟨i, hi1⟩) = _; rw [hstep i hi1]; exact hMsJ ⟨i, c1⟩
        rw [this]
        have hp : i < P.length := by simp [P, c1]
        rw [List.getElem_append_left (by simp [P]; omega), List.getElem_append_left (by simp [P]; omega),
          List.getElem_append_left hp, List.getElem_ofFn]
      · by_cases c2 : i < m + d₁
        · have hno1 : ¬ ∃ s : Fin m, stepJ s.val = next^[r₀] ⟨i, hi1⟩ := by
            rintro ⟨s, hs⟩
            dsimp [stepJ] at hs
            rw [← hstep s.val (by omega)] at hs
            have := congrArg Fin.val (next_iter_inj r₀ hs)
            change s.val = i at this; omega
          have hno2 : ¬ ∃ s : Fin m, stepK s.val = next^[r₀] ⟨i, hi1⟩ := by
            rintro ⟨s, hs⟩
            have hs' : stepK s.val = next^[r₀] ⟨m + d₁ + s.val, by omega⟩ := by
              dsimp [stepK, k]
              rw [hstep _ (by omega), ← Function.iterate_add_apply, Nat.add_comm s.val (m + d₁)]
            rw [hs'] at hs
            have := congrArg Fin.val (next_iter_inj r₀ hs)
            change m + d₁ + s.val = i at this; omega
          have : M' ⟨i, hi1⟩ = A r := by change M (next^[r₀] ⟨i, hi1⟩) = _; simp [M, hno1, hno2]
          rw [this]
          have hp1 : P.length ≤ i := by simp [P]; omega
          have hp2 : i < (P ++ List.replicate d₁ (A r)).length := by simp [P]; omega
          rw [List.getElem_append_left (by simp [P]; omega), List.getElem_append_left hp2,
            List.getElem_append_right hp1]
          simp
        · by_cases c3 : i < m + d₁ + m
          · let s : Fin m := ⟨i - (m + d₁), by omega⟩
            have : M' ⟨i, hi1⟩ = patMat r (patBit w s.val) (patBit w (s.val + 1)) := by
              change M (next^[r₀] ⟨i, hi1⟩) = _
              have hs' : stepK s.val = next^[r₀] ⟨i, hi1⟩ := by
                dsimp [stepK, k]
                rw [hstep i hi1, ← Function.iterate_add_apply, Nat.add_comm s.val (m + d₁),
                  show m + d₁ + s.val = i by dsimp [s]; omega]
              rw [← hs']; exact hMsK s
            rw [this]
            have hp1 : (P ++ List.replicate d₁ (A r)).length ≤ i := by simp [P]; omega
            have hp2 : i < (P ++ List.replicate d₁ (A r) ++ P).length := by simp [P]; omega
            rw [List.getElem_append_left hp2, List.getElem_append_right hp1, List.getElem_ofFn]
            congr 2 <;> simp [s, P]
          · have hno1 : ¬ ∃ s : Fin m, stepJ s.val = next^[r₀] ⟨i, hi1⟩ := by
              rintro ⟨s, hs⟩
              dsimp [stepJ] at hs
              rw [← hstep s.val (by omega)] at hs
              have := congrArg Fin.val (next_iter_inj r₀ hs)
              change s.val = i at this; omega
            have hno2 : ¬ ∃ s : Fin m, stepK s.val = next^[r₀] ⟨i, hi1⟩ := by
              rintro ⟨s, hs⟩
              have hs' : stepK s.val = next^[r₀] ⟨m + d₁ + s.val, by omega⟩ := by
                dsimp [stepK, k]
                rw [hstep _ (by omega), ← Function.iterate_add_apply, Nat.add_comm s.val (m + d₁)]
              rw [hs'] at hs
              have := congrArg Fin.val (next_iter_inj r₀ hs)
              change m + d₁ + s.val = i at this; omega
            have : M' ⟨i, hi1⟩ = A r := by change M (next^[r₀] ⟨i, hi1⟩) = _; simp [M, hno1, hno2]
            rw [this]
            have hp : (P ++ List.replicate d₁ (A r) ++ P).length ≤ i := by simp [P]; omega
            rw [List.getElem_append_right hp]
            simp
  change (List.ofFn M').prod.trace = _
  rw [hL]
  simp only [List.prod_append, list_prod_replicate, P]
  rw [patProd_aux r (patBit w) m hm1]
  simp only [smul_mul_assoc, mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
  rw [unitMat_mul_quad_trace]
  change (∏ s : Fin m, A r (patBit w s.val) (patBit w (s.val + 1))) *
      ((∏ s : Fin m, A r (patBit w s.val) (patBit w (s.val + 1))) *
        ((A r ^ d₁) (patBit w m) (patBit w 0) * (A r ^ d₂) (patBit w m) (patBit w 0))) = _
  change patW r w * (patW r w * _) = _
  ring

end Transfer

namespace Patterns
open SupportGeometry (next)
open HostDim (prev prev_next next_prev prev_next_iter prev_inj next_inj zdist zdist_spec zdist_lt zdist_eq_zero zdist_step oddZSet)
open Transfer (patAt patCount nonBdry two_runs_add_nonBdry)

lemma prev_iter_inj {n : ℕ} : ∀ k : ℕ, Function.Injective (prev^[k] : Fin n → Fin n) := by
  intro k a b h
  induction k generalizing a b with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
    exact prev_inj (ih h)

lemma next_iter_prev_iter {n : ℕ} (a b : ℕ) (h : a ≤ b) (j : Fin n) :
    next^[a] (prev^[b] j) = prev^[b - a] j := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
    rw [show b = (b - 1) + 1 by omega, Function.iterate_succ_apply, Function.iterate_succ_apply',
      next_prev, ih (b - 1) (by omega)]
    congr 1
    omega

lemma prev_iter_next_iter {n : ℕ} (a b : ℕ) (h : a ≤ b) (j : Fin n) :
    prev^[a] (next^[b] j) = next^[b - a] j := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
    rw [show b = (b - 1) + 1 by omega, Function.iterate_succ_apply, Function.iterate_succ_apply',
      prev_next, ih (b - 1) (by omega)]
    congr 1
    omega

noncomputable def remOdd {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j => 3 ≤ zdist S hS j ∧ zdist S hS j % 2 = 1

lemma oddZSet_card_eq {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    (oddZSet S hS).card = Join.runs S + (remOdd S hS).card := by
  classical
  let oneZ : Finset (Fin n) := Finset.univ.filter fun j => zdist S hS j = 1
  have hdisj : Disjoint oneZ (remOdd S hS) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have h1 := (Finset.mem_filter.mp hj1).2
    have h2 := (Finset.mem_filter.mp hj2).2.1
    omega
  have hunion : oddZSet S hS = oneZ ∪ remOdd S hS := by
    ext j
    simp only [oddZSet, oneZ, remOdd, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hjS, hmod⟩
      have hne0 : zdist S hS j ≠ 0 := by
        intro h0
        exact hjS ((zdist_eq_zero S hS j).mp h0)
      by_cases h1 : zdist S hS j = 1
      · left; exact h1
      · right; exact ⟨by omega, hmod⟩
    · rintro (h1 | ⟨h3, hmod⟩)
      · exact ⟨fun hjS => by have := (zdist_eq_zero S hS j).mpr hjS; omega, by omega⟩
      · exact ⟨fun hjS => by have := (zdist_eq_zero S hS j).mpr hjS; omega, hmod⟩
  have hruns : oneZ.card = Join.runs S := by
    unfold Join.runs
    symm
    refine Finset.card_bij (fun i _ => next i) ?_ ?_ ?_
    · intro i hi
      rcases Finset.mem_filter.mp hi with ⟨hiS, hniS⟩
      simp only [oneZ, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [zdist_step S hS hniS, prev_next, (zdist_eq_zero S hS i).mpr hiS]
    · intro a _ b _ h
      exact next_inj h
    · intro j hj
      have hj1 : zdist S hS j = 1 := (Finset.mem_filter.mp hj).2
      have hjS : j ∉ S := fun hs => by have := (zdist_eq_zero S hS j).mpr hs; omega
      have hpz : zdist S hS (prev j) = 0 := by
        have := zdist_step S hS hjS
        omega
      refine ⟨prev j, Finset.mem_filter.mpr ⟨(zdist_eq_zero S hS (prev j)).mp hpz, ?_⟩, next_prev j⟩
      rwa [next_prev]
  rw [hunion, Finset.card_union_of_disjoint hdisj, hruns]

lemma zdist_ge_iff {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (j : Fin n) (K : ℕ) :
    K ≤ zdist S hS j ↔ ∀ s < K, prev^[s] j ∉ S := by
  constructor
  · intro h s hs
    exact zdist_lt S hS (lt_of_lt_of_le hs h)
  · intro h
    by_contra! hlt
    exact h (zdist S hS j) hlt (zdist_spec S hS j)

lemma zdist_eq_iff {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (j : Fin n) (k : ℕ) :
    zdist S hS j = k ↔ (∀ s < k, prev^[s] j ∉ S) ∧ prev^[k] j ∈ S := by
  constructor
  · rintro rfl
    exact ⟨fun s hs => zdist_lt S hS hs, zdist_spec S hS j⟩
  · rintro ⟨h1, h2⟩
    have hge : k ≤ zdist S hS j := (zdist_ge_iff S hS j k).mpr h1
    by_contra! hne
    exact zdist_lt S hS (by omega : k < zdist S hS j) h2

lemma patAt_replicate_false_iff {n : ℕ} (K : ℕ) (S : Finset (Fin n)) (i : Fin n) :
    patAt (List.replicate K false) S i = true ↔ ∀ s < K, next^[s] i ∉ S := by
  simp only [patAt, List.all_eq_true, List.mem_finRange, decide_eq_true_eq,
    List.get_eq_getElem, List.getElem_replicate]
  constructor
  · intro h s hs
    have hs' : s < (List.replicate K false).length := by simp [hs]
    simpa using h ⟨s, hs'⟩ trivial
  · intro h s _
    have hs' : s.val < K := by simpa using s.isLt
    simpa using h s.val hs'

lemma patAt_true_replicate_false_iff {n : ℕ} (k : ℕ) (S : Finset (Fin n)) (i : Fin n) :
    patAt (true :: List.replicate k false) S i = true ↔
      i ∈ S ∧ ∀ s : ℕ, s < k → next^[s + 1] i ∉ S := by
  simp only [patAt, List.all_eq_true, List.mem_finRange, decide_eq_true_eq, List.get_eq_getElem]
  constructor
  · intro h
    refine ⟨?_, fun s hs => ?_⟩
    · simpa using h ⟨0, by simp⟩ trivial
    · have hs' : s + 1 < (true :: List.replicate k false).length := by simp [hs]
      simpa [List.getElem_cons_succ, List.getElem_replicate] using h ⟨s + 1, hs'⟩ trivial
  · rintro ⟨hiS, hno⟩ s _
    cases s with
    | mk v hv =>
      cases v with
      | zero => simpa using hiS
      | succ s =>
        have hs : s < k := by simp at hv; omega
        simpa [List.getElem_cons_succ, List.getElem_replicate] using hno s hs

lemma card_zdist_ge {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (K : ℕ) (hK : 1 ≤ K) :
    (Finset.univ.filter fun j : Fin n => K ≤ zdist S hS j).card =
      patCount (List.replicate K false) S := by
  unfold patCount
  refine Finset.card_bij (fun j _ => prev^[K - 1] j) ?_ ?_ ?_
  · intro j hj
    have hge := (zdist_ge_iff S hS j K).mp (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (patAt_replicate_false_iff K S _).mpr ?_⟩
    intro s hs
    rw [next_iter_prev_iter s (K - 1) (by omega)]
    exact hge (K - 1 - s) (by omega)
  · intro a _ b _ h
    exact prev_iter_inj (K - 1) h
  · intro i hi
    have hpat := (patAt_replicate_false_iff K S i).mp (Finset.mem_filter.mp hi).2
    refine ⟨next^[K - 1] i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (zdist_ge_iff S hS _ K).mpr ?_⟩,
      by simpa using prev_iter_next_iter (K - 1) (K - 1) le_rfl i⟩
    intro s hs
    rw [prev_iter_next_iter s (K - 1) (by omega) i]
    exact hpat (K - 1 - s) (by omega)

lemma card_zdist_eq {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (k : ℕ) :
    (Finset.univ.filter fun j : Fin n => zdist S hS j = k).card =
      patCount (true :: List.replicate k false) S := by
  unfold patCount
  refine Finset.card_bij (fun j _ => prev^[k] j) ?_ ?_ ?_
  · intro j hj
    rcases (zdist_eq_iff S hS j k).mp (Finset.mem_filter.mp hj).2 with ⟨hno, hyes⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (patAt_true_replicate_false_iff k S _).mpr ⟨hyes, ?_⟩⟩
    intro s hs
    rw [next_iter_prev_iter (s + 1) k (by omega)]
    exact hno (k - (s + 1)) (by omega)
  · intro a _ b _ h
    exact prev_iter_inj k h
  · intro i hi
    rcases (patAt_true_replicate_false_iff k S i).mp (Finset.mem_filter.mp hi).2 with ⟨hiS, hno⟩
    refine ⟨next^[k] i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (zdist_eq_iff S hS _ k).mpr ⟨?_, ?_⟩⟩,
      by simpa using prev_iter_next_iter k k le_rfl i⟩
    · intro s hs
      rw [prev_iter_next_iter s k (by omega) i, show k - s = (k - 1 - s) + 1 by omega]
      exact hno (k - 1 - s) (by omega)
    · rw [prev_iter_next_iter k k le_rfl i, Nat.sub_self]; exact hiS

lemma remOdd_bounds {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, patCount (true :: List.replicate (2 * m + 1) false) S) ≤ (remOdd S hS).card ∧
    (remOdd S hS).card ≤
      (∑ m ∈ Finset.Icc 1 M, patCount (true :: List.replicate (2 * m + 1) false) S) +
        patCount (List.replicate (2 * M + 3) false) S := by
  classical
  let head : Finset (Fin n) := Finset.univ.filter fun j =>
    3 ≤ zdist S hS j ∧ zdist S hS j % 2 = 1 ∧ zdist S hS j ≤ 2 * M + 1
  let tail : Finset (Fin n) := Finset.univ.filter fun j =>
    2 * M + 3 ≤ zdist S hS j ∧ zdist S hS j % 2 = 1
  have hdisj : Disjoint head tail := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have h1 := (Finset.mem_filter.mp hj1).2.2.2
    have h2 := (Finset.mem_filter.mp hj2).2.1
    omega
  have hunion : remOdd S hS = head ∪ tail := by
    ext j
    simp only [remOdd, head, tail, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h3, hmod⟩
      by_cases hle : zdist S hS j ≤ 2 * M + 1
      · left; exact ⟨h3, hmod, hle⟩
      · right; exact ⟨by omega, hmod⟩
    · rintro (⟨h3, hmod, _⟩ | ⟨hge, hmod⟩)
      · exact ⟨h3, hmod⟩
      · exact ⟨by omega, hmod⟩
  have hhead : head.card =
      ∑ m ∈ Finset.Icc 1 M, patCount (true :: List.replicate (2 * m + 1) false) S := by
    have hbi : head = (Finset.Icc 1 M).biUnion fun m =>
        Finset.univ.filter fun j => zdist S hS j = 2 * m + 1 := by
      ext j
      simp only [head, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h3, hmod, hle⟩
        refine ⟨(zdist S hS j - 1) / 2, ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨m, ⟨hm1, hmM⟩, heq⟩
        omega
    rw [hbi, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro m _
      exact card_zdist_eq S hS (2 * m + 1)
    · intro a _ b _ hab
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro j hja hjb
      have ha := (Finset.mem_filter.mp hja).2
      have hb := (Finset.mem_filter.mp hjb).2
      omega
  have htail : tail.card ≤ patCount (List.replicate (2 * M + 3) false) S := by
    rw [← card_zdist_ge S hS (2 * M + 3) (by omega)]
    apply Finset.card_le_card
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩
  rw [hunion, Finset.card_union_of_disjoint hdisj, hhead]
  omega

end Patterns

namespace Asymp
open SupportGeometry (next)
open Transfer (A A_pow wt wt_eq_q_pow_runs sum_wt nonBdry sum_wt_X0 sum_wt_X0_sq
  patAt patCount patBit patW next_reach_offset next_iter_inj_small sum_wt_pat_one sum_wt_pat_two)

lemma wt_nonneg {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (S : Finset (Fin n)) : 0 ≤ wt r S := by
  unfold wt
  apply Finset.prod_nonneg
  intro i _
  have hA (a b : Fin 2) : 0 ≤ A r a b := by
    fin_cases a <;> fin_cases b <;> simp [A, hr]
  exact hA _ _

lemma abs_sub_le_add {r : ℝ} (hr : 0 ≤ r) : |1 - r| ≤ 1 + r := by
  rw [abs_le]
  constructor <;> linarith

lemma A_pow_nonneg {r : ℝ} (hr : 0 ≤ r) (k : ℕ) (a b : Fin 2) : 0 ≤ (A r ^ k) a b := by
  rw [A_pow]
  have hle : |1 - r| ^ k ≤ (1 + r) ^ k :=
    pow_le_pow_left₀ (abs_nonneg _) (abs_sub_le_add hr) k
  have h1 : |(1 - r) ^ k| ≤ (1 + r) ^ k := by rw [abs_pow]; exact hle
  have h2 := (abs_le.mp h1).1
  have h3 := (abs_le.mp h1).2
  fin_cases a <;> fin_cases b <;> simp <;> linarith

lemma A_pow_le {r : ℝ} (hr : 0 ≤ r) (k : ℕ) (a b : Fin 2) :
    (A r ^ k) a b ≤ ((1 + r) ^ k + |1 - r| ^ k) / 2 := by
  rw [A_pow]
  have h1 : (1 - r) ^ k ≤ |1 - r| ^ k := by
    rw [← abs_pow]; exact le_abs_self _
  have h2 : -(1 - r) ^ k ≤ |1 - r| ^ k := by
    rw [← abs_pow]; exact neg_le_abs _
  fin_cases a <;> fin_cases b <;> simp <;> linarith

lemma A_pow_ge {r : ℝ} (k : ℕ) (a b : Fin 2) :
    ((1 + r) ^ k - |1 - r| ^ k) / 2 ≤ (A r ^ k) a b := by
  rw [A_pow]
  have h1 : (1 - r) ^ k ≤ |1 - r| ^ k := by
    rw [← abs_pow]; exact le_abs_self _
  have h2 : -(1 - r) ^ k ≤ |1 - r| ^ k := by
    rw [← abs_pow]; exact neg_le_abs _
  fin_cases a <;> fin_cases b <;> simp <;> linarith

lemma sum_wt_bounds {n : ℕ} (hn : 0 < n) (heven : Even n) (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) ^ n ≤ (∑ S : Finset (Fin n), wt r S) ∧
      (∑ S : Finset (Fin n), wt r S) ≤ 2 * (1 + r) ^ n := by
  rw [sum_wt hn r]
  have hnn : 0 ≤ (1 - r) ^ n := heven.pow_nonneg (1 - r)
  have hle : (1 - r) ^ n ≤ (1 + r) ^ n := by
    have h1 : |(1 - r) ^ n| ≤ (1 + r) ^ n := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub_le_add hr) n
    exact (abs_le.mp h1).2
  constructor <;> linarith

lemma var_X0 {n : ℕ} (hn : 2 ≤ n) (r : ℝ) (hr : 0 ≤ r) :
    let L := 1 + r
    ∑ S : Finset (Fin n), wt r S * ((nonBdry S : ℝ) - (n : ℝ) / L) ^ 2 ≤
      (n : ℝ) * L ^ (n - 1) + ((n : ℝ) * L + 4 * (n : ℝ) ^ 2) * |1 - r| ^ (n - 2) := by
  intro L
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := by linarith
  have hn0 : 0 < n := by omega
  have hexp : ∑ S : Finset (Fin n), wt r S * ((nonBdry S : ℝ) - (n : ℝ) / L) ^ 2 =
      (∑ S : Finset (Fin n), wt r S * (nonBdry S : ℝ) ^ 2) -
        2 * ((n : ℝ) / L) * (∑ S : Finset (Fin n), wt r S * (nonBdry S : ℝ)) +
        ((n : ℝ) / L) ^ 2 * (∑ S : Finset (Fin n), wt r S) := by
    have h1 : ∀ S : Finset (Fin n),
        wt r S * ((nonBdry S : ℝ) - (n : ℝ) / L) ^ 2 =
        wt r S * (nonBdry S : ℝ) ^ 2 - 2 * ((n : ℝ) / L) * (wt r S * (nonBdry S : ℝ)) +
          ((n : ℝ) / L) ^ 2 * wt r S := fun S => by ring
    simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexp, sum_wt hn0 r, sum_wt_X0 hn0 r, sum_wt_X0_sq hn r]
  have hpow1 : L ^ n = L ^ (n - 2) * L ^ 2 := by
    rw [← pow_add, show n - 2 + 2 = n by omega]
  have hpow2 : L ^ (n - 1) = L ^ (n - 2) * L := by
    rw [← pow_succ, show n - 2 + 1 = n - 1 by omega]
  have hmain : (n : ℝ) * L ^ (n - 1) + (n : ℝ) * ((n : ℝ) - 1) * L ^ (n - 2) -
      2 * ((n : ℝ) / L) * ((n : ℝ) * L ^ (n - 1)) + ((n : ℝ) / L) ^ 2 * L ^ n =
      (n : ℝ) * r * L ^ (n - 2) := by
    have hL0 : L ≠ 0 := hLpos.ne'
    rw [hpow1, hpow2]
    field_simp [hL0]
    dsimp [L]
    ring
  have hmain_le : (n : ℝ) * r * L ^ (n - 2) ≤ (n : ℝ) * L ^ (n - 1) := by
    have h1 : (n : ℝ) * r * L ^ (n - 2) ≤ (n : ℝ) * L * L ^ (n - 2) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hLpos.le _)
      apply mul_le_mul_of_nonneg_left (by dsimp [L]; linarith) (Nat.cast_nonneg _)
    calc (n : ℝ) * r * L ^ (n - 2) ≤ (n : ℝ) * L * L ^ (n - 2) := h1
      _ = (n : ℝ) * L ^ (n - 1) := by rw [mul_assoc, mul_comm L (L ^ (n - 2)), hpow2]
  have hbpow1 : |1 - r| ^ (n - 1) = |1 - r| ^ (n - 2) * |1 - r| := by
    rw [← pow_succ, show n - 2 + 1 = n - 1 by omega]
  have hbpow2 : |1 - r| ^ n = |1 - r| ^ (n - 2) * |1 - r| ^ 2 := by
    rw [← pow_add, show n - 2 + 2 = n by omega]
  have hba : |1 - r| ≤ L := abs_sub_le_add hr
  have hrem : (n : ℝ) * (1 - r) ^ (n - 1) + (n : ℝ) * ((n : ℝ) - 1) * (1 - r) ^ (n - 2) -
      2 * ((n : ℝ) / L) * ((n : ℝ) * (1 - r) ^ (n - 1)) + ((n : ℝ) / L) ^ 2 * (1 - r) ^ n ≤
      ((n : ℝ) * L + 4 * (n : ℝ) ^ 2) * |1 - r| ^ (n - 2) := by
    have habs (k : ℕ) : |(1 - r) ^ k| = |1 - r| ^ k := abs_pow _ _
    have hle_b (x : ℝ) (k : ℕ) : x * (1 - r) ^ k ≤ |x| * |1 - r| ^ k := by
      calc x * (1 - r) ^ k ≤ |x * (1 - r) ^ k| := le_abs_self _
        _ = |x| * |1 - r| ^ k := by rw [abs_mul, habs]
    have t1 : (n : ℝ) * (1 - r) ^ (n - 1) ≤ (n : ℝ) * L * |1 - r| ^ (n - 2) := by
      calc (n : ℝ) * (1 - r) ^ (n - 1) ≤ |(n : ℝ)| * |1 - r| ^ (n - 1) := hle_b _ _
        _ = (n : ℝ) * |1 - r| * |1 - r| ^ (n - 2) := by rw [abs_of_nonneg (Nat.cast_nonneg _), hbpow1]; ring
        _ ≤ (n : ℝ) * L * |1 - r| ^ (n - 2) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (abs_nonneg _) _)
          exact mul_le_mul_of_nonneg_left hba (Nat.cast_nonneg _)
    have t2 : (n : ℝ) * ((n : ℝ) - 1) * (1 - r) ^ (n - 2) ≤ (n : ℝ) ^ 2 * |1 - r| ^ (n - 2) := by
      calc (n : ℝ) * ((n : ℝ) - 1) * (1 - r) ^ (n - 2)
          ≤ |(n : ℝ) * ((n : ℝ) - 1)| * |1 - r| ^ (n - 2) := hle_b _ _
        _ ≤ (n : ℝ) ^ 2 * |1 - r| ^ (n - 2) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (abs_nonneg _) _)
          have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
            have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
            linarith
          rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hn1)]
          nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg _]
    have t3 : -(2 * ((n : ℝ) / L) * ((n : ℝ) * (1 - r) ^ (n - 1))) ≤
        2 * (n : ℝ) ^ 2 * |1 - r| ^ (n - 2) := by
      calc -(2 * ((n : ℝ) / L) * ((n : ℝ) * (1 - r) ^ (n - 1)))
          = (-2 * (n : ℝ) ^ 2 / L) * (1 - r) ^ (n - 1) := by ring
        _ ≤ |-2 * (n : ℝ) ^ 2 / L| * |1 - r| ^ (n - 1) := hle_b _ _
        _ = 2 * (n : ℝ) ^ 2 * (|1 - r| / L) * |1 - r| ^ (n - 2) := by
          rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
            abs_of_nonneg hLpos.le, hbpow1]
          ring
        _ ≤ 2 * (n : ℝ) ^ 2 * 1 * |1 - r| ^ (n - 2) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (abs_nonneg _) _)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (div_le_one hLpos).mpr hba
        _ = 2 * (n : ℝ) ^ 2 * |1 - r| ^ (n - 2) := by ring
    have t4 : ((n : ℝ) / L) ^ 2 * (1 - r) ^ n ≤ (n : ℝ) ^ 2 * |1 - r| ^ (n - 2) := by
      calc ((n : ℝ) / L) ^ 2 * (1 - r) ^ n
          ≤ |((n : ℝ) / L) ^ 2| * |1 - r| ^ n := hle_b _ _
        _ = (n : ℝ) ^ 2 * (|1 - r| / L) ^ 2 * |1 - r| ^ (n - 2) := by
          rw [abs_pow, abs_div, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hLpos.le, hbpow2]
          ring
        _ ≤ (n : ℝ) ^ 2 * 1 ^ 2 * |1 - r| ^ (n - 2) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (abs_nonneg _) _)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (div_nonneg (abs_nonneg _) hLpos.le) ((div_le_one hLpos).mpr hba) 2
        _ = (n : ℝ) ^ 2 * |1 - r| ^ (n - 2) := by ring
    linarith
  have hsplit : (n : ℝ) * ((1 + r) ^ (n - 1) + (1 - r) ^ (n - 1)) +
      (n : ℝ) * ((n : ℝ) - 1) * ((1 + r) ^ (n - 2) + (1 - r) ^ (n - 2)) -
      2 * ((n : ℝ) / L) * ((n : ℝ) * ((1 + r) ^ (n - 1) + (1 - r) ^ (n - 1))) +
      ((n : ℝ) / L) ^ 2 * ((1 + r) ^ n + (1 - r) ^ n) =
      ((n : ℝ) * L ^ (n - 1) + (n : ℝ) * ((n : ℝ) - 1) * L ^ (n - 2) -
        2 * ((n : ℝ) / L) * ((n : ℝ) * L ^ (n - 1)) + ((n : ℝ) / L) ^ 2 * L ^ n) +
      ((n : ℝ) * (1 - r) ^ (n - 1) + (n : ℝ) * ((n : ℝ) - 1) * (1 - r) ^ (n - 2) -
        2 * ((n : ℝ) / L) * ((n : ℝ) * (1 - r) ^ (n - 1)) + ((n : ℝ) / L) ^ 2 * (1 - r) ^ n) := by
    dsimp [L]; ring
  rw [hsplit, hmain]
  linarith

lemma sum_patCount_one {n : ℕ} (r : ℝ) (w : List Bool) (hw : 2 ≤ w.length) (hwn : w.length ≤ n) :
    (∑ S : Finset (Fin n), wt r S * (patCount w S : ℝ)) =
      (n : ℝ) * patW r w * (A r ^ (n - (w.length - 1))) (patBit w (w.length - 1)) (patBit w 0) := by
  have hcard : ∀ S : Finset (Fin n), (patCount w S : ℝ) =
      ∑ j : Fin n, (if patAt w S j = true then (1 : ℝ) else 0) := by
    intro S
    unfold patCount
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_wt_pat_one r w hw hwn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma sum_fin_next_iter {n : ℕ} (j : Fin n) (f : Fin n → ℝ) :
    (∑ k : Fin n, f k) = ∑ u : Fin n, f (next^[u.val] j) := by
  symm
  refine Finset.sum_bij (fun u _ => next^[u.val] j) (fun _ _ => Finset.mem_univ _) ?_ ?_ fun u _ => rfl
  · intro a _ b _ h
    exact Fin.ext (next_iter_inj_small j a.isLt b.isLt h)
  · intro k _
    obtain ⟨u, hu, hju⟩ := next_reach_offset j k
    exact ⟨⟨u, hu⟩, Finset.mem_univ _, hju⟩

lemma geom_sum_abs_sub {r : ℝ} (hr : 1 ≤ r) (K : ℕ) :
    (∑ d ∈ Finset.range (K + 1), |1 - r| ^ d * (1 + r) ^ (K - d)) ≤ (1 + r) ^ (K + 1) / 2 := by
  let L := 1 + r
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hsum : ∑ d ∈ Finset.range (K + 1), |1 - r| ^ d * L ^ (K - d) =
      L ^ K * ∑ d ∈ Finset.range (K + 1), (|1 - r| / L) ^ d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdK : d ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    rw [div_pow]
    field_simp [pow_ne_zero d hLpos.ne']
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hdK]
  rw [hsum]
  have hx0 : 0 ≤ |1 - r| / L := div_nonneg (abs_nonneg _) hLpos.le
  have hx : 1 - |1 - r| / L = 2 / L := by
    rw [abs_of_nonpos (by linarith : 1 - r ≤ 0)]
    dsimp [L]
    field_simp [hLpos.ne']
    ring
  have hgeom : (1 - |1 - r| / L) * ∑ d ∈ Finset.range (K + 1), (|1 - r| / L) ^ d =
      1 - (|1 - r| / L) ^ (K + 1) := by
    rw [mul_comm, geom_sum_mul_neg]
  have hgeom_le : (∑ d ∈ Finset.range (K + 1), (|1 - r| / L) ^ d) ≤ L / 2 := by
    have h2L : 0 < 2 / L := by positivity
    have hmul : (2 / L) * (∑ d ∈ Finset.range (K + 1), (|1 - r| / L) ^ d) ≤ 1 := by
      rw [← hx, hgeom]
      linarith [pow_nonneg hx0 (K + 1)]
    have hmul' := mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ L / 2)
    have hid : (L / 2) * ((2 / L) * ∑ d ∈ Finset.range (K + 1), (|1 - r| / L) ^ d) =
        ∑ d ∈ Finset.range (K + 1), (|1 - r| / L) ^ d := by
      field_simp [hLpos.ne']
    linarith
  calc L ^ K * ∑ d ∈ Finset.range (K + 1), (|1 - r| / L) ^ d
      ≤ L ^ K * (L / 2) := mul_le_mul_of_nonneg_left hgeom_le (pow_nonneg hLpos.le K)
    _ = L ^ (K + 1) / 2 := by rw [pow_succ]; ring

lemma var_pat {n : ℕ} (r : ℝ) (hr : 1 ≤ r) (w : List Bool) (hw : 2 ≤ w.length)
    (hpat : 0 ≤ patW r w) (hn : 2 * (w.length - 1) ≤ n) :
    let m := w.length - 1
    let L := 1 + r
    let μ := (n : ℝ) * patW r w / (2 * L ^ m)
    ∑ S : Finset (Fin n), wt r S * ((patCount w S : ℝ) - μ) ^ 2 ≤
      2 * (m : ℝ) * (n : ℝ) * patW r w * L ^ (n - m) +
        (n : ℝ) * (patW r w) ^ 2 * (3 / 8) * L ^ (n - 2 * m + 1) +
        (n : ℝ) ^ 2 * (patW r w) ^ 2 * |1 - r| ^ (n - m) / L ^ m := by
  intro m L μ
  have hr0 : 0 ≤ r := by linarith
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hn0 : 0 < n := by omega
  have hwn : w.length ≤ n := by omega
  have hm1 : 1 ≤ m := by omega
  have hcard : ∀ S : Finset (Fin n), (patCount w S : ℝ) =
      ∑ j : Fin n, (if patAt w S j = true then (1 : ℝ) else 0) := by
    intro S; unfold patCount; rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  have hT2_split : ∑ S : Finset (Fin n), wt r S * (patCount w S : ℝ) ^ 2 =
      ∑ j : Fin n, ∑ u : Fin n, ∑ S : Finset (Fin n),
        wt r S * (if patAt w S j = true then 1 else 0) *
          (if patAt w S (next^[u.val] j) = true then 1 else 0) := by
    have hsq (S : Finset (Fin n)) : wt r S * (patCount w S : ℝ) ^ 2 =
        ∑ j : Fin n, ∑ k : Fin n, wt r S * (if patAt w S j = true then 1 else 0) *
          (if patAt w S k = true then 1 else 0) := by
      rw [hcard S, sq, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hsq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    exact sum_fin_next_iter j fun k =>
      ∑ S : Finset (Fin n), wt r S * (if patAt w S j = true then 1 else 0) *
        (if patAt w S k = true then 1 else 0)
  have hj_bound (j : Fin n) :
      (∑ u : Fin n, ∑ S : Finset (Fin n),
        wt r S * (if patAt w S j = true then 1 else 0) *
          (if patAt w S (next^[u.val] j) = true then 1 else 0)) ≤
      2 * (m : ℝ) * patW r w * L ^ (n - m) +
        (patW r w) ^ 2 * ((n - 2 * m + 1 : ℕ) * L ^ (n - 2 * m) / 4 +
          (3 / 8) * L ^ (n - 2 * m + 1)) := by
    let disjR : Finset (Fin n) := Finset.univ.filter fun u => m ≤ u.val ∧ u.val ≤ n - m
    let overR : Finset (Fin n) := Finset.univ.filter fun u => ¬ (m ≤ u.val ∧ u.val ≤ n - m)
    have hpart : ∀ f : Fin n → ℝ, (∑ u : Fin n, f u) = (∑ u ∈ overR, f u) + ∑ u ∈ disjR, f u := by
      intro f
      have hd : Disjoint overR disjR := by
        rw [Finset.disjoint_left]; intro u hu1 hu2
        exact (Finset.mem_filter.mp hu1).2 (Finset.mem_filter.mp hu2).2
      have hu : overR ∪ disjR = Finset.univ := by
        ext u; simp only [overR, disjR, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      rw [← Finset.sum_union hd, hu]
    rw [hpart]
    have hover : (∑ u ∈ overR, ∑ S : Finset (Fin n),
        wt r S * (if patAt w S j = true then 1 else 0) *
          (if patAt w S (next^[u.val] j) = true then 1 else 0)) ≤
        2 * (m : ℝ) * patW r w * L ^ (n - m) := by
      have hterm : ∀ u : Fin n, (∑ S : Finset (Fin n),
          wt r S * (if patAt w S j = true then 1 else 0) *
            (if patAt w S (next^[u.val] j) = true then 1 else 0)) ≤
          patW r w * L ^ (n - m) := by
        intro u
        calc ∑ S : Finset (Fin n), wt r S * (if patAt w S j = true then 1 else 0) *
              (if patAt w S (next^[u.val] j) = true then 1 else 0)
            ≤ ∑ S : Finset (Fin n), wt r S * (if patAt w S j = true then 1 else 0) := by
              refine Finset.sum_le_sum fun S _ => ?_
              by_cases h1 : patAt w S j = true <;> by_cases h2 : patAt w S (next^[u.val] j) = true <;>
                simp [h1, h2, wt_nonneg hr0 S]
          _ = patW r w * (A r ^ (n - m)) (patBit w m) (patBit w 0) := sum_wt_pat_one r w hw hwn j
          _ ≤ patW r w * (((1 + r) ^ (n - m) + |1 - r| ^ (n - m)) / 2) :=
              mul_le_mul_of_nonneg_left (A_pow_le hr0 (n - m) _ _) hpat
          _ ≤ patW r w * L ^ (n - m) := by
              refine mul_le_mul_of_nonneg_left ?_ hpat
              have hba := pow_le_pow_left₀ (abs_nonneg _) (abs_sub_le_add hr0) (n - m)
              change (L ^ (n - m) + |1 - r| ^ (n - m)) / 2 ≤ L ^ (n - m)
              linarith
      have hcard_over : overR.card ≤ 2 * m := by
        let s1 : Finset (Fin n) := Finset.univ.filter fun u => u.val < m
        let s2 : Finset (Fin n) := Finset.univ.filter fun u => n - m < u.val
        have hsub : overR ⊆ s1 ∪ s2 := by
          intro u hu
          have h := (Finset.mem_filter.mp hu).2
          simp only [s1, s2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        have hs1 : s1.card ≤ m := by
          have : s1.card ≤ (Finset.range m).card := by
            refine Finset.card_le_card_of_injOn (fun u => u.val) ?_ ?_
            · intro u hu; exact Finset.mem_range.mpr (Finset.mem_filter.mp hu).2
            · intro a _ b _ h; exact Fin.ext h
          simpa using this
        have hs2 : s2.card ≤ m := by
          have hm_le : 2 * m ≤ n := hn
          have : s2.card ≤ (Finset.Icc 1 m).card := by
            refine Finset.card_le_card_of_injOn (fun u => n - u.val) ?_ ?_
            · intro u hu
              have hu1 : n - m < u.val := (Finset.mem_filter.mp hu).2
              dsimp only [m] at hu1
              have hu2 := u.isLt
              have hw_le : 2 * (w.length - 1) ≤ n := hn
              exact Finset.mem_Icc.mpr ⟨Nat.sub_pos_of_lt hu2,
                Nat.sub_le_iff_le_add.mpr (by dsimp only [m]; omega)⟩
            · intro a _ b _ h
              dsimp only at h
              have ha2 := a.isLt
              have hb2 := b.isLt
              exact Fin.ext (by omega)
          simpa using this
        exact (Finset.card_le_card hsub).trans ((Finset.card_union_le s1 s2).trans (by omega))
      calc ∑ u ∈ overR, _
          ≤ ∑ _u ∈ overR, (patW r w * L ^ (n - m)) := Finset.sum_le_sum fun u _ => hterm u
        _ = (overR.card : ℝ) * (patW r w * L ^ (n - m)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * m : ℕ) * (patW r w * L ^ (n - m)) := by
            refine mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard_over) ?_
            exact mul_nonneg hpat (pow_nonneg hLpos.le _)
        _ = 2 * (m : ℝ) * patW r w * L ^ (n - m) := by push_cast; ring
    have hdisj : (∑ u ∈ disjR, ∑ S : Finset (Fin n),
        wt r S * (if patAt w S j = true then 1 else 0) *
          (if patAt w S (next^[u.val] j) = true then 1 else 0)) ≤
        (patW r w) ^ 2 * ((n - 2 * m + 1 : ℕ) * L ^ (n - 2 * m) / 4 +
          (3 / 8) * L ^ (n - 2 * m + 1)) := by
      let K := n - 2 * m
      have hbij : (∑ u ∈ disjR, ∑ S : Finset (Fin n),
          wt r S * (if patAt w S j = true then 1 else 0) *
            (if patAt w S (next^[u.val] j) = true then 1 else 0)) =
          ∑ d₁ ∈ Finset.range (K + 1), (patW r w) ^ 2 *
            (A r ^ d₁) (patBit w m) (patBit w 0) * (A r ^ (K - d₁)) (patBit w m) (patBit w 0) := by
        refine Finset.sum_bij (fun u _ => u.val - m) ?_ ?_ ?_ ?_
        · intro u hu
          have h := (Finset.mem_filter.mp hu).2
          exact Finset.mem_range.mpr (by omega)
        · intro a ha b hb h
          have ha' := (Finset.mem_filter.mp ha).2
          have hb' := (Finset.mem_filter.mp hb).2
          exact Fin.ext (by omega)
        · intro d₁ hd₁
          have hd₁' := Finset.mem_range.mp hd₁
          have hK_eq : K = n - 2 * m := rfl
          have hm_le : 2 * m ≤ n := hn
          refine ⟨⟨m + d₁, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only [m]; omega⟩, by simp⟩
        · intro u hu
          have hu' : m ≤ u.val ∧ u.val ≤ n - m := (Finset.mem_filter.mp hu).2
          have hK_eq : K = n - 2 * m := rfl
          have hm_le : 2 * m ≤ n := hn
          have hd : (u.val - m) + (K - (u.val - m)) + 2 * (w.length - 1) = n := by dsimp only [m] at *; omega
          have hmadd : m + (u.val - m) = u.val := by omega
          have hpat2 := sum_wt_pat_two r w hw j (u.val - m) (K - (u.val - m)) hd
          dsimp only at hpat2
          rw [hmadd] at hpat2
          exact hpat2
      rw [hbij]
      have hterm (d₁ : ℕ) (hd₁ : d₁ ∈ Finset.range (K + 1)) :
          (patW r w) ^ 2 * (A r ^ d₁) (patBit w m) (patBit w 0) *
            (A r ^ (K - d₁)) (patBit w m) (patBit w 0) ≤
          (patW r w) ^ 2 * (L ^ K / 4 + (L ^ d₁ * |1 - r| ^ (K - d₁) +
            |1 - r| ^ d₁ * L ^ (K - d₁) + |1 - r| ^ K) / 4) := by
        have h1 : 0 ≤ (A r ^ d₁) (patBit w m) (patBit w 0) := A_pow_nonneg hr0 d₁ _ _
        have h2 : (A r ^ d₁) (patBit w m) (patBit w 0) ≤ (L ^ d₁ + |1 - r| ^ d₁) / 2 :=
          A_pow_le hr0 d₁ _ _
        have h3 : (A r ^ (K - d₁)) (patBit w m) (patBit w 0) ≤ (L ^ (K - d₁) + |1 - r| ^ (K - d₁)) / 2 :=
          A_pow_le hr0 (K - d₁) _ _
        have hnn3 : 0 ≤ (L ^ (K - d₁) + |1 - r| ^ (K - d₁)) / 2 := by positivity
        have hprod : (A r ^ d₁) (patBit w m) (patBit w 0) *
            (A r ^ (K - d₁)) (patBit w m) (patBit w 0) ≤
            ((L ^ d₁ + |1 - r| ^ d₁) / 2) * ((L ^ (K - d₁) + |1 - r| ^ (K - d₁)) / 2) :=
          mul_le_mul h2 h3 (A_pow_nonneg hr0 (K - d₁) _ _) (by positivity)
        have hdK : d₁ ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd₁)
        have hLK : L ^ d₁ * L ^ (K - d₁) = L ^ K := by rw [← pow_add, Nat.add_sub_cancel' hdK]
        have hbK : |1 - r| ^ d₁ * |1 - r| ^ (K - d₁) = |1 - r| ^ K := by
          rw [← pow_add, Nat.add_sub_cancel' hdK]
        have hmul : ((L ^ d₁ + |1 - r| ^ d₁) / 2) * ((L ^ (K - d₁) + |1 - r| ^ (K - d₁)) / 2) =
            L ^ K / 4 + (L ^ d₁ * |1 - r| ^ (K - d₁) + |1 - r| ^ d₁ * L ^ (K - d₁) + |1 - r| ^ K) / 4 := by
          calc _ = (L ^ d₁ * L ^ (K - d₁) + L ^ d₁ * |1 - r| ^ (K - d₁) +
              |1 - r| ^ d₁ * L ^ (K - d₁) + |1 - r| ^ d₁ * |1 - r| ^ (K - d₁)) / 4 := by ring
            _ = _ := by rw [hLK, hbK]; ring
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hprod.trans_eq hmul) (sq_nonneg _)
      calc ∑ d₁ ∈ Finset.range (K + 1), (patW r w) ^ 2 *
              (A r ^ d₁) (patBit w m) (patBit w 0) * (A r ^ (K - d₁)) (patBit w m) (patBit w 0)
          ≤ ∑ d₁ ∈ Finset.range (K + 1), (patW r w) ^ 2 *
              (L ^ K / 4 + (L ^ d₁ * |1 - r| ^ (K - d₁) + |1 - r| ^ d₁ * L ^ (K - d₁) + |1 - r| ^ K) / 4) :=
            Finset.sum_le_sum hterm
        _ = (patW r w) ^ 2 * ((K + 1 : ℕ) * L ^ K / 4 +
            ((∑ d₁ ∈ Finset.range (K + 1), L ^ d₁ * |1 - r| ^ (K - d₁)) +
             (∑ d₁ ∈ Finset.range (K + 1), |1 - r| ^ d₁ * L ^ (K - d₁)) +
             (∑ _d₁ ∈ Finset.range (K + 1), |1 - r| ^ K)) / 4) := by
            rw [← Finset.mul_sum]
            congr 1
            simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ← Finset.sum_div]
            ring
        _ ≤ (patW r w) ^ 2 * ((K + 1 : ℕ) * L ^ K / 4 + (3 / 8) * L ^ (K + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            refine add_le_add le_rfl ?_
            have g1 : (∑ d₁ ∈ Finset.range (K + 1), |1 - r| ^ d₁ * L ^ (K - d₁)) ≤ L ^ (K + 1) / 2 :=
              geom_sum_abs_sub hr K
            have g2 : (∑ d₁ ∈ Finset.range (K + 1), L ^ d₁ * |1 - r| ^ (K - d₁)) ≤ L ^ (K + 1) / 2 := by
              have heq : (∑ d₁ ∈ Finset.range (K + 1), L ^ d₁ * |1 - r| ^ (K - d₁)) =
                  ∑ d₁ ∈ Finset.range (K + 1), |1 - r| ^ d₁ * L ^ (K - d₁) := by
                rw [← Finset.sum_range_reflect (fun d₁ => |1 - r| ^ d₁ * L ^ (K - d₁)) (K + 1)]
                refine Finset.sum_congr rfl fun d hd => ?_
                have hd' := Finset.mem_range.mp hd
                rw [show K + 1 - 1 - d = K - d by omega, show K - (K - d) = d by omega]
                ring
              rw [heq]; exact g1
            have g3 : (∑ _d₁ ∈ Finset.range (K + 1), |1 - r| ^ K) ≤ L ^ (K + 1) / 2 := by
              calc (∑ _d₁ ∈ Finset.range (K + 1), |1 - r| ^ K)
                  ≤ ∑ d₁ ∈ Finset.range (K + 1), |1 - r| ^ d₁ * L ^ (K - d₁) := by
                    refine Finset.sum_le_sum fun d₁ hd₁ => ?_
                    have hdK : d₁ ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd₁)
                    rw [show |1 - r| ^ K = |1 - r| ^ d₁ * |1 - r| ^ (K - d₁) by
                      rw [← pow_add, Nat.add_sub_cancel' hdK]]
                    exact mul_le_mul_of_nonneg_left
                      (pow_le_pow_left₀ (abs_nonneg _) (abs_sub_le_add hr0) _)
                      (pow_nonneg (abs_nonneg _) _)
                _ ≤ L ^ (K + 1) / 2 := g1
            linarith
    linarith
  have hT2 : ∑ S : Finset (Fin n), wt r S * (patCount w S : ℝ) ^ 2 ≤
      2 * (m : ℝ) * (n : ℝ) * patW r w * L ^ (n - m) +
        (n : ℝ) * (patW r w) ^ 2 * ((n - 2 * m + 1 : ℕ) * L ^ (n - 2 * m) / 4 +
          (3 / 8) * L ^ (n - 2 * m + 1)) := by
    rw [hT2_split]
    calc ∑ j : Fin n, ∑ u : Fin n, ∑ S : Finset (Fin n),
            wt r S * (if patAt w S j = true then 1 else 0) *
              (if patAt w S (next^[u.val] j) = true then 1 else 0)
        ≤ ∑ _j : Fin n, (2 * (m : ℝ) * patW r w * L ^ (n - m) +
            (patW r w) ^ 2 * ((n - 2 * m + 1 : ℕ) * L ^ (n - 2 * m) / 4 +
              (3 / 8) * L ^ (n - 2 * m + 1))) := Finset.sum_le_sum fun j _ => hj_bound j
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hexp : ∑ S : Finset (Fin n), wt r S * ((patCount w S : ℝ) - μ) ^ 2 =
      (∑ S : Finset (Fin n), wt r S * (patCount w S : ℝ) ^ 2) -
        2 * μ * (∑ S : Finset (Fin n), wt r S * (patCount w S : ℝ)) +
        μ ^ 2 * (∑ S : Finset (Fin n), wt r S) := by
    have h1 (S : Finset (Fin n)) : wt r S * ((patCount w S : ℝ) - μ) ^ 2 =
        wt r S * (patCount w S : ℝ) ^ 2 - 2 * μ * (wt r S * (patCount w S : ℝ)) + μ ^ 2 * wt r S := by
      ring
    simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexp, sum_patCount_one r w hw hwn, sum_wt hn0 r]
  have hT1_ge : (n : ℝ) * patW r w * ((L ^ (n - m) - |1 - r| ^ (n - m)) / 2) ≤
      (n : ℝ) * patW r w * (A r ^ (n - m)) (patBit w m) (patBit w 0) :=
    mul_le_mul_of_nonneg_left (A_pow_ge (n - m) _ _) (mul_nonneg (Nat.cast_nonneg _) hpat)
  have hT0_le : (1 + r) ^ n + (1 - r) ^ n ≤ L ^ n + |1 - r| ^ n := by
    change L ^ n + (1 - r) ^ n ≤ L ^ n + |1 - r| ^ n
    have : (1 - r) ^ n ≤ |1 - r| ^ n := by rw [← abs_pow]; exact le_abs_self _
    linarith
  have hL0 : L ≠ 0 := hLpos.ne'
  have hLn : L ^ n = L ^ (n - 2 * m) * L ^ (2 * m) := by
    rw [← pow_add, show n - 2 * m + 2 * m = n by omega]
  have hLnm : L ^ (n - m) = L ^ (n - 2 * m) * L ^ m := by
    rw [← pow_add, show n - 2 * m + m = n - m by omega]
  have hL2m : L ^ (2 * m) = (L ^ m) ^ 2 := by rw [← pow_mul, mul_comm m 2]
  have hmain_cancel : (n : ℝ) * (patW r w) ^ 2 * ((n - 2 * m + 1 : ℕ) * L ^ (n - 2 * m) / 4) -
      2 * μ * ((n : ℝ) * patW r w * (L ^ (n - m) / 2)) + μ ^ 2 * L ^ n ≤ 0 := by
    have hmle : ((n - 2 * m + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : n - 2 * m + 1 ≤ n)
    have hfirst : (n : ℝ) * (patW r w) ^ 2 * ((n - 2 * m + 1 : ℕ) * L ^ (n - 2 * m) / 4) ≤
        (n : ℝ) ^ 2 * (patW r w) ^ 2 * L ^ (n - 2 * m) / 4 := by
      have hn2 : 0 ≤ (n : ℝ) * (patW r w) ^ 2 * L ^ (n - 2 * m) / 4 := by positivity
      calc (n : ℝ) * (patW r w) ^ 2 * ((n - 2 * m + 1 : ℕ) * L ^ (n - 2 * m) / 4)
          = ((n - 2 * m + 1 : ℕ) : ℝ) * ((n : ℝ) * (patW r w) ^ 2 * L ^ (n - 2 * m) / 4) := by ring
        _ ≤ (n : ℝ) * ((n : ℝ) * (patW r w) ^ 2 * L ^ (n - 2 * m) / 4) :=
            mul_le_mul_of_nonneg_right hmle hn2
        _ = (n : ℝ) ^ 2 * (patW r w) ^ 2 * L ^ (n - 2 * m) / 4 := by ring
    have hzero : (n : ℝ) ^ 2 * (patW r w) ^ 2 * L ^ (n - 2 * m) / 4 -
        2 * μ * ((n : ℝ) * patW r w * (L ^ (n - m) / 2)) + μ ^ 2 * L ^ n = 0 := by
      dsimp [μ]
      rw [hLn, hLnm, hL2m]
      field_simp [pow_ne_zero m hL0]
      ring
    linarith
  have hbn : |1 - r| ^ n ≤ |1 - r| ^ (n - m) * L ^ m := by
    rw [show |1 - r| ^ n = |1 - r| ^ (n - m) * |1 - r| ^ m by
      rw [← pow_add, show n - m + m = n by omega]]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (abs_sub_le_add hr0) m)
      (pow_nonneg (abs_nonneg _) _)
  have hbterm : 2 * μ * ((n : ℝ) * patW r w * (|1 - r| ^ (n - m) / 2)) + μ ^ 2 * |1 - r| ^ n ≤
      (n : ℝ) ^ 2 * (patW r w) ^ 2 * |1 - r| ^ (n - m) / L ^ m := by
    have h1 : μ ^ 2 * |1 - r| ^ n ≤ μ ^ 2 * (|1 - r| ^ (n - m) * L ^ m) :=
      mul_le_mul_of_nonneg_left hbn (sq_nonneg _)
    have h2 : 2 * μ * ((n : ℝ) * patW r w * (|1 - r| ^ (n - m) / 2)) +
        μ ^ 2 * (|1 - r| ^ (n - m) * L ^ m) =
        (3 / 4 : ℝ) * ((n : ℝ) ^ 2 * (patW r w) ^ 2 * |1 - r| ^ (n - m) / L ^ m) := by
      dsimp [μ]
      field_simp [pow_ne_zero m hL0]
      ring
    have h3 : 0 ≤ (n : ℝ) ^ 2 * (patW r w) ^ 2 * |1 - r| ^ (n - m) / L ^ m := by positivity
    linarith
  have h1 : 2 * μ * ((n : ℝ) * patW r w * (L ^ (n - m) / 2)) -
      2 * μ * ((n : ℝ) * patW r w * (|1 - r| ^ (n - m) / 2)) ≤
      2 * μ * ((n : ℝ) * patW r w * (A r ^ (n - m)) (patBit w m) (patBit w 0)) := by
    have hμ0 : 0 ≤ 2 * μ := by dsimp [μ]; positivity
    have hdiff : ((n : ℝ) * patW r w * (L ^ (n - m) / 2) -
        (n : ℝ) * patW r w * (|1 - r| ^ (n - m) / 2)) =
        (n : ℝ) * patW r w * ((L ^ (n - m) - |1 - r| ^ (n - m)) / 2) := by ring
    nlinarith [mul_le_mul_of_nonneg_left hT1_ge hμ0]
  linarith [hT2, h1, mul_le_mul_of_nonneg_left hT0_le (sq_nonneg μ)]

lemma L_prev_le {d : ℕ} (hd : 2 ≤ d) : Join.L (d - 1) ≤ (7 / 8 : ℝ) * Join.L d := by
  unfold Join.L Join.q
  have hd1 : 1 ≤ d := by omega
  have h2d : (4 : ℝ) ≤ (2 : ℝ) ^ d := by
    have : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd
    norm_num at this; exact this
  have hq : 3 ≤ (2 : ℝ) ^ d - 1 := by linarith
  have hqprev : (2 : ℝ) ^ (d - 1) - 1 = (((2 : ℝ) ^ d - 1) - 1) / 2 := by
    have : (2 : ℝ) ^ d = 2 * (2 : ℝ) ^ (d - 1) := by
      rw [← pow_succ', show d - 1 + 1 = d by omega]
    linarith
  have hsqrt_le : 8 * Real.sqrt ((2 : ℝ) ^ (d - 1) - 1) ≤ 6 * Real.sqrt ((2 : ℝ) ^ d - 1) := by
    rw [hqprev]
    have hy0 : 0 ≤ ((2 : ℝ) ^ d - 1 - 1) / 2 := by linarith
    have h1 : 8 * Real.sqrt (((2 : ℝ) ^ d - 1 - 1) / 2) = Real.sqrt (64 * (((2 : ℝ) ^ d - 1 - 1) / 2)) := by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 64 = 8 by norm_num]
    have h2 : 6 * Real.sqrt ((2 : ℝ) ^ d - 1) = Real.sqrt (36 * ((2 : ℝ) ^ d - 1)) := by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 36 = 6 by norm_num]
    rw [h1, h2]
    exact Real.sqrt_le_sqrt (by linarith)
  have h1le : 1 ≤ Real.sqrt ((2 : ℝ) ^ d - 1) := Real.one_le_sqrt.mpr (by linarith)
  linarith

lemma sum_powerset_q_card {α : Type*} [DecidableEq α] (A : Finset α) (q : ℝ) :
    (∑ S ∈ A.powerset, q ^ S.card) = (1 + q) ^ A.card := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.powerset_insert, Finset.sum_union, Finset.card_insert_of_notMem ha, pow_succ']
    · rw [Finset.sum_image (fun x hx y hy h => by
          have hax : a ∉ x := fun ha' => ha (Finset.mem_powerset.mp hx ha')
          have hay : a ∉ y := fun ha' => ha (Finset.mem_powerset.mp hy ha')
          have hdiff := congrArg (fun t => Finset.erase t a) h
          simpa [Finset.erase_insert hax, Finset.erase_insert hay] using hdiff)]
      have hcard : ∀ x ∈ s.powerset, q ^ (insert a x).card = q * q ^ x.card := by
        intro x hx
        have hax : a ∉ x := fun h => ha (Finset.mem_powerset.mp hx h)
        rw [Finset.card_insert_of_notMem hax, pow_succ']
      rw [Finset.sum_congr rfl hcard, ← Finset.mul_sum, ih]
      ring
    · rw [Finset.disjoint_left]
      intro T hT1 hT2
      rcases Finset.mem_image.mp hT2 with ⟨U, _, rfl⟩
      exact ha (Finset.mem_powerset.mp hT1 (Finset.mem_insert_self a U))

lemma parity_subset_card (t p : ℕ) (hp : p < 2) :
    (Finset.univ.filter fun i : Fin (6 * t) => i.val % 2 = p).card = 3 * t := by
  rw [← Fintype.card_fin (3 * t), ← Finset.card_univ]
  have hp2 : p = 0 ∨ p = 1 := by omega
  rcases hp2 with rfl | rfl
  · refine Finset.card_bij (fun i _ => (⟨i.val / 2, by have := i.isLt; omega⟩ : Fin (3 * t))) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a ha b hb h
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have hval := congrArg Fin.val h
      change a.val / 2 = b.val / 2 at hval
      exact Fin.ext (by omega)
    · intro k _
      refine ⟨⟨2 * k.val, by have := k.isLt; omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change (2 * k.val) % 2 = 0; omega⟩,
        Fin.ext (by change (2 * k.val) / 2 = k.val; simp)⟩
  · refine Finset.card_bij (fun i _ => (⟨i.val / 2, by have := i.isLt; omega⟩ : Fin (3 * t))) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a ha b hb h
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have hval := congrArg Fin.val h
      change a.val / 2 = b.val / 2 at hval
      exact Fin.ext (by omega)
    · intro k _
      refine ⟨⟨2 * k.val + 1, by have := k.isLt; omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change (2 * k.val + 1) % 2 = 1; omega⟩,
        Fin.ext (by
          change (2 * k.val + 1) / 2 = k.val
          rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by norm_num)]
          norm_num)⟩

lemma nonMixed_weight_le {t d : ℕ} (hd : 2 ≤ d) :
    let n := 6 * t
    let sites (S : Finset (Fin n)) (p : ℕ) : ℕ := (S.filter fun i => i.val % 2 = p).card
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => sites S 0 = 0 ∨ sites S 1 = 0),
      Join.q d ^ Join.runs S) ≤ 2 * ((2 : ℝ) ^ d) ^ (3 * t) := by
  intro n sites
  let E0 : Finset (Fin n) := Finset.univ.filter fun i => i.val % 2 = 0
  let E1 : Finset (Fin n) := Finset.univ.filter fun i => i.val % 2 = 1
  have hq1 : 1 ≤ Join.q d := by
    unfold Join.q
    have : (4 : ℝ) ≤ (2 : ℝ) ^ d := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
    linarith
  have hsub : (Finset.univ : Finset (Finset (Fin n))).filter (fun S => sites S 0 = 0 ∨ sites S 1 = 0) ⊆
      E0.powerset ∪ E1.powerset := by
    intro S hS
    rcases (Finset.mem_filter.mp hS).2 with h0 | h1
    · exact Finset.mem_union_right _ (Finset.mem_powerset.mpr fun i hi => by
        simp only [E1, Finset.mem_filter, Finset.mem_univ, true_and]
        by_contra hne
        have hi0 : i ∈ S.filter fun j => j.val % 2 = 0 := Finset.mem_filter.mpr ⟨hi, by omega⟩
        have hpos : 0 < sites S 0 := Finset.card_pos.mpr ⟨i, hi0⟩
        omega)
    · exact Finset.mem_union_left _ (Finset.mem_powerset.mpr fun i hi => by
        simp only [E0, Finset.mem_filter, Finset.mem_univ, true_and]
        by_contra hne
        have hi1 : i ∈ S.filter fun j => j.val % 2 = 1 := Finset.mem_filter.mpr ⟨hi, by omega⟩
        have hpos : 0 < sites S 1 := Finset.card_pos.mpr ⟨i, hi1⟩
        omega)
  have hle_card (S : Finset (Fin n)) : Join.q d ^ Join.runs S ≤ Join.q d ^ S.card := by
    apply pow_le_pow_right₀ hq1
    unfold Join.runs
    exact Finset.card_filter_le S _
  calc ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => sites S 0 = 0 ∨ sites S 1 = 0),
          Join.q d ^ Join.runs S
      ≤ ∑ S ∈ E0.powerset ∪ E1.powerset, Join.q d ^ S.card := by
        refine (Finset.sum_le_sum fun S _ => hle_card S).trans ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun S _ _ => pow_nonneg (by linarith) _
    _ ≤ (∑ S ∈ E0.powerset, Join.q d ^ S.card) + ∑ S ∈ E1.powerset, Join.q d ^ S.card := by
        rw [← Finset.sum_union_inter]
        linarith [Finset.sum_nonneg (fun S (_ : S ∈ E0.powerset ∩ E1.powerset) =>
          pow_nonneg (by linarith : 0 ≤ Join.q d) S.card)]
    _ = (1 + Join.q d) ^ E0.card + (1 + Join.q d) ^ E1.card := by
        rw [sum_powerset_q_card, sum_powerset_q_card]
    _ = 2 * ((2 : ℝ) ^ d) ^ (3 * t) := by
        rw [parity_subset_card t 0 (by norm_num), parity_subset_card t 1 (by norm_num)]
        have h1q : 1 + Join.q d = (2 : ℝ) ^ d := by unfold Join.q; ring
        rw [h1q]; ring

lemma nonMixed_weight_le_pred {t d : ℕ} (hd : 2 ≤ d)
    (sf : Finset (Finset (Fin (6 * t))))
    (hsf : ∀ S, S ∈ sf ↔ (S.filter fun i => i.val % 2 = 0).card = 0 ∨ (S.filter fun i => i.val % 2 = 1).card = 0) :
    (∑ S ∈ sf, Join.q d ^ Join.runs S) ≤ 2 * ((2 : ℝ) ^ d) ^ (3 * t) := by
  refine le_trans (le_of_eq ?_) (nonMixed_weight_le (t := t) hd)
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsf]

lemma patW_replicate_false (r : ℝ) (K : ℕ) :
    patW r (List.replicate K false) = 1 := by
  unfold patW
  refine Finset.prod_eq_one fun s _ => ?_
  have hs1 : s.val < K := by have := s.isLt; simp at this; omega
  have hs2 : s.val + 1 < K := by have := s.isLt; simp at this; omega
  simp [patBit, List.getD_eq_getElem?_getD, hs1, hs2, A]

lemma patW_true_replicate_false (r : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    patW r (true :: List.replicate k false) = r := by
  unfold patW
  have hlen : (true :: List.replicate k false).length - 1 = k := by simp
  have hf0 : patBit (true :: List.replicate k false) 0 = 1 := by
    simp [patBit, List.getD_eq_getElem?_getD]
  have hfpos (u : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) :
      patBit (true :: List.replicate k false) u = 0 := by
    cases u with
    | zero => omega
    | succ u' =>
      have : u' < k := by omega
      simp [patBit, List.getD_eq_getElem?_getD, this]
  let z : Fin ((true :: List.replicate k false).length - 1) := ⟨0, by rw [hlen]; omega⟩
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ z)]
  have h1 : A r (patBit (true :: List.replicate k false) z.val)
      (patBit (true :: List.replicate k false) (z.val + 1)) = r := by
    change A r (patBit (true :: List.replicate k false) 0) (patBit (true :: List.replicate k false) 1) = r
    rw [hf0, hfpos 1 le_rfl hk]
    simp [A]
  have h2 : (∏ s ∈ Finset.univ.erase z,
      A r (patBit (true :: List.replicate k false) s.val)
        (patBit (true :: List.replicate k false) (s.val + 1))) = 1 := by
    refine Finset.prod_eq_one fun s hs => ?_
    have hne : s ≠ z := Finset.ne_of_mem_erase hs
    have hs1 : 1 ≤ s.val := by
      have : s.val ≠ 0 := fun h0 => hne (Fin.ext h0)
      omega
    have hsk : s.val + 1 ≤ k := by have := s.isLt; simp at this; omega
    rw [hfpos s.val hs1 (by omega), hfpos (s.val + 1) (by omega) hsk]
    simp [A]
  rw [h1, h2, mul_one]

lemma geom_sum_remOdd {r : ℝ} (hr : 0 < r) (M : ℕ) :
    let L := 1 + r
    ∑ m ∈ Finset.Icc 1 M, r / L ^ (2 * m + 1) =
      (1 - 1 / L ^ (2 * M)) / (L * (L + 1)) := by
  intro L
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hL0 : L ≠ 0 := hLpos.ne'
  have hL10 : L + 1 ≠ 0 := by linarith
  induction M with
  | zero =>
    simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), ih]
    have hL2 : L ^ 2 - 1 = r * (L + 1) := by dsimp [L]; ring
    have hp1 : L ^ (2 * (M + 1) + 1) = L * L ^ (2 * (M + 1)) := by ring
    have hp2 : L ^ (2 * (M + 1)) = L ^ (2 * M) * L ^ 2 := by ring
    have hM0 : L ^ (2 * M) ≠ 0 := pow_ne_zero _ hL0
    have hM10 : L ^ (2 * (M + 1)) ≠ 0 := pow_ne_zero _ hL0
    field_simp [hL0, hL10, hM0, hM10]
    rw [hp1, hp2]
    calc ((L ^ (2 * M) - 1) * (L * (L ^ (2 * M) * L ^ 2)) + L ^ (2 * M) * L * (L + 1) * r) * (L ^ (2 * M) * L ^ 2)
        = ((L ^ (2 * M) - 1) * (L * (L ^ (2 * M) * L ^ 2)) + L ^ (2 * M) * L * (r * (L + 1))) * (L ^ (2 * M) * L ^ 2) := by
            ring
      _ = ((L ^ (2 * M) - 1) * (L * (L ^ (2 * M) * L ^ 2)) + L ^ (2 * M) * L * (L ^ 2 - 1)) * (L ^ (2 * M) * L ^ 2) := by
          rw [← hL2]
      _ = L ^ (2 * M) * (L * (L ^ (2 * M) * L ^ 2)) * (L ^ (2 * M) * L ^ 2 - 1) := by ring

lemma L_lower {d : ℕ} (hd : 2 ≤ d) : 2 < Join.L d ∧ 1 ≤ Real.sqrt (Join.q d) := by
  have hq3 : 3 ≤ Join.q d := by
    unfold Join.q
    have : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd
    norm_num at this; linarith
  have h1 : 1 ≤ Real.sqrt (Join.q d) := Real.one_le_sqrt.mpr (by linarith)
  have hsq : Real.sqrt 3 ≤ Real.sqrt (Join.q d) := Real.sqrt_le_sqrt hq3
  have hgt : 1 < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  unfold Join.L
  exact ⟨by linarith, h1⟩

lemma L_upper {d : ℕ} : Join.L d ≤ 2 * Real.sqrt ((2 : ℝ) ^ d) := by
  unfold Join.L Join.q
  have h1 : 1 ≤ Real.sqrt ((2 : ℝ) ^ d) :=
    Real.one_le_sqrt.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have h2 : Real.sqrt ((2 : ℝ) ^ d - 1) ≤ Real.sqrt ((2 : ℝ) ^ d) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

lemma two_pow_le_exp (k : ℕ) : (2 : ℝ) ^ k ≤ Real.exp (k : ℝ) := by
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  calc (2 : ℝ) ^ k ≤ (Real.exp 1) ^ k := pow_le_pow_left₀ (by norm_num) h2e k
    _ = Real.exp (k : ℝ) := by rw [← Real.exp_nat_mul]; simp

lemma one_sub_pow_le_exp_neg {x : ℝ} (hx0 : 0 ≤ 1 - x) (k : ℕ) :
    (1 - x) ^ k ≤ Real.exp (-(k : ℝ) * x) := by
  have h1 : 1 - x ≤ Real.exp (-x) := by
    simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-x)
  calc (1 - x) ^ k ≤ (Real.exp (-x)) ^ k := pow_le_pow_left₀ hx0 h1 k
    _ = Real.exp (-(k : ℝ) * x) := by rw [← Real.exp_nat_mul]; ring_nf

lemma exp_neg_pow_le_of_growth {D : ℕ → ℕ} (hD : ∀ t, 2 ≤ D t)
    (hgrowth : Filter.Tendsto (fun t : ℕ => ((D t : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (D t)) / (t : ℝ))
      Filter.atTop (nhds 0)) :
    ∀ K : ℕ, ∀ᶠ t : ℕ in Filter.atTop,
      1 ≤ t ∧ 8 * (K : ℝ) * ((D t : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (D t)) ≤ (t : ℝ) := by
  intro K
  have hev : ∀ᶠ t : ℕ in Filter.atTop,
      |((D t : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (D t)) / (t : ℝ) - 0| < 1 / (8 * (K : ℝ) + 1) :=
    hgrowth.eventually (Metric.ball_mem_nhds 0 (by positivity))
  filter_upwards [hev, Filter.eventually_ge_atTop (K + 1)] with t ht ht1
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  rw [sub_zero, abs_of_nonneg (by positivity)] at ht
  have h1 : ((D t : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (D t)) / (t : ℝ) ≤ 1 / (8 * (K : ℝ) + 1) := ht.le
  have hmul := (div_le_div_iff₀ htpos (by positivity : (0 : ℝ) < 8 * (K : ℝ) + 1)).mp h1
  have hnn : 0 ≤ ((D t : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (D t)) := by positivity
  refine ⟨by omega, ?_⟩
  nlinarith

lemma error_div_L_tendsto (D : ℕ → ℕ) (hD : ∀ t, 2 ≤ D t)
    (hgrowth : Filter.Tendsto (fun t : ℕ => ((D t : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (D t)) / (t : ℝ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t : ℕ =>
      let d := D t
      let n := 6 * t
      (1 + 2 * (Join.M 4 d - 1) * (Join.L d) ^ n * (Join.t d) ^ t +
        2 * Join.M 4 d * Join.q d * (Join.L (d - 1)) ^ n +
        2 * ((2 : ℝ) ^ d) ^ (3 * t)) / (Join.L d) ^ n) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hexp0 : Filter.Tendsto (fun k : ℕ => Real.exp (-(k : ℝ))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hhalf0 : Filter.Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hevK : ∀ᶠ k : ℕ in Filter.atTop,
      50 ≤ k ∧ 10 * Real.exp (-(k : ℝ)) < δ ∧ 10 * (1 / 2 : ℝ) ^ k < δ :=
    (Filter.eventually_ge_atTop 50).and
      (((tendsto_const_nhds.mul hexp0).eventually (Iio_mem_nhds (by simpa using hδ))).and
       ((tendsto_const_nhds.mul hhalf0).eventually (Iio_mem_nhds (by simpa using hδ))))
  obtain ⟨K, hK50, hKexp, hKhalf⟩ := hevK.exists
  have hgrow := exp_neg_pow_le_of_growth hD hgrowth K
  filter_upwards [hgrow, Filter.eventually_ge_atTop K] with t ⟨ht1, htg⟩ htK
  dsimp only
  let d := D t
  let n := 6 * t
  let L := Join.L d
  have hd2 : 2 ≤ d := hD t
  obtain ⟨hL2, _⟩ := L_lower hd2
  have hLpos : 0 < L := by linarith
  have hLnpos : 0 < L ^ n := pow_pos hLpos n
  have hsqrtpos : 0 < Real.sqrt ((2 : ℝ) ^ d) := Real.sqrt_pos.mpr (by positivity)
  have htl : (K : ℝ) * ((d : ℝ) + 1) ≤ (t : ℝ) / (4 * L) := by
    have h1 : 4 * L ≤ 8 * Real.sqrt ((2 : ℝ) ^ d) := by linarith [L_upper (d := d)]
    have h2 : (K : ℝ) * ((d : ℝ) + 1) * (4 * L) ≤ (t : ℝ) := by
      have hk0 : 0 ≤ (K : ℝ) * ((d : ℝ) + 1) := by positivity
      calc (K : ℝ) * ((d : ℝ) + 1) * (4 * L)
          ≤ (K : ℝ) * ((d : ℝ) + 1) * (8 * Real.sqrt ((2 : ℝ) ^ d)) := mul_le_mul_of_nonneg_left h1 hk0
        _ = 8 * (K : ℝ) * ((d : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ d) := by ring
        _ ≤ (t : ℝ) := htg
    exact (le_div_iff₀ (by positivity : 0 < 4 * L)).mpr h2
  have hts : 8 * (K : ℝ) ≤ (t : ℝ) / Real.sqrt ((2 : ℝ) ^ d) := by
    have hd3 : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]
    have h1 : 8 * (K : ℝ) * Real.sqrt ((2 : ℝ) ^ d) ≤ 8 * (K : ℝ) * ((d : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ d) := by
      have : 0 ≤ 8 * (K : ℝ) * Real.sqrt ((2 : ℝ) ^ d) := by positivity
      nlinarith
    exact (le_div_iff₀ hsqrtpos).mpr (h1.trans htg)
  have p1 : 1 / L ^ n ≤ (1 / 2 : ℝ) ^ K := by
    have h1 : (2 : ℝ) ^ n ≤ L ^ n := pow_le_pow_left₀ (by norm_num) hL2.le n
    have h2 : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by dsimp [n]; omega)
    calc 1 / L ^ n ≤ 1 / (2 : ℝ) ^ n := one_div_le_one_div_of_le (by positivity) h1
      _ ≤ 1 / (2 : ℝ) ^ K := one_div_le_one_div_of_le (by positivity) h2
      _ = (1 / 2 : ℝ) ^ K := by rw [div_pow, one_pow]
  have p2 : 2 * (Join.M 4 d - 1) * L ^ n * (Join.t d) ^ t / L ^ n ≤ 2 * Real.exp (-(K : ℝ)) := by
    have heq : 2 * (Join.M 4 d - 1) * L ^ n * (Join.t d) ^ t / L ^ n = 2 * (Join.M 4 d - 1) * (Join.t d) ^ t := by
      field_simp [hLnpos.ne']
    rw [heq]
    have ht0 : 0 ≤ Join.t d := by
      unfold Join.t
      have : 1 / (4 * L) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      linarith
    have htp : (Join.t d) ^ t ≤ Real.exp (-(t : ℝ) / (4 * L)) := by
      calc (Join.t d) ^ t = (1 - 1 / (4 * L)) ^ t := rfl
        _ ≤ Real.exp (-(t : ℝ) * (1 / (4 * L))) := one_sub_pow_le_exp_neg ht0 t
        _ = Real.exp (-(t : ℝ) / (4 * L)) := by ring_nf
    have hM : Join.M 4 d - 1 ≤ Real.exp ((4 * d : ℕ) : ℝ) := by
      unfold Join.M
      linarith [two_pow_le_exp (4 * d)]
    have hM0 : 0 ≤ Join.M 4 d - 1 := by
      unfold Join.M
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * d) := one_le_pow₀ (by norm_num)
      linarith
    calc 2 * (Join.M 4 d - 1) * (Join.t d) ^ t
        ≤ 2 * Real.exp ((4 * d : ℕ) : ℝ) * Real.exp (-(t : ℝ) / (4 * L)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num)) htp (pow_nonneg ht0 t) (by positivity)
      _ = 2 * Real.exp (((4 * d : ℕ) : ℝ) - (t : ℝ) / (4 * L)) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ 2 * Real.exp (-(K : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
          push_cast
          have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
          have : (50 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK50
          nlinarith
  have p3 : 2 * Join.M 4 d * Join.q d * (Join.L (d - 1)) ^ n / L ^ n ≤ 2 * (1 / 2 : ℝ) ^ K := by
    have hLp : Join.L (d - 1) ≤ (7 / 8 : ℝ) * L := L_prev_le hd2
    have hLp0 : 0 ≤ Join.L (d - 1) := by unfold Join.L; positivity
    have hpowL : (Join.L (d - 1)) ^ n / L ^ n ≤ (1 / 2 : ℝ) ^ t := by
      have h1 : (Join.L (d - 1)) ^ n ≤ ((7 / 8 : ℝ) * L) ^ n := pow_le_pow_left₀ hLp0 hLp n
      have h2 : ((7 / 8 : ℝ) * L) ^ n / L ^ n = ((7 / 8 : ℝ) ^ 6) ^ t := by
        calc ((7 / 8 : ℝ) * L) ^ n / L ^ n
            = (7 / 8 : ℝ) ^ n * L ^ n / L ^ n := by rw [mul_pow]
          _ = (7 / 8 : ℝ) ^ n := mul_div_cancel_right₀ _ hLnpos.ne'
          _ = ((7 / 8 : ℝ) ^ 6) ^ t := by dsimp [n]; rw [pow_mul]
      have h3 : ((7 / 8 : ℝ) ^ 6) ^ t ≤ (1 / 2 : ℝ) ^ t :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) t
      calc (Join.L (d - 1)) ^ n / L ^ n ≤ ((7 / 8 : ℝ) * L) ^ n / L ^ n :=
            div_le_div_of_nonneg_right h1 hLnpos.le
        _ = ((7 / 8 : ℝ) ^ 6) ^ t := h2
        _ ≤ (1 / 2 : ℝ) ^ t := h3
    have hMq : Join.M 4 d * Join.q d ≤ (2 : ℝ) ^ (5 * d) := by
      unfold Join.M Join.q
      have hq : (2 : ℝ) ^ d - 1 ≤ (2 : ℝ) ^ d := by linarith
      have hM0 : 0 ≤ (2 : ℝ) ^ (4 * d) := by positivity
      calc (2 : ℝ) ^ (4 * d) * ((2 : ℝ) ^ d - 1) ≤ (2 : ℝ) ^ (4 * d) * (2 : ℝ) ^ d :=
            mul_le_mul_of_nonneg_left hq hM0
        _ = (2 : ℝ) ^ (5 * d) := by rw [← pow_add]; congr 1; omega
    have ht5d : 5 * d + K ≤ t := by
      have h1 : 8 * (K : ℝ) * ((d : ℝ) + 1) ≤ 8 * (K : ℝ) * ((d : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ d) := by
        have hsq1 : 1 ≤ Real.sqrt ((2 : ℝ) ^ d) :=
          Real.one_le_sqrt.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        have : 0 ≤ 8 * (K : ℝ) * ((d : ℝ) + 1) := by positivity
        nlinarith
      have h2 : (5 * (d : ℝ) + (K : ℝ)) ≤ (t : ℝ) := by
        have : (50 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK50
        nlinarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]
      exact_mod_cast h2
    have h2half : (2 : ℝ) ^ (5 * d) * (1 / 2 : ℝ) ^ t ≤ (1 / 2 : ℝ) ^ K := by
      have hpow_eq : (2 : ℝ) ^ (5 * d) * (1 / 2 : ℝ) ^ t = (1 / 2 : ℝ) ^ (t - 5 * d) := by
        calc (2 : ℝ) ^ (5 * d) * (1 / 2 : ℝ) ^ t
            = (2 : ℝ) ^ (5 * d) * ((1 / 2 : ℝ) ^ (5 * d) * (1 / 2 : ℝ) ^ (t - 5 * d)) := by
              rw [← pow_add, Nat.add_sub_cancel' (by omega : 5 * d ≤ t)]
          _ = ((2 : ℝ) * (1 / 2 : ℝ)) ^ (5 * d) * (1 / 2 : ℝ) ^ (t - 5 * d) := by
              rw [mul_pow]; ring
          _ = (1 / 2 : ℝ) ^ (t - 5 * d) := by norm_num
      rw [hpow_eq, one_div, inv_pow, inv_pow]
      exact inv_anti₀ (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by omega : K ≤ t - 5 * d))
    calc 2 * Join.M 4 d * Join.q d * (Join.L (d - 1)) ^ n / L ^ n
        = 2 * ((Join.M 4 d * Join.q d) * ((Join.L (d - 1)) ^ n / L ^ n)) := by ring
      _ ≤ 2 * ((2 : ℝ) ^ (5 * d) * (1 / 2 : ℝ) ^ t) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hMq hpowL (by positivity) (by positivity)
      _ ≤ 2 * (1 / 2 : ℝ) ^ K := mul_le_mul_of_nonneg_left h2half (by norm_num)
  have p4 : 2 * ((2 : ℝ) ^ d) ^ (3 * t) / L ^ n ≤ 2 * Real.exp (-(K : ℝ)) := by
    have hLsq : L ^ 2 = (2 : ℝ) ^ d + 2 * Real.sqrt ((2 : ℝ) ^ d - 1) := by
      dsimp [L]; unfold Join.L Join.q
      have hnn : 0 ≤ (2 : ℝ) ^ d - 1 := by
        have : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
        linarith
      rw [add_sq, one_pow, Real.sq_sqrt hnn]
      ring
    have hsqrt_lo : Real.sqrt ((2 : ℝ) ^ d) ≤ 2 * Real.sqrt ((2 : ℝ) ^ d - 1) := by
      have h2d4 : (4 : ℝ) ≤ (2 : ℝ) ^ d := by
        have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hd2
        norm_num at this; exact this
      have h1 : (2 : ℝ) ^ d ≤ 4 * ((2 : ℝ) ^ d - 1) := by linarith
      calc Real.sqrt ((2 : ℝ) ^ d) ≤ Real.sqrt (4 * ((2 : ℝ) ^ d - 1)) := Real.sqrt_le_sqrt h1
        _ = 2 * Real.sqrt ((2 : ℝ) ^ d - 1) := by
            rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num]
    have hLsq_up : L ^ 2 ≤ 4 * (2 : ℝ) ^ d := by
      have h := pow_le_pow_left₀ hLpos.le (L_upper (d := d)) 2
      rw [mul_pow, Real.sq_sqrt (by positivity)] at h
      linarith
    have hrat : (2 : ℝ) ^ d / L ^ 2 ≤ 1 - 1 / (4 * Real.sqrt ((2 : ℝ) ^ d)) := by
      have hLsqpos : 0 < L ^ 2 := sq_pos_of_pos hLpos
      have h1 : (2 : ℝ) ^ d / L ^ 2 = 1 - 2 * Real.sqrt ((2 : ℝ) ^ d - 1) / L ^ 2 := by
        field_simp [hLsqpos.ne']; rw [hLsq]; ring
      have h2 : 1 / (4 * Real.sqrt ((2 : ℝ) ^ d)) ≤ 2 * Real.sqrt ((2 : ℝ) ^ d - 1) / L ^ 2 := by
        calc 1 / (4 * Real.sqrt ((2 : ℝ) ^ d))
            = Real.sqrt ((2 : ℝ) ^ d) / (4 * (2 : ℝ) ^ d) := by
              rw [div_eq_div_iff (by positivity) (by positivity)]
              have hms := Real.mul_self_sqrt (by positivity : 0 ≤ (2 : ℝ) ^ d)
              calc 1 * (4 * (2 : ℝ) ^ d) = 4 * (Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt ((2 : ℝ) ^ d)) := by
                    rw [hms, one_mul]
                _ = Real.sqrt ((2 : ℝ) ^ d) * (4 * Real.sqrt ((2 : ℝ) ^ d)) := by ring
          _ ≤ (2 * Real.sqrt ((2 : ℝ) ^ d - 1)) / L ^ 2 := by
              calc Real.sqrt ((2 : ℝ) ^ d) / (4 * (2 : ℝ) ^ d)
                  ≤ (2 * Real.sqrt ((2 : ℝ) ^ d - 1)) / (4 * (2 : ℝ) ^ d) :=
                    div_le_div_of_nonneg_right hsqrt_lo (by positivity)
                _ ≤ (2 * Real.sqrt ((2 : ℝ) ^ d - 1)) / L ^ 2 :=
                    div_le_div_of_nonneg_left (by positivity) hLsqpos hLsq_up
      linarith
    have hnn_rat : 0 ≤ 1 - 1 / (4 * Real.sqrt ((2 : ℝ) ^ d)) := by
      have hsq1 : 1 ≤ Real.sqrt ((2 : ℝ) ^ d) :=
        Real.one_le_sqrt.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      have : 1 / (4 * Real.sqrt ((2 : ℝ) ^ d)) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      linarith
    have hLn2 : L ^ n = (L ^ 2) ^ (3 * t) := by
      dsimp [n]; rw [← pow_mul, mul_comm 2 (3 * t)]; congr 1; omega
    have hpow_rat : ((2 : ℝ) ^ d) ^ (3 * t) / L ^ n ≤ Real.exp (-(K : ℝ)) := by
      rw [hLn2, ← div_pow]
      calc ((2 : ℝ) ^ d / L ^ 2) ^ (3 * t)
          ≤ (1 - 1 / (4 * Real.sqrt ((2 : ℝ) ^ d))) ^ (3 * t) :=
            pow_le_pow_left₀ (by positivity) hrat (3 * t)
        _ ≤ Real.exp (-((3 * t : ℕ) : ℝ) * (1 / (4 * Real.sqrt ((2 : ℝ) ^ d)))) :=
            one_sub_pow_le_exp_neg hnn_rat (3 * t)
        _ ≤ Real.exp (-(K : ℝ)) := by
            apply Real.exp_le_exp.mpr
            push_cast
            have : -((3 : ℝ) * (t : ℝ)) * (1 / (4 * Real.sqrt ((2 : ℝ) ^ d))) =
                -(3 / 4 : ℝ) * ((t : ℝ) / Real.sqrt ((2 : ℝ) ^ d)) := by ring
            rw [this]
            linarith
    calc 2 * ((2 : ℝ) ^ d) ^ (3 * t) / L ^ n
        = 2 * (((2 : ℝ) ^ d) ^ (3 * t) / L ^ n) := by ring
      _ ≤ 2 * Real.exp (-(K : ℝ)) := mul_le_mul_of_nonneg_left hpow_rat (by norm_num)
  have hsum_nonneg : 0 ≤ (1 + 2 * (Join.M 4 d - 1) * L ^ n * (Join.t d) ^ t +
      2 * Join.M 4 d * Join.q d * (Join.L (d - 1)) ^ n +
      2 * ((2 : ℝ) ^ d) ^ (3 * t)) / L ^ n := by
    have hM0 : 0 ≤ Join.M 4 d - 1 := by
      unfold Join.M; have : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * d) := one_le_pow₀ (by norm_num); linarith
    have hMnn : 0 ≤ Join.M 4 d := by unfold Join.M; positivity
    have hq0 : 0 ≤ Join.q d := Join.q_nn d
    have ht0 : 0 ≤ Join.t d := by
      unfold Join.t; have : 1 / (4 * L) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith); linarith
    have hLp0 : 0 ≤ Join.L (d - 1) := by unfold Join.L; positivity
    refine div_nonneg ?_ hLnpos.le
    refine add_nonneg (add_nonneg (add_nonneg (by norm_num) ?_) ?_) (by positivity)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) hLnpos.le) (pow_nonneg ht0 t)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hMnn) hq0) (pow_nonneg hLp0 n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsum_nonneg]
  have hdecomp : (1 + 2 * (Join.M 4 d - 1) * L ^ n * (Join.t d) ^ t +
      2 * Join.M 4 d * Join.q d * (Join.L (d - 1)) ^ n +
      2 * ((2 : ℝ) ^ d) ^ (3 * t)) / L ^ n =
      1 / L ^ n + 2 * (Join.M 4 d - 1) * L ^ n * (Join.t d) ^ t / L ^ n +
      2 * Join.M 4 d * Join.q d * (Join.L (d - 1)) ^ n / L ^ n +
      2 * ((2 : ℝ) ^ d) ^ (3 * t) / L ^ n := by ring
  rw [hdecomp]
  linarith

lemma abs_sub_div_L_le_exp {d : ℕ} (hd : 2 ≤ d) :
    let r := Real.sqrt (Join.q d)
    let L := Join.L d
    ∀ k : ℕ, (|1 - r| / L) ^ k ≤ Real.exp (-2 * (k : ℝ) / L) := by
  intro r L k
  obtain ⟨hL2, hr1⟩ := L_lower hd
  have hLpos : 0 < L := by linarith
  have hba : |1 - r| / L = 1 - 2 / L := by
    rw [abs_of_nonpos (by linarith : 1 - r ≤ 0)]
    dsimp [L]; unfold Join.L
    field_simp [hLpos.ne']
    ring
  have hnn : 0 ≤ 1 - 2 / L := by rw [← hba]; exact div_nonneg (abs_nonneg _) hLpos.le
  rw [hba]
  calc (1 - 2 / L) ^ k ≤ Real.exp (-(k : ℝ) * (2 / L)) := one_sub_pow_le_exp_neg hnn k
    _ = Real.exp (-2 * (k : ℝ) / L) := by ring_nf

lemma growth_L_div_n_tendsto (D : ℕ → ℕ)
    (hgrowth : Filter.Tendsto (fun t : ℕ => ((D t : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (D t)) / (t : ℝ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t : ℕ => (Join.L (D t) + 1) / ((6 * t : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hev := hgrowth.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < δ))
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with t ht ht1
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at ht
  have h1 : Join.L (D t) + 1 ≤ 3 * Real.sqrt ((2 : ℝ) ^ (D t)) := by
    have hsq1 : 1 ≤ Real.sqrt ((2 : ℝ) ^ (D t)) :=
      Real.one_le_sqrt.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    linarith [L_upper (d := D t)]
  have hd3 : (1 : ℝ) ≤ (D t : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ (D t : ℝ) from Nat.cast_nonneg _]
  have h2 : (Join.L (D t) + 1) / ((6 * t : ℕ) : ℝ) ≤
      ((D t : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (D t)) / (t : ℝ) := by
    have hLnn : 0 ≤ Join.L (D t) + 1 := by unfold Join.L; positivity
    have hsq0 : 0 ≤ Real.sqrt ((2 : ℝ) ^ (D t)) := Real.sqrt_nonneg _
    have hc1 : (Join.L (D t) + 1) / ((6 * t : ℕ) : ℝ) ≤
        (3 * Real.sqrt ((2 : ℝ) ^ (D t))) / (6 * (t : ℝ)) := by
      rw [show ((6 * t : ℕ) : ℝ) = 6 * (t : ℝ) by push_cast; rfl]
      exact div_le_div_of_nonneg_right h1 (by positivity)
    have hc2 : (3 * Real.sqrt ((2 : ℝ) ^ (D t))) / (6 * (t : ℝ)) ≤
        (6 * (((D t : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (D t)))) / (6 * (t : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    have hc3 : (6 * (((D t : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (D t)))) / (6 * (t : ℝ)) =
        ((D t : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (D t)) / (t : ℝ) := by
      field_simp [htpos.ne']
    exact (hc1.trans hc2).trans_eq hc3
  have hLpos : 0 < Join.L (D t) := by unfold Join.L; positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (by linarith) (Nat.cast_nonneg _))]
  exact h2.trans_lt ht

lemma var_X0_div_tendsto (D : ℕ → ℕ) (hD : ∀ t, 2 ≤ D t)
    (hgrowth : Filter.Tendsto (fun t : ℕ => ((D t : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (D t)) / (t : ℝ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t : ℕ =>
      let d := D t
      let n := 6 * t
      let r := Real.sqrt (Join.q d)
      let L := Join.L d
      (∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)) ^ 2) / L ^ n)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hexp0 : Filter.Tendsto (fun k : ℕ => Real.exp (-(k : ℝ))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hevK : ∀ᶠ k : ℕ in Filter.atTop, 50 ≤ k ∧ 50 * Real.exp (-(k : ℝ)) < δ / 2 :=
    (Filter.eventually_ge_atTop 50).and
      ((tendsto_const_nhds.mul hexp0).eventually (Iio_mem_nhds (by simpa using half_pos hδ)))
  obtain ⟨K, hK50, hKexp⟩ := hevK.exists
  have hgrow := exp_neg_pow_le_of_growth hD hgrowth K
  have hLn := (growth_L_div_n_tendsto D hgrowth).eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < min (δ / 4) 1))
  filter_upwards [hgrow, hLn, Filter.eventually_ge_atTop 1] with t ⟨ht1, htg⟩ hLnt _
  dsimp only
  let d := D t
  let n := 6 * t
  let r := Real.sqrt (Join.q d)
  let L := Join.L d
  have hd2 : 2 ≤ d := hD t
  obtain ⟨hL2, hr1⟩ := L_lower hd2
  have hr0 : 0 ≤ r := by linarith
  have hLpos : 0 < L := by linarith
  have hn2 : 2 ≤ n := by dsimp [n]; omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hLnpos : 0 < L ^ n := pow_pos hLpos n
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hLnt
  have hLn_lt1 : (L + 1) / (n : ℝ) < δ / 4 := lt_of_lt_of_le hLnt (min_le_left _ _)
  have hLn_lt2 : (L + 1) / (n : ℝ) < 1 := lt_of_lt_of_le hLnt (min_le_right _ _)
  have hpull : (∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)) ^ 2) =
      ((L + 1) / (n : ℝ)) ^ 2 * ∑ S : Finset (Fin n), wt r S * ((nonBdry S : ℝ) - (n : ℝ) / L) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => by ring
  have hv := var_X0 hn2 r hr0
  have hLdef : 1 + r = L := rfl
  rw [hLdef] at hv
  have hsum_nn : 0 ≤ (∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)) ^ 2) / L ^ n := by
    apply div_nonneg _ hLnpos.le
    exact Finset.sum_nonneg fun S _ => mul_nonneg (wt_nonneg hr0 S) (sq_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsum_nn, hpull]
  have hbound : ((L + 1) / (n : ℝ)) ^ 2 * (∑ S : Finset (Fin n), wt r S * ((nonBdry S : ℝ) - (n : ℝ) / L) ^ 2) / L ^ n ≤
      ((L + 1) / (n : ℝ)) ^ 2 * ((n : ℝ) * L ^ (n - 1) + ((n : ℝ) * L + 4 * (n : ℝ) ^ 2) * |1 - r| ^ (n - 2)) / L ^ n := by
    apply div_le_div_of_nonneg_right _ hLnpos.le
    exact mul_le_mul_of_nonneg_left hv (sq_nonneg _)
  have hpow1 : L ^ n = L ^ (n - 1) * L := by rw [← pow_succ, show n - 1 + 1 = n by omega]
  have hpow2 : L ^ n = L ^ (n - 2) * L ^ 2 := by rw [← pow_add, show n - 2 + 2 = n by omega]
  have hterm1 : ((L + 1) / (n : ℝ)) ^ 2 * ((n : ℝ) * L ^ (n - 1)) / L ^ n ≤ 2 * ((L + 1) / (n : ℝ)) := by
    have hid : ((L + 1) / (n : ℝ)) ^ 2 * ((n : ℝ) * L ^ (n - 1)) / L ^ n =
        ((L + 1) / L) * ((L + 1) / (n : ℝ)) := by
      rw [hpow1]; field_simp [hLpos.ne', hnpos.ne']
    rw [hid]
    have hL1L : (L + 1) / L ≤ 2 := by rw [div_le_iff₀ hLpos]; linarith
    exact mul_le_mul_of_nonneg_right hL1L (by positivity)
  have hterm2 : ((L + 1) / (n : ℝ)) ^ 2 * (((n : ℝ) * L + 4 * (n : ℝ) ^ 2) * |1 - r| ^ (n - 2)) / L ^ n ≤
      45 * Real.exp (-(K : ℝ)) := by
    have hsplit : ((L + 1) / (n : ℝ)) ^ 2 * (((n : ℝ) * L + 4 * (n : ℝ) ^ 2) * |1 - r| ^ (n - 2)) / L ^ n =
        (L + 1) ^ 2 * (L / (n : ℝ) + 4) / L ^ 2 * (|1 - r| / L) ^ (n - 2) := by
      rw [hpow2, div_pow, div_pow]; field_simp [hLpos.ne', hnpos.ne', pow_ne_zero (n - 2) hLpos.ne']
    rw [hsplit]
    have hc1 : (L + 1) ^ 2 / L ^ 2 ≤ 9 := by
      have : (L + 1) ^ 2 ≤ (3 * L) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      rw [div_le_iff₀ (sq_pos_of_pos hLpos)]
      nlinarith
    have hc2 : L / (n : ℝ) + 4 ≤ 5 := by
      have : L / (n : ℝ) ≤ (L + 1) / (n : ℝ) := div_le_div_of_nonneg_right (by linarith) hnpos.le
      linarith
    have hc3 : (L + 1) ^ 2 * (L / (n : ℝ) + 4) / L ^ 2 ≤ 45 := by
      have h1 : (L + 1) ^ 2 * (L / (n : ℝ) + 4) / L ^ 2 = ((L + 1) ^ 2 / L ^ 2) * (L / (n : ℝ) + 4) := by ring
      rw [h1]
      exact (mul_le_mul hc1 hc2 (by positivity) (by norm_num)).trans_eq (by norm_num)
    have hexp_b : (|1 - r| / L) ^ (n - 2) ≤ Real.exp (-(K : ℝ)) := by
      calc (|1 - r| / L) ^ (n - 2)
          ≤ Real.exp (-2 * ((n - 2 : ℕ) : ℝ) / L) := abs_sub_div_L_le_exp hd2 (n - 2)
        _ ≤ Real.exp (-(K : ℝ)) := by
            apply Real.exp_le_exp.mpr
            have hnm : 4 * (t : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by
              have : 4 * t ≤ n - 2 := by dsimp [n]; omega
              exact_mod_cast this
            have hL2s : L ≤ 2 * Real.sqrt ((2 : ℝ) ^ d) := L_upper
            have htl : 4 * (K : ℝ) * ((d : ℝ) + 1) ≤ (t : ℝ) / L := by
              have : 4 * (K : ℝ) * ((d : ℝ) + 1) * L ≤ (t : ℝ) := by
                have hk0 : 0 ≤ 4 * (K : ℝ) * ((d : ℝ) + 1) := by positivity
                calc 4 * (K : ℝ) * ((d : ℝ) + 1) * L
                    ≤ 4 * (K : ℝ) * ((d : ℝ) + 1) * (2 * Real.sqrt ((2 : ℝ) ^ d)) :=
                      mul_le_mul_of_nonneg_left hL2s hk0
                  _ = 8 * (K : ℝ) * ((d : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ d) := by ring
                  _ ≤ (t : ℝ) := htg
              exact (le_div_iff₀ hLpos).mpr this
            have hk_le : (K : ℝ) ≤ (t : ℝ) / L := by
              have : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg _]
              nlinarith [show (0 : ℝ) ≤ (K : ℝ) from Nat.cast_nonneg _]
            have hdiv : 4 * ((t : ℝ) / L) ≤ ((n - 2 : ℕ) : ℝ) / L := by
              rw [show 4 * ((t : ℝ) / L) = (4 * (t : ℝ)) / L by ring]
              exact div_le_div_of_nonneg_right hnm hLpos.le
            have hneg : -2 * ((n - 2 : ℕ) : ℝ) / L = -2 * (((n - 2 : ℕ) : ℝ) / L) := by ring
            rw [hneg]
            linarith
    exact mul_le_mul hc3 hexp_b (pow_nonneg (div_nonneg (abs_nonneg _) hLpos.le) _) (by norm_num)
  have hsep : ((L + 1) / (n : ℝ)) ^ 2 * ((n : ℝ) * L ^ (n - 1) + ((n : ℝ) * L + 4 * (n : ℝ) ^ 2) * |1 - r| ^ (n - 2)) / L ^ n =
      ((L + 1) / (n : ℝ)) ^ 2 * ((n : ℝ) * L ^ (n - 1)) / L ^ n +
      ((L + 1) / (n : ℝ)) ^ 2 * (((n : ℝ) * L + 4 * (n : ℝ) ^ 2) * |1 - r| ^ (n - 2)) / L ^ n := by ring
  calc ((L + 1) / (n : ℝ)) ^ 2 * (∑ S : Finset (Fin n), wt r S * ((nonBdry S : ℝ) - (n : ℝ) / L) ^ 2) / L ^ n
      ≤ ((L + 1) / (n : ℝ)) ^ 2 * ((n : ℝ) * L ^ (n - 1) + ((n : ℝ) * L + 4 * (n : ℝ) ^ 2) * |1 - r| ^ (n - 2)) / L ^ n := hbound
    _ = ((L + 1) / (n : ℝ)) ^ 2 * ((n : ℝ) * L ^ (n - 1)) / L ^ n +
        ((L + 1) / (n : ℝ)) ^ 2 * (((n : ℝ) * L + 4 * (n : ℝ) ^ 2) * |1 - r| ^ (n - 2)) / L ^ n := hsep
    _ ≤ 2 * ((L + 1) / (n : ℝ)) + 45 * Real.exp (-(K : ℝ)) := add_le_add hterm1 hterm2
    _ < δ / 2 + δ / 2 := by
        have : 2 * ((L + 1) / (n : ℝ)) < δ / 2 := by linarith
        linarith
    _ = δ := add_halves δ

lemma var_pat_div_tendsto (D : ℕ → ℕ) (hD : ∀ t, 2 ≤ D t)
    (hgrowth : Filter.Tendsto (fun t : ℕ => ((D t : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (D t)) / (t : ℝ))
      Filter.atTop (nhds 0))
    (w : List Bool) (hw : 3 ≤ w.length)
    (hpat_bnd : ∀ d : ℕ, 2 ≤ d → let r := Real.sqrt (Join.q d); 0 ≤ patW r w ∧ patW r w ≤ Join.L d) :
    Filter.Tendsto (fun t : ℕ =>
      let d := D t
      let n := 6 * t
      let r := Real.sqrt (Join.q d)
      let L := Join.L d
      let m := w.length - 1
      let μ := (n : ℝ) * patW r w / (2 * L ^ m)
      (∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) * ((patCount w S : ℝ) - μ)) ^ 2) / L ^ n)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  let m := w.length - 1
  have hm2 : 2 ≤ m := by dsimp [m]; omega
  have hexp0 : Filter.Tendsto (fun k : ℕ => Real.exp (-(k : ℝ))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hevK : ∀ᶠ k : ℕ in Filter.atTop, 50 ≤ k ∧ 10 * Real.exp (-(k : ℝ)) < δ / 2 :=
    (Filter.eventually_ge_atTop 50).and
      ((tendsto_const_nhds.mul hexp0).eventually (Iio_mem_nhds (by simpa using half_pos hδ)))
  obtain ⟨K, hK50, hKexp⟩ := hevK.exists
  have hgrow := exp_neg_pow_le_of_growth hD hgrowth K
  have hLn := (growth_L_div_n_tendsto D hgrowth).eventually
    (Metric.ball_mem_nhds 0 (by positivity : 0 < δ / (16 * ((m : ℝ) + 1))))
  filter_upwards [hgrow, hLn, Filter.eventually_ge_atTop m] with t ⟨ht1, htg⟩ hLnt htm
  dsimp only
  let d := D t
  let n := 6 * t
  let r := Real.sqrt (Join.q d)
  let L := Join.L d
  let μ := (n : ℝ) * patW r w / (2 * L ^ m)
  have hd2 : 2 ≤ d := hD t
  obtain ⟨hL2, hr1⟩ := L_lower hd2
  have hr0 : 0 ≤ r := by linarith
  have hLpos : 0 < L := by linarith
  have hn2m : 2 * m ≤ n := by dsimp [n]; omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hLnpos : 0 < L ^ n := pow_pos hLpos n
  obtain ⟨hpat0, hpatL⟩ := hpat_bnd d hd2
  change 0 ≤ patW r w at hpat0
  change patW r w ≤ L at hpatL
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hLnt
  have hpull : (∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) * ((patCount w S : ℝ) - μ)) ^ 2) =
      ((L + 1) / (n : ℝ)) ^ 2 * ∑ S : Finset (Fin n), wt r S * ((patCount w S : ℝ) - μ) ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun S _ => by ring
  have hv := var_pat r hr1 w (by omega) hpat0 hn2m
  change ∑ S : Finset (Fin n), wt r S * ((patCount w S : ℝ) - μ) ^ 2 ≤
      2 * (m : ℝ) * (n : ℝ) * patW r w * L ^ (n - m) +
        (n : ℝ) * (patW r w) ^ 2 * (3 / 8) * L ^ (n - 2 * m + 1) +
        (n : ℝ) ^ 2 * (patW r w) ^ 2 * |1 - r| ^ (n - m) / L ^ m at hv
  have hsum_nn : 0 ≤ (∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) * ((patCount w S : ℝ) - μ)) ^ 2) / L ^ n := by
    apply div_nonneg _ hLnpos.le
    exact Finset.sum_nonneg fun S _ => mul_nonneg (wt_nonneg hr0 S) (sq_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsum_nn, hpull]
  have hbound : ((L + 1) / (n : ℝ)) ^ 2 * (∑ S : Finset (Fin n), wt r S * ((patCount w S : ℝ) - μ) ^ 2) / L ^ n ≤
      ((L + 1) / (n : ℝ)) ^ 2 * (2 * (m : ℝ) * (n : ℝ) * patW r w * L ^ (n - m)) / L ^ n +
      ((L + 1) / (n : ℝ)) ^ 2 * ((n : ℝ) * (patW r w) ^ 2 * (3 / 8) * L ^ (n - 2 * m + 1)) / L ^ n +
      ((L + 1) / (n : ℝ)) ^ 2 * ((n : ℝ) ^ 2 * (patW r w) ^ 2 * |1 - r| ^ (n - m) / L ^ m) / L ^ n := by
    have hmul := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv (sq_nonneg ((L + 1) / (n : ℝ)))) hLnpos.le
    calc _ ≤ _ := hmul
      _ = _ := by ring
  have hLm2 : L ^ 2 ≤ L ^ m := pow_le_pow_right₀ (by linarith) hm2
  have hL1_2L : L + 1 ≤ 2 * L := by linarith
  have ht1' : ((L + 1) / (n : ℝ)) ^ 2 * (2 * (m : ℝ) * (n : ℝ) * patW r w * L ^ (n - m)) / L ^ n ≤
      8 * (m : ℝ) * ((L + 1) / (n : ℝ)) := by
    have hpow : L ^ n = L ^ (n - m) * L ^ m := by rw [← pow_add, show n - m + m = n by omega]
    have hid : ((L + 1) / (n : ℝ)) ^ 2 * (2 * (m : ℝ) * (n : ℝ) * patW r w * L ^ (n - m)) / L ^ n =
        (2 * (m : ℝ) * ((L + 1) * patW r w / L ^ m)) * ((L + 1) / (n : ℝ)) := by
      rw [hpow]; field_simp [hLpos.ne', hnpos.ne', pow_ne_zero m hLpos.ne']
    rw [hid]
    have hrat : (L + 1) * patW r w / L ^ m ≤ 2 := by
      rw [div_le_iff₀ (pow_pos hLpos m)]
      calc (L + 1) * patW r w ≤ (2 * L) * L := mul_le_mul hL1_2L hpatL hpat0 (by linarith)
        _ = 2 * L ^ 2 := by ring
        _ ≤ 2 * L ^ m := mul_le_mul_of_nonneg_left hLm2 (by norm_num)
    calc (2 * (m : ℝ) * ((L + 1) * patW r w / L ^ m)) * ((L + 1) / (n : ℝ))
        ≤ (2 * (m : ℝ) * 2) * ((L + 1) / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hrat (by positivity)
      _ ≤ 8 * (m : ℝ) * ((L + 1) / (n : ℝ)) := by
          have : 0 ≤ (m : ℝ) * ((L + 1) / (n : ℝ)) := by positivity
          linarith
  have ht2' : ((L + 1) / (n : ℝ)) ^ 2 * ((n : ℝ) * (patW r w) ^ 2 * (3 / 8) * L ^ (n - 2 * m + 1)) / L ^ n ≤
      2 * ((L + 1) / (n : ℝ)) := by
    have hpow : L ^ n = L ^ (n - 2 * m + 1) * L ^ (2 * m - 1) := by
      rw [← pow_add, show n - 2 * m + 1 + (2 * m - 1) = n by omega]
    have hid : ((L + 1) / (n : ℝ)) ^ 2 * ((n : ℝ) * (patW r w) ^ 2 * (3 / 8) * L ^ (n - 2 * m + 1)) / L ^ n =
        ((3 / 8 : ℝ) * ((L + 1) * (patW r w) ^ 2 / L ^ (2 * m - 1))) * ((L + 1) / (n : ℝ)) := by
      rw [hpow]; field_simp [hLpos.ne', hnpos.ne', pow_ne_zero (2 * m - 1) hLpos.ne']
    rw [hid]
    have hL3 : L ^ 3 ≤ L ^ (2 * m - 1) := pow_le_pow_right₀ (by linarith) (by omega)
    have hrat : (L + 1) * (patW r w) ^ 2 / L ^ (2 * m - 1) ≤ 2 := by
      rw [div_le_iff₀ (pow_pos hLpos _)]
      calc (L + 1) * (patW r w) ^ 2 ≤ (2 * L) * L ^ 2 :=
            mul_le_mul hL1_2L (pow_le_pow_left₀ hpat0 hpatL 2) (sq_nonneg _) (by linarith)
        _ = 2 * L ^ 3 := by ring
        _ ≤ 2 * L ^ (2 * m - 1) := mul_le_mul_of_nonneg_left hL3 (by norm_num)
    calc ((3 / 8 : ℝ) * ((L + 1) * (patW r w) ^ 2 / L ^ (2 * m - 1))) * ((L + 1) / (n : ℝ))
        ≤ ((3 / 8 : ℝ) * 2) * ((L + 1) / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hrat (by norm_num)
      _ ≤ 2 * ((L + 1) / (n : ℝ)) := by
          have : 0 ≤ (L + 1) / (n : ℝ) := by positivity
          linarith
  have ht3' : ((L + 1) / (n : ℝ)) ^ 2 * ((n : ℝ) ^ 2 * (patW r w) ^ 2 * |1 - r| ^ (n - m) / L ^ m) / L ^ n ≤
      4 * Real.exp (-(K : ℝ)) := by
    have hpow : L ^ n = L ^ (n - m) * L ^ m := by rw [← pow_add, show n - m + m = n by omega]
    have hid : ((L + 1) / (n : ℝ)) ^ 2 * ((n : ℝ) ^ 2 * (patW r w) ^ 2 * |1 - r| ^ (n - m) / L ^ m) / L ^ n =
        ((L + 1) ^ 2 * (patW r w) ^ 2 / L ^ (2 * m)) * (|1 - r| / L) ^ (n - m) := by
      have h2m : L ^ (2 * m) = L ^ m * L ^ m := by rw [← pow_add, two_mul]
      rw [hpow, div_pow, div_pow, h2m]
      field_simp [hnpos.ne', hLpos.ne', pow_ne_zero m hLpos.ne', pow_ne_zero (n - m) hLpos.ne']
    rw [hid]
    have hc : (L + 1) ^ 2 * (patW r w) ^ 2 / L ^ (2 * m) ≤ 4 := by
      rw [div_le_iff₀ (pow_pos hLpos _)]
      have hL4 : L ^ 4 ≤ L ^ (2 * m) := pow_le_pow_right₀ (by linarith) (by omega)
      calc (L + 1) ^ 2 * (patW r w) ^ 2 ≤ (2 * L) ^ 2 * L ^ 2 :=
            mul_le_mul (pow_le_pow_left₀ (by linarith) hL1_2L 2) (pow_le_pow_left₀ hpat0 hpatL 2)
              (sq_nonneg _) (by positivity)
        _ = 4 * L ^ 4 := by ring
        _ ≤ 4 * L ^ (2 * m) := mul_le_mul_of_nonneg_left hL4 (by norm_num)
    have hexp_b : (|1 - r| / L) ^ (n - m) ≤ Real.exp (-(K : ℝ)) := by
      calc (|1 - r| / L) ^ (n - m)
          ≤ Real.exp (-2 * ((n - m : ℕ) : ℝ) / L) := abs_sub_div_L_le_exp hd2 (n - m)
        _ ≤ Real.exp (-(K : ℝ)) := by
            apply Real.exp_le_exp.mpr
            have hnm : 3 * (t : ℝ) ≤ ((n - m : ℕ) : ℝ) := by
              have : 3 * t ≤ n - m := by dsimp [n]; omega
              exact_mod_cast this
            have hL2s : L ≤ 2 * Real.sqrt ((2 : ℝ) ^ d) := L_upper
            have htl : 4 * (K : ℝ) * ((d : ℝ) + 1) ≤ (t : ℝ) / L := by
              have : 4 * (K : ℝ) * ((d : ℝ) + 1) * L ≤ (t : ℝ) := by
                have hk0 : 0 ≤ 4 * (K : ℝ) * ((d : ℝ) + 1) := by positivity
                calc 4 * (K : ℝ) * ((d : ℝ) + 1) * L
                    ≤ 4 * (K : ℝ) * ((d : ℝ) + 1) * (2 * Real.sqrt ((2 : ℝ) ^ d)) :=
                      mul_le_mul_of_nonneg_left hL2s hk0
                  _ = 8 * (K : ℝ) * ((d : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ d) := by ring
                  _ ≤ (t : ℝ) := htg
              exact (le_div_iff₀ hLpos).mpr this
            have hk_le : (K : ℝ) ≤ (t : ℝ) / L := by
              have : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg _]
              nlinarith [show (0 : ℝ) ≤ (K : ℝ) from Nat.cast_nonneg _]
            have hdiv : 3 * ((t : ℝ) / L) ≤ ((n - m : ℕ) : ℝ) / L := by
              rw [show 3 * ((t : ℝ) / L) = (3 * (t : ℝ)) / L by ring]
              exact div_le_div_of_nonneg_right hnm hLpos.le
            have hneg : -2 * ((n - m : ℕ) : ℝ) / L = -2 * (((n - m : ℕ) : ℝ) / L) := by ring
            rw [hneg]
            linarith
    exact mul_le_mul hc hexp_b (pow_nonneg (div_nonneg (abs_nonneg _) hLpos.le) _) (by norm_num)
  have ht12 : (8 * (m : ℝ) + 2) * ((L + 1) / (n : ℝ)) < δ / 2 := by
    have hm_le : 8 * (m : ℝ) + 2 ≤ 8 * ((m : ℝ) + 1) := by linarith
    have hn_nonneg : 0 ≤ (L + 1) / (n : ℝ) := by positivity
    calc (8 * (m : ℝ) + 2) * ((L + 1) / (n : ℝ))
        ≤ 8 * ((m : ℝ) + 1) * ((L + 1) / (n : ℝ)) := mul_le_mul_of_nonneg_right hm_le hn_nonneg
      _ < 8 * ((m : ℝ) + 1) * (δ / (16 * ((m : ℝ) + 1))) := by
          apply mul_lt_mul_of_pos_left hLnt (by positivity)
      _ = δ / 2 := by field_simp [show ((m : ℝ) + 1) ≠ 0 by positivity]; ring
  linarith

lemma markov_sq {n : ℕ} (r : ℝ) (hr : 0 ≤ r) (f : Finset (Fin n) → ℝ) {c : ℝ} (hc : 0 < c)
    (P : Finset (Fin n) → Prop) [DecidablePred P] (hP : ∀ S, P S → c < |f S|) :
    (∑ S ∈ Finset.univ.filter P, wt r S) ≤
      (1 / c ^ 2) * ∑ S : Finset (Fin n), wt r S * (f S) ^ 2 := by
  rw [Finset.mul_sum]
  calc ∑ S ∈ Finset.univ.filter P, wt r S
      ≤ ∑ S ∈ Finset.univ.filter P, (1 / c ^ 2) * (wt r S * (f S) ^ 2) := by
        refine Finset.sum_le_sum fun S hS => ?_
        have hlt : c < |f S| := hP S (Finset.mem_filter.mp hS).2
        have hsq : c ^ 2 ≤ (f S) ^ 2 := by
          rw [← sq_abs (f S)]
          exact pow_le_pow_left₀ hc.le hlt.le 2
        have h1 : 1 ≤ (1 / c ^ 2) * (f S) ^ 2 := by
          rw [one_div, mul_comm, ← div_eq_mul_inv, one_le_div (sq_pos_of_pos hc)]
          exact hsq
        calc wt r S = wt r S * 1 := (mul_one _).symm
          _ ≤ wt r S * ((1 / c ^ 2) * (f S) ^ 2) := mul_le_mul_of_nonneg_left h1 (wt_nonneg hr S)
          _ = (1 / c ^ 2) * (wt r S * (f S) ^ 2) := by ring
    _ ≤ ∑ S : Finset (Fin n), (1 / c ^ 2) * (wt r S * (f S) ^ 2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun S _ _ => ?_
        exact mul_nonneg (by positivity) (mul_nonneg (wt_nonneg hr S) (sq_nonneg _))

noncomputable def goodS (d t : ℕ) (L₀ : ℝ) (M : ℕ) (η : ℝ) (S : Finset (Fin (6 * t))) : Prop :=
  let n := 6 * t
  let r := Real.sqrt (Join.q d)
  let L := Join.L d
  if L₀ ≤ L then
    |((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)| ≤ η / 6 ∧
    2 * ((L + 1) / (n : ℝ)) * (patCount [false, false, false] S : ℝ) ≤ η / 6
  else
    |((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)| ≤ η / 12 ∧
    (∀ m ∈ Finset.Icc 1 M,
      2 * ((L + 1) / (n : ℝ)) *
        |(patCount (true :: List.replicate (2 * m + 1) false) S : ℝ) -
          (n : ℝ) * r / (2 * L ^ (2 * m + 1))| ≤ η / (12 * ((M : ℝ) + 1))) ∧
    2 * ((L + 1) / (n : ℝ)) *
      |(patCount (List.replicate (2 * M + 3) false) S : ℝ) - (n : ℝ) / (2 * L ^ (2 * M + 2))| ≤
      η / 12

lemma goodS_implies_typical {d t : ℕ} (ht : 1 ≤ t) (hd : 2 ≤ d)
    {L₀ η : ℝ} {M : ℕ} (hη0 : 0 < η) (hηhalf : η ≤ 1 / 2) (hL0_ge : 24 / η ≤ L₀)
    (hM : (L₀ + 1) / (2 : ℝ) ^ (2 * M + 2) + 1 / (2 : ℝ) ^ (2 * M + 1) ≤ η / 6)
    (hstep : 8 * (Join.L d + 1) / ((6 * t : ℕ) : ℝ) ≤ η / 2)
    (S : Finset (Fin (6 * t))) (hS : S.Nonempty) (hgood : goodS d t L₀ M η S)
    {hU : ℕ} (hlo : (HostDim.oddZSet S hS).card - 4 ≤ hU)
    (hhi : hU ≤ (HostDim.oddZSet S hS).card) :
    |2 * (Join.L d + 1) * (((3 * t - hU : ℕ) : ℝ)) / ((6 * t : ℕ) : ℝ) - 1| ≤ η := by
  let n := 6 * t
  let a := 3 * t
  let r := Real.sqrt (Join.q d)
  let L := Join.L d
  obtain ⟨hL2, hr1⟩ := L_lower hd
  have hrpos : 0 < r := by linarith
  have hLpos : 0 < L := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hoz := Patterns.oddZSet_card_eq S hS
  have h2r := Transfer.two_runs_add_nonBdry (by omega : 1 < n) S
  have haoz : 2 * ((a : ℝ) - ((HostDim.oddZSet S hS).card : ℝ)) =
      (nonBdry S : ℝ) - 2 * ((Patterns.remOdd S hS).card : ℝ) := by
    have hnat : 2 * a + 2 * (Patterns.remOdd S hS).card =
        2 * (HostDim.oddZSet S hS).card + nonBdry S := by
      have ha2 : 2 * a = n := by omega
      omega
    have hreal : 2 * (a : ℝ) + 2 * ((Patterns.remOdd S hS).card : ℝ) =
        2 * ((HostDim.oddZSet S hS).card : ℝ) + (nonBdry S : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hnorm_oz : 2 * (L + 1) * ((a : ℝ) - ((HostDim.oddZSet S hS).card : ℝ)) / (n : ℝ) =
      ((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - 2 * ((Patterns.remOdd S hS).card : ℝ)) := by
    rw [show 2 * (L + 1) * ((a : ℝ) - ((HostDim.oddZSet S hS).card : ℝ)) / (n : ℝ) =
      ((L + 1) / (n : ℝ)) * (2 * ((a : ℝ) - ((HostDim.oddZSet S hS).card : ℝ))) by ring, haoz]
  have hclose : |2 * (L + 1) * ((a : ℝ) - ((HostDim.oddZSet S hS).card : ℝ)) / (n : ℝ) - 1| ≤ η / 2 := by
    rw [hnorm_oz]
    by_cases hLcase : L₀ ≤ L
    · have hg := hgood
      unfold goodS at hg
      rw [if_pos hLcase] at hg
      rcases hg with ⟨hx0, hpat0⟩
      have hrem : ((Patterns.remOdd S hS).card : ℝ) ≤ (patCount [false, false, false] S : ℝ) := by
        exact_mod_cast (by simpa using (Patterns.remOdd_bounds S hS 0).2 :
          (Patterns.remOdd S hS).card ≤ patCount [false, false, false] S)
      have hrem_nn : 0 ≤ ((Patterns.remOdd S hS).card : ℝ) := Nat.cast_nonneg _
      have hfac_nn : 0 ≤ 2 * ((L + 1) / (n : ℝ)) := by positivity
      have hrem_le : 2 * ((L + 1) / (n : ℝ)) * ((Patterns.remOdd S hS).card : ℝ) ≤ η / 6 :=
        (mul_le_mul_of_nonneg_left hrem hfac_nn).trans hpat0
      have h1L : |(L + 1) / L - 1| ≤ η / 6 := by
        have hid : (L + 1) / L - 1 = 1 / L := by field_simp [hLpos.ne']; ring
        rw [hid, abs_of_nonneg (by positivity)]
        have hL24 : 24 / η ≤ L := hL0_ge.trans hLcase
        have h6 : (η / 6)⁻¹ = 6 / η := by ring
        have h6le : 6 / η ≤ 24 / η := div_le_div_of_nonneg_right (by norm_num) hη0.le
        rw [one_div, inv_le_comm₀ hLpos (by positivity), h6]
        linarith
      have hdecomp : ((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - 2 * ((Patterns.remOdd S hS).card : ℝ)) - 1 =
          (((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)) + ((L + 1) / L - 1) -
            2 * ((L + 1) / (n : ℝ)) * ((Patterns.remOdd S hS).card : ℝ) := by
        field_simp [hLpos.ne', hnpos.ne']; ring
      rw [hdecomp]
      calc |_ - _| ≤ |((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L) + ((L + 1) / L - 1)| +
              |2 * ((L + 1) / (n : ℝ)) * ((Patterns.remOdd S hS).card : ℝ)| := abs_sub _ _
        _ ≤ |((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)| + |(L + 1) / L - 1| +
              |2 * ((L + 1) / (n : ℝ)) * ((Patterns.remOdd S hS).card : ℝ)| := by
            linarith [abs_add_le (((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)) ((L + 1) / L - 1)]
        _ ≤ η / 6 + η / 6 + η / 6 := by
            rw [abs_of_nonneg (mul_nonneg hfac_nn hrem_nn)]
            linarith
        _ = η / 2 := by ring
    · have hg := hgood
      unfold goodS at hg
      rw [if_neg hLcase] at hg
      rcases hg with ⟨hx0, hpatM, htail⟩
      have hLlt : L < L₀ := lt_of_not_ge hLcase
      have hremB := Patterns.remOdd_bounds S hS M
      let headSum : ℝ :=
        ∑ m ∈ Finset.Icc 1 M, (patCount (true :: List.replicate (2 * m + 1) false) S : ℝ)
      let tailR : ℝ := (patCount (List.replicate (2 * M + 3) false) S : ℝ)
      have hhead_le : headSum ≤ ((Patterns.remOdd S hS).card : ℝ) := by
        dsimp [headSum]; rw [← Nat.cast_sum]; exact Nat.cast_le.mpr hremB.1
      have hhead_up : ((Patterns.remOdd S hS).card : ℝ) ≤ headSum + tailR := by
        dsimp [headSum, tailR]; rw [← Nat.cast_sum, ← Nat.cast_add]; exact Nat.cast_le.mpr hremB.2
      have hrem_diff : |((Patterns.remOdd S hS).card : ℝ) - headSum| ≤ tailR := by
        rw [abs_le]; constructor <;> linarith
      let μhead : ℝ := ∑ m ∈ Finset.Icc 1 M, (n : ℝ) * r / (2 * L ^ (2 * m + 1))
      have hgeom : 2 * ((L + 1) / (n : ℝ)) * μhead = (1 - 1 / L ^ (2 * M)) / L := by
        dsimp [μhead]
        rw [Finset.mul_sum]
        have hterm (m : ℕ) : 2 * ((L + 1) / (n : ℝ)) * ((n : ℝ) * r / (2 * L ^ (2 * m + 1))) =
            (L + 1) * (r / L ^ (2 * m + 1)) := by
          field_simp [hnpos.ne', pow_ne_zero (2 * m + 1) hLpos.ne']
        simp_rw [hterm, ← Finset.mul_sum]
        have hLdef : 1 + r = L := rfl
        rw [← hLdef, geom_sum_remOdd hrpos M, hLdef]
        have hL10 : L + 1 ≠ 0 := by linarith
        field_simp [hLpos.ne', hL10]
      have hhead_err : |2 * ((L + 1) / (n : ℝ)) * (headSum - μhead)| ≤ η / 12 := by
        have heq : 2 * ((L + 1) / (n : ℝ)) * (headSum - μhead) =
            ∑ m ∈ Finset.Icc 1 M, 2 * ((L + 1) / (n : ℝ)) *
              ((patCount (true :: List.replicate (2 * m + 1) false) S : ℝ) -
                (n : ℝ) * r / (2 * L ^ (2 * m + 1))) := by
          dsimp [headSum, μhead]
          rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        rw [heq]
        calc |∑ m ∈ Finset.Icc 1 M, _|
            ≤ ∑ m ∈ Finset.Icc 1 M, |2 * ((L + 1) / (n : ℝ)) *
                ((patCount (true :: List.replicate (2 * m + 1) false) S : ℝ) -
                  (n : ℝ) * r / (2 * L ^ (2 * m + 1)))| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _m ∈ Finset.Icc 1 M, η / (12 * ((M : ℝ) + 1)) := by
              refine Finset.sum_le_sum fun m hm => ?_
              rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * ((L + 1) / (n : ℝ)))]
              exact hpatM m hm
          _ = (M : ℝ) * (η / (12 * ((M : ℝ) + 1))) := by
              have hcard : (Finset.Icc 1 M).card = M := by simp
              rw [Finset.sum_const, hcard, nsmul_eq_mul]
          _ ≤ η / 12 := by
              have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
              have hle1 : (M : ℝ) / ((M : ℝ) + 1) ≤ 1 := (div_le_one hMpos).mpr (by linarith)
              calc (M : ℝ) * (η / (12 * ((M : ℝ) + 1)))
                  = ((M : ℝ) / ((M : ℝ) + 1)) * (η / 12) := by field_simp [hMpos.ne']
                _ ≤ 1 * (η / 12) := mul_le_mul_of_nonneg_right hle1 (by positivity)
                _ = η / 12 := one_mul _
      have htail_le : 2 * ((L + 1) / (n : ℝ)) * tailR ≤ η / 12 + (L₀ + 1) / (2 : ℝ) ^ (2 * M + 2) := by
        have h1 : 2 * ((L + 1) / (n : ℝ)) * tailR ≤
            2 * ((L + 1) / (n : ℝ)) * |tailR - (n : ℝ) / (2 * L ^ (2 * M + 2))| +
              2 * ((L + 1) / (n : ℝ)) * ((n : ℝ) / (2 * L ^ (2 * M + 2))) := by
          have htri : tailR ≤ |tailR - (n : ℝ) / (2 * L ^ (2 * M + 2))| + (n : ℝ) / (2 * L ^ (2 * M + 2)) := by
            linarith [le_abs_self (tailR - (n : ℝ) / (2 * L ^ (2 * M + 2)))]
          have hmul := mul_le_mul_of_nonneg_left htri (by positivity : 0 ≤ 2 * ((L + 1) / (n : ℝ)))
          linarith
        have h2 : 2 * ((L + 1) / (n : ℝ)) * ((n : ℝ) / (2 * L ^ (2 * M + 2))) =
            (L + 1) / L ^ (2 * M + 2) := by
          field_simp [hnpos.ne', pow_ne_zero (2 * M + 2) hLpos.ne']
        have h3 : (L + 1) / L ^ (2 * M + 2) ≤ (L₀ + 1) / (2 : ℝ) ^ (2 * M + 2) := by
          have hpow : (2 : ℝ) ^ (2 * M + 2) ≤ L ^ (2 * M + 2) :=
            pow_le_pow_left₀ (by norm_num) hL2.le _
          exact div_le_div₀ (by linarith) (by linarith) (by positivity) hpow
        linarith
      have hpow1_le : 1 / L ^ (2 * M + 1) ≤ 1 / (2 : ℝ) ^ (2 * M + 1) := by
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by norm_num) hL2.le _)
      have hmean_id : ((L + 1) / (n : ℝ)) * ((n : ℝ) / L) - 2 * ((L + 1) / (n : ℝ)) * μhead =
          1 + 1 / L ^ (2 * M + 1) := by
        rw [hgeom]
        have hp : L ^ (2 * M + 1) = L ^ (2 * M) * L := by rw [pow_succ]
        field_simp [hnpos.ne', hLpos.ne', pow_ne_zero (2 * M) hLpos.ne', pow_ne_zero (2 * M + 1) hLpos.ne']
        rw [hp]; ring
      have hdecomp : ((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - 2 * ((Patterns.remOdd S hS).card : ℝ)) - 1 =
          (((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)) -
            2 * ((L + 1) / (n : ℝ)) * (((Patterns.remOdd S hS).card : ℝ) - headSum) -
            2 * ((L + 1) / (n : ℝ)) * (headSum - μhead) + 1 / L ^ (2 * M + 1) := by
        have hdiff : ((L + 1) / (n : ℝ)) * ((n : ℝ) / L) - 2 * ((L + 1) / (n : ℝ)) * μhead - 1 =
            1 / L ^ (2 * M + 1) := by linarith [hmean_id]
        linarith
      have hrem_abs : |2 * ((L + 1) / (n : ℝ)) * (((Patterns.remOdd S hS).card : ℝ) - headSum)| ≤
          2 * ((L + 1) / (n : ℝ)) * tailR := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * ((L + 1) / (n : ℝ)))]
        exact mul_le_mul_of_nonneg_left hrem_diff (by positivity)
      rw [hdecomp]
      calc |_ + _|
          ≤ |((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)| +
              |2 * ((L + 1) / (n : ℝ)) * (((Patterns.remOdd S hS).card : ℝ) - headSum)| +
              |2 * ((L + 1) / (n : ℝ)) * (headSum - μhead)| + |1 / L ^ (2 * M + 1)| := by
            have t1 := abs_add_le (((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L) -
              2 * ((L + 1) / (n : ℝ)) * (((Patterns.remOdd S hS).card : ℝ) - headSum) -
              2 * ((L + 1) / (n : ℝ)) * (headSum - μhead)) (1 / L ^ (2 * M + 1))
            have t2 := abs_sub (((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L) -
              2 * ((L + 1) / (n : ℝ)) * (((Patterns.remOdd S hS).card : ℝ) - headSum))
              (2 * ((L + 1) / (n : ℝ)) * (headSum - μhead))
            have t3 := abs_sub (((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L))
              (2 * ((L + 1) / (n : ℝ)) * (((Patterns.remOdd S hS).card : ℝ) - headSum))
            linarith
        _ ≤ η / 12 + (η / 12 + (L₀ + 1) / (2 : ℝ) ^ (2 * M + 2)) + η / 12 + 1 / (2 : ℝ) ^ (2 * M + 1) := by
            rw [abs_of_nonneg (by positivity : 0 ≤ 1 / L ^ (2 * M + 1))]
            linarith
        _ ≤ η / 2 := by linarith
  have hpos_oz : (0 : ℝ) < (a : ℝ) - ((HostDim.oddZSet S hS).card : ℝ) := by
    have hge : 1 - η / 2 ≤ 2 * (L + 1) * ((a : ℝ) - ((HostDim.oddZSet S hS).card : ℝ)) / (n : ℝ) :=
      (abs_le.mp hclose).1 |> fun h => by linarith
    have h34 : (0 : ℝ) < 2 * (L + 1) * ((a : ℝ) - ((HostDim.oddZSet S hS).card : ℝ)) / (n : ℝ) := by
      linarith
    have hfac : 0 < 2 * (L + 1) / (n : ℝ) := by positivity
    nlinarith [show 2 * (L + 1) * ((a : ℝ) - ((HostDim.oddZSet S hS).card : ℝ)) / (n : ℝ) =
      (2 * (L + 1) / (n : ℝ)) * ((a : ℝ) - ((HostDim.oddZSet S hS).card : ℝ)) by ring]
  have hoz_le_a : (HostDim.oddZSet S hS).card ≤ a := by
    have : ((HostDim.oddZSet S hS).card : ℝ) < (a : ℝ) := by linarith
    exact Nat.le_of_lt (by exact_mod_cast this)
  have hhU_le_a : hU ≤ a := hhi.trans hoz_le_a
  rw [Nat.cast_sub hhU_le_a]
  have hdiff_hU : |2 * (L + 1) * ((a : ℝ) - (hU : ℝ)) / (n : ℝ) -
      2 * (L + 1) * ((a : ℝ) - ((HostDim.oddZSet S hS).card : ℝ)) / (n : ℝ)| ≤ η / 2 := by
    have hid : 2 * (L + 1) * ((a : ℝ) - (hU : ℝ)) / (n : ℝ) -
        2 * (L + 1) * ((a : ℝ) - ((HostDim.oddZSet S hS).card : ℝ)) / (n : ℝ) =
        2 * (L + 1) / (n : ℝ) * (((HostDim.oddZSet S hS).card : ℝ) - (hU : ℝ)) := by ring
    rw [hid, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (L + 1) / (n : ℝ))]
    have h4 : |((HostDim.oddZSet S hS).card : ℝ) - (hU : ℝ)| ≤ 4 := by
      rw [abs_le]
      have hhiR : (hU : ℝ) ≤ ((HostDim.oddZSet S hS).card : ℝ) := by exact_mod_cast hhi
      have hloR : ((HostDim.oddZSet S hS).card : ℝ) - 4 ≤ (hU : ℝ) := by
        have : (HostDim.oddZSet S hS).card ≤ hU + 4 := by omega
        have : ((HostDim.oddZSet S hS).card : ℝ) ≤ (hU : ℝ) + 4 := by exact_mod_cast this
        linarith
      constructor <;> linarith
    calc 2 * (L + 1) / (n : ℝ) * |((HostDim.oddZSet S hS).card : ℝ) - (hU : ℝ)|
        ≤ 2 * (L + 1) / (n : ℝ) * 4 := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 8 * (L + 1) / (n : ℝ) := by ring
      _ ≤ η / 2 := hstep
  have hadd : (2 * (L + 1) * ((a : ℝ) - (hU : ℝ)) / (n : ℝ) - 1) =
      (2 * (L + 1) * ((a : ℝ) - (hU : ℝ)) / (n : ℝ) -
        2 * (L + 1) * ((a : ℝ) - ((HostDim.oddZSet S hS).card : ℝ)) / (n : ℝ)) +
      (2 * (L + 1) * ((a : ℝ) - ((HostDim.oddZSet S hS).card : ℝ)) / (n : ℝ) - 1) := by ring
  change |2 * (L + 1) * ((a : ℝ) - (hU : ℝ)) / (n : ℝ) - 1| ≤ η
  rw [hadd]
  exact (abs_add_le _ _).trans (by linarith [hdiff_hU, hclose])

lemma bad_weight_tendsto (D : ℕ → ℕ) (hD : ∀ t, 2 ≤ D t)
    (hgrowth : Filter.Tendsto (fun t : ℕ => ((D t : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ (D t)) / (t : ℝ))
      Filter.atTop (nhds 0))
    {L₀ η : ℝ} (hη0 : 0 < η) (hL0_ge : 24 / η ≤ L₀) (M : ℕ) :
    Filter.Tendsto (fun t : ℕ =>
      letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      let d := D t
      let n := 6 * t
      let r := Real.sqrt (Join.q d)
      let L := Join.L d
      (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ¬ goodS d t L₀ M η S),
        wt r S) / L ^ n) Filter.atTop (nhds 0) := by
  let w0 : List Bool := [false, false, false]
  let wM (m : ℕ) : List Bool := true :: List.replicate (2 * m + 1) false
  let wTail : List Bool := List.replicate (2 * M + 3) false
  have hpatM_aux : ∀ m, 1 ≤ m → ∀ r : ℝ, patW r (wM m) = r := fun m hm1 r =>
    patW_true_replicate_false r (2 * m + 1) (by omega)
  have hX0 := var_X0_div_tendsto D hD hgrowth
  have hw0 := var_pat_div_tendsto D hD hgrowth w0 (by decide) (fun d hd => by
    dsimp only
    have : patW (Real.sqrt (Join.q d)) w0 = 1 := patW_replicate_false _ 3
    rw [this]; obtain ⟨hL2, _⟩ := L_lower hd; exact ⟨by norm_num, by linarith⟩)
  have hwM : ∀ m ∈ Finset.Icc 1 M, Filter.Tendsto (fun t : ℕ =>
      let d := D t; let n := 6 * t; let r := Real.sqrt (Join.q d); let L := Join.L d
      let μ := (n : ℝ) * patW r (wM m) / (2 * L ^ ((wM m).length - 1))
      (∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) * ((patCount (wM m) S : ℝ) - μ)) ^ 2) / L ^ n)
      Filter.atTop (nhds 0) := fun m hm =>
    var_pat_div_tendsto D hD hgrowth (wM m) (by
      have hm1 := (Finset.mem_Icc.mp hm).1
      have : (wM m).length = 2 * m + 2 := by simp [wM]
      omega) (fun d hd => by
      have hm1 := (Finset.mem_Icc.mp hm).1
      dsimp only
      have : patW (Real.sqrt (Join.q d)) (wM m) = Real.sqrt (Join.q d) :=
        hpatM_aux m hm1 (Real.sqrt (Join.q d))
      rw [this]; obtain ⟨_, hr1⟩ := L_lower hd
      exact ⟨by linarith, by unfold Join.L; linarith⟩)
  have hwTail := var_pat_div_tendsto D hD hgrowth wTail (by simp [wTail]) (fun d hd => by
    dsimp only
    have : patW (Real.sqrt (Join.q d)) wTail = 1 := patW_replicate_false _ (2 * M + 3)
    rw [this]; obtain ⟨hL2, _⟩ := L_lower hd; exact ⟨by norm_num, by linarith⟩)
  let Ftot : ℕ → ℝ := fun t =>
    let d := D t; let n := 6 * t; let r := Real.sqrt (Join.q d); let L := Join.L d
    (12 / η) ^ 2 *
      ((∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)) ^ 2) / L ^ n) +
    (24 / η) ^ 2 *
      ((∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) *
        ((patCount w0 S : ℝ) - (n : ℝ) * patW r w0 / (2 * L ^ (w0.length - 1)))) ^ 2) / L ^ n) +
    (∑ m ∈ Finset.Icc 1 M, (24 * ((M : ℝ) + 1) / η) ^ 2 *
      ((∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) *
        ((patCount (wM m) S : ℝ) - (n : ℝ) * patW r (wM m) / (2 * L ^ ((wM m).length - 1)))) ^ 2) / L ^ n)) +
    (24 / η) ^ 2 *
      ((∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) *
        ((patCount wTail S : ℝ) - (n : ℝ) * patW r wTail / (2 * L ^ (wTail.length - 1)))) ^ 2) / L ^ n)
  have hFtend : Filter.Tendsto Ftot Filter.atTop (nhds 0) := by
    have t1 := (tendsto_const_nhds (x := (12 / η) ^ 2)).mul hX0
    have t2 := (tendsto_const_nhds (x := (24 / η) ^ 2)).mul hw0
    have t3_aux : ∀ s : Finset ℕ, s ⊆ Finset.Icc 1 M →
        Filter.Tendsto (fun t : ℕ => ∑ m ∈ s,
          (24 * ((M : ℝ) + 1) / η) ^ 2 *
            ((∑ S : Finset (Fin (6 * t)), wt (Real.sqrt (Join.q (D t))) S *
              (((Join.L (D t) + 1) / ((6 * t : ℕ) : ℝ)) *
                ((patCount (wM m) S : ℝ) - (6 * t : ℝ) * patW (Real.sqrt (Join.q (D t))) (wM m) /
                  (2 * (Join.L (D t)) ^ ((wM m).length - 1)))) ^ 2) / (Join.L (D t)) ^ (6 * t)))
          Filter.atTop (nhds 0) := by
      intro s hs
      induction s using Finset.induction_on with
      | empty => simp
      | @insert m s hm ih =>
        have hmem : m ∈ Finset.Icc 1 M := hs (Finset.mem_insert_self m s)
        have hsub : s ⊆ Finset.Icc 1 M := fun x hx => hs (Finset.mem_insert_of_mem hx)
        have hm_t := (tendsto_const_nhds (x := (24 * ((M : ℝ) + 1) / η) ^ 2)).mul (hwM m hmem)
        simpa [Finset.sum_insert hm] using hm_t.add (ih hsub)
    have t3 := t3_aux (Finset.Icc 1 M) Finset.Subset.rfl
    have t4 := (tendsto_const_nhds (x := (24 / η) ^ 2)).mul hwTail
    simpa [Ftot] using ((t1.add t2).add t3).add t4
  have hη12 : 0 < η / 12 := by positivity
  have hη24 : 0 < η / 24 := by positivity
  have hηM : 0 < η / (24 * ((M : ℝ) + 1)) := by positivity
  have hc1 : 1 / (η / 12) ^ 2 = (12 / η) ^ 2 := by ring
  have hc2 : 1 / (η / 24) ^ 2 = (24 / η) ^ 2 := by ring
  have hc3 : 1 / (η / (24 * ((M : ℝ) + 1))) ^ 2 = (24 * ((M : ℝ) + 1) / η) ^ 2 := by
    field_simp [hη0.ne']
  have hdiv2_aux : η / (12 * ((M : ℝ) + 1)) = 2 * (η / (24 * ((M : ℝ) + 1))) := by
    field_simp; ring
  have h11_aux : ∀ L x : ℝ, x ≠ 0 → L ≠ 0 →
      ((L + 1) / x) * (x * 1 / (2 * L ^ 2)) = (L + 1) / (2 * L ^ 2) := fun L x hx hL => by
    field_simp
  have htwo_pos : (0 : ℝ) < 2 := by norm_num
  have hlen0 : w0.length - 1 = 2 := by simp [w0]
  have hlenM_fn : ∀ m, (wM m).length - 1 = 2 * m + 1 := fun m => by simp [wM]
  have hlenT : wTail.length - 1 = 2 * M + 2 := by simp [wTail]
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hFtend ?_ ?_
  · refine Filter.Eventually.of_forall fun t => ?_
    dsimp only
    obtain ⟨hL2, hr1⟩ := L_lower (hD t)
    have hr0 : 0 ≤ Real.sqrt (Join.q (D t)) := by linarith
    have hLnpos : 0 ≤ Join.L (D t) ^ (6 * t) := pow_nonneg (by linarith) _
    exact div_nonneg (Finset.sum_nonneg fun S _ => wt_nonneg hr0 S) hLnpos
  · filter_upwards [Filter.eventually_ge_atTop 1] with t ht1
    dsimp only [Ftot]
    let d := D t; let n := 6 * t; let r := Real.sqrt (Join.q d); let L := Join.L d
    obtain ⟨hL2, hr1⟩ := L_lower (hD t)
    have hr0 : 0 ≤ r := by linarith
    have hLpos : 0 < L := by linarith
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      dsimp [n]
      exact_mod_cast Nat.mul_pos (by norm_num) ht1
    have hLnpos : 0 < L ^ n := pow_pos hLpos n
    let PX0 (S : Finset (Fin n)) : Prop := η / 12 < |((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)|
    let P0 (S : Finset (Fin n)) : Prop := η / 24 < |((L + 1) / (n : ℝ)) *
      ((patCount w0 S : ℝ) - (n : ℝ) * patW r w0 / (2 * L ^ (w0.length - 1)))|
    let PM (m : ℕ) (S : Finset (Fin n)) : Prop := η / (24 * ((M : ℝ) + 1)) < |((L + 1) / (n : ℝ)) *
      ((patCount (wM m) S : ℝ) - (n : ℝ) * patW r (wM m) / (2 * L ^ ((wM m).length - 1)))|
    let PT (S : Finset (Fin n)) : Prop := η / 24 < |((L + 1) / (n : ℝ)) *
      ((patCount wTail S : ℝ) - (n : ℝ) * patW r wTail / (2 * L ^ (wTail.length - 1)))|
    have hsub : (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ¬ goodS d t L₀ M η S) ⊆
        Finset.univ.filter PX0 ∪ (Finset.univ.filter P0 ∪
          ((Finset.Icc 1 M).biUnion (fun m => Finset.univ.filter (PM m)) ∪ Finset.univ.filter PT)) := by
      intro S hS
      have hnot := (Finset.mem_filter.mp hS).2
      unfold goodS at hnot
      by_cases hLcase : L₀ ≤ L
      · rw [if_pos hLcase] at hnot
        push_neg at hnot
        by_cases h1 : η / 6 < |((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)|
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by linarith⟩)
        · have h2 := hnot (not_lt.mp h1)
          have hw0eq : patW r w0 = 1 := patW_replicate_false r 3
          have hμ_le : ((L + 1) / (n : ℝ)) * ((n : ℝ) * patW r w0 / (2 * L ^ (w0.length - 1))) ≤ η / 24 := by
            rw [hw0eq, hlen0]
            have h11 : ((L + 1) / (n : ℝ)) * ((n : ℝ) * 1 / (2 * L ^ 2)) = (L + 1) / (2 * L ^ 2) :=
              h11_aux L (n : ℝ) hnpos.ne' hLpos.ne'
            rw [h11]
            have hL12 : L + 1 ≤ 2 * L := by linarith
            have h2L : (L + 1) / (2 * L ^ 2) ≤ 1 / L := by
              rw [div_le_div_iff₀ (mul_pos htwo_pos (pow_pos hLpos 2)) hLpos]
              nlinarith
            have hinv : 1 / L ≤ η / 24 := by
              have hL24 : 24 / η ≤ L := hL0_ge.trans hLcase
              have h24 : (η / 24)⁻¹ = 24 / η := by ring
              rw [one_div, inv_le_comm₀ hLpos hη24, h24]
              linarith
            linarith
          have hlt0 : η / 12 < ((L + 1) / (n : ℝ)) * (patCount w0 S : ℝ) := by dsimp [w0]; linarith
          have hP0 : P0 S := by
            dsimp [P0]
            have hdiff : η / 24 < ((L + 1) / (n : ℝ)) *
                ((patCount w0 S : ℝ) - (n : ℝ) * patW r w0 / (2 * L ^ (w0.length - 1))) := by
              have hid : ((L + 1) / (n : ℝ)) *
                  ((patCount w0 S : ℝ) - (n : ℝ) * patW r w0 / (2 * L ^ (w0.length - 1))) =
                  ((L + 1) / (n : ℝ)) * (patCount w0 S : ℝ) -
                    ((L + 1) / (n : ℝ)) * ((n : ℝ) * patW r w0 / (2 * L ^ (w0.length - 1))) := by ring
              linarith
            exact lt_of_lt_of_le hdiff (le_abs_self _)
          exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP0⟩))
      · rw [if_neg hLcase] at hnot
        by_cases h1 : η / 12 < |((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)|
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
        · have h1' := not_lt.mp h1
          by_cases h2 : ∃ m ∈ Finset.Icc 1 M,
              η / (12 * ((M : ℝ) + 1)) < 2 * ((L + 1) / (n : ℝ)) *
                |(patCount (wM m) S : ℝ) - (n : ℝ) * r / (2 * L ^ (2 * m + 1))|
          · rcases h2 with ⟨m, hm, hmgt⟩
            have hm1 := (Finset.mem_Icc.mp hm).1
            have hwMeq : patW r (wM m) = r := hpatM_aux m hm1 r
            have hlenM : (wM m).length - 1 = 2 * m + 1 := hlenM_fn m
            have hPM : PM m S := by
              change η / (24 * ((M : ℝ) + 1)) < |((L + 1) / (n : ℝ)) *
                ((patCount (wM m) S : ℝ) - (n : ℝ) * patW r (wM m) / (2 * L ^ ((wM m).length - 1)))|
              rw [hwMeq, hlenM, abs_mul, abs_of_nonneg (div_nonneg (by linarith) hnpos.le)]
              have hdiv2 := hdiv2_aux
              linarith
            exact Finset.mem_union_right _ (Finset.mem_union_right _
              (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPM⟩⟩)))
          · have h2' : ∀ m ∈ Finset.Icc 1 M, 2 * ((L + 1) / (n : ℝ)) *
                |(patCount (wM m) S : ℝ) - (n : ℝ) * r / (2 * L ^ (2 * m + 1))| ≤ η / (12 * ((M : ℝ) + 1)) := by
              intro m hm; by_contra! hlt; exact h2 ⟨m, hm, hlt⟩
            have h3 : η / 12 < 2 * ((L + 1) / (n : ℝ)) *
                |(patCount wTail S : ℝ) - (n : ℝ) / (2 * L ^ (2 * M + 2))| := by
              by_contra! h3le; exact hnot ⟨h1', h2', h3le⟩
            have hwTeq : patW r wTail = 1 := patW_replicate_false r (2 * M + 3)
            have hPT : PT S := by
              change η / 24 < |((L + 1) / (n : ℝ)) *
                ((patCount wTail S : ℝ) - (n : ℝ) * patW r wTail / (2 * L ^ (wTail.length - 1)))|
              rw [hwTeq, hlenT, mul_one, abs_mul, abs_of_nonneg (div_nonneg (by linarith) hnpos.le)]
              linarith
            exact Finset.mem_union_right _ (Finset.mem_union_right _
              (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPT⟩)))
    have hsum_union (A B : Finset (Finset (Fin n))) :
        (∑ S ∈ A ∪ B, wt r S) ≤ (∑ S ∈ A, wt r S) + ∑ S ∈ B, wt r S := by
      rw [← Finset.sum_union_inter]
      linarith [Finset.sum_nonneg fun S (_ : S ∈ A ∩ B) => wt_nonneg hr0 S]
    have hsum_biUnion : (∑ S ∈ (Finset.Icc 1 M).biUnion (fun m => Finset.univ.filter (PM m)), wt r S) ≤
        ∑ m ∈ Finset.Icc 1 M, ∑ S ∈ Finset.univ.filter (PM m), wt r S := by
      refine Finset.induction_on (Finset.Icc 1 M) (by simp) fun a s ha ih => ?_
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (hsum_union _ _).trans (add_le_add le_rfl ih)
    have htot : (∑ S ∈ Finset.univ.filter (fun S => ¬ goodS d t L₀ M η S), wt r S) ≤
        (∑ S ∈ Finset.univ.filter PX0, wt r S) + (∑ S ∈ Finset.univ.filter P0, wt r S) +
        (∑ m ∈ Finset.Icc 1 M, ∑ S ∈ Finset.univ.filter (PM m), wt r S) +
        (∑ S ∈ Finset.univ.filter PT, wt r S) := by
      have s0 := Finset.sum_le_sum_of_subset_of_nonneg hsub fun S _ _ => wt_nonneg hr0 S
      have s1 := hsum_union (Finset.univ.filter PX0)
        (Finset.univ.filter P0 ∪ ((Finset.Icc 1 M).biUnion (fun m => Finset.univ.filter (PM m)) ∪ Finset.univ.filter PT))
      have s2 := hsum_union (Finset.univ.filter P0)
        ((Finset.Icc 1 M).biUnion (fun m => Finset.univ.filter (PM m)) ∪ Finset.univ.filter PT)
      have s3 := hsum_union ((Finset.Icc 1 M).biUnion fun m => Finset.univ.filter (PM m)) (Finset.univ.filter PT)
      linarith
    have mX0 := markov_sq r hr0 _ hη12 PX0 (fun S h => h)
    have mP0 := markov_sq r hr0 _ hη24 P0 (fun S h => h)
    have mPM (m : ℕ) := markov_sq r hr0 (fun S => ((L + 1) / (n : ℝ)) *
      ((patCount (wM m) S : ℝ) - (n : ℝ) * patW r (wM m) / (2 * L ^ ((wM m).length - 1))))
      hηM (PM m) (fun S h => h)
    have mPT := markov_sq r hr0 _ hη24 PT (fun S h => h)
    rw [hc1] at mX0
    rw [hc2] at mP0 mPT
    have hsum_mPM : (∑ m ∈ Finset.Icc 1 M, ∑ S ∈ Finset.univ.filter (PM m), wt r S) ≤
        ∑ m ∈ Finset.Icc 1 M, (24 * ((M : ℝ) + 1) / η) ^ 2 *
          ∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) *
            ((patCount (wM m) S : ℝ) - (n : ℝ) * patW r (wM m) / (2 * L ^ ((wM m).length - 1)))) ^ 2 := by
      refine Finset.sum_le_sum fun m _ => ?_
      have hm' := mPM m
      rw [hc3] at hm'
      exact hm'
    have hcomb : (∑ S ∈ Finset.univ.filter PX0, wt r S) + (∑ S ∈ Finset.univ.filter P0, wt r S) +
        (∑ m ∈ Finset.Icc 1 M, ∑ S ∈ Finset.univ.filter (PM m), wt r S) +
        (∑ S ∈ Finset.univ.filter PT, wt r S) ≤
        (12 / η) ^ 2 * (∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)) ^ 2) +
        (24 / η) ^ 2 * (∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) *
          ((patCount w0 S : ℝ) - (n : ℝ) * patW r w0 / (2 * L ^ (w0.length - 1)))) ^ 2) +
        (∑ m ∈ Finset.Icc 1 M, (24 * ((M : ℝ) + 1) / η) ^ 2 *
          ∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) *
            ((patCount (wM m) S : ℝ) - (n : ℝ) * patW r (wM m) / (2 * L ^ ((wM m).length - 1)))) ^ 2) +
        (24 / η) ^ 2 * (∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) *
          ((patCount wTail S : ℝ) - (n : ℝ) * patW r wTail / (2 * L ^ (wTail.length - 1)))) ^ 2) := by
      exact add_le_add (add_le_add (add_le_add mX0 mP0) hsum_mPM) mPT
    have hdiv_all := div_le_div_of_nonneg_right (htot.trans hcomb) hLnpos.le
    have hsplit_div :
        ((12 / η) ^ 2 * (∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)) ^ 2) +
          (24 / η) ^ 2 * (∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) *
            ((patCount w0 S : ℝ) - (n : ℝ) * patW r w0 / (2 * L ^ (w0.length - 1)))) ^ 2) +
          (∑ m ∈ Finset.Icc 1 M, (24 * ((M : ℝ) + 1) / η) ^ 2 *
            ∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) *
              ((patCount (wM m) S : ℝ) - (n : ℝ) * patW r (wM m) / (2 * L ^ ((wM m).length - 1)))) ^ 2) +
          (24 / η) ^ 2 * (∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) *
            ((patCount wTail S : ℝ) - (n : ℝ) * patW r wTail / (2 * L ^ (wTail.length - 1)))) ^ 2)) / L ^ n =
        (12 / η) ^ 2 * ((∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) * ((nonBdry S : ℝ) - (n : ℝ) / L)) ^ 2) / L ^ n) +
        (24 / η) ^ 2 * ((∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) *
          ((patCount w0 S : ℝ) - (n : ℝ) * patW r w0 / (2 * L ^ (w0.length - 1)))) ^ 2) / L ^ n) +
        (∑ m ∈ Finset.Icc 1 M, (24 * ((M : ℝ) + 1) / η) ^ 2 *
          ((∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) *
            ((patCount (wM m) S : ℝ) - (n : ℝ) * patW r (wM m) / (2 * L ^ ((wM m).length - 1)))) ^ 2) / L ^ n)) +
        (24 / η) ^ 2 * ((∑ S : Finset (Fin n), wt r S * (((L + 1) / (n : ℝ)) *
          ((patCount wTail S : ℝ) - (n : ℝ) * patW r wTail / (2 * L ^ (wTail.length - 1)))) ^ 2) / L ^ n) := by
      rw [add_div, add_div, add_div, Finset.sum_div]
      simp only [mul_div_assoc]
    exact hdiv_all.trans_eq hsplit_div

end Asymp

end PEqualNP.Outside.L_lib_927_aux

theorem PEqualNP.Outside.L_lib_927 : (∀ D : ℕ → ℕ, (∀ t, 2 ≤ D t) →
  Filter.Tendsto (fun t : ℕ => ((D t : ℝ)+1)*Real.sqrt ((2 : ℝ)^(D t))/(t : ℝ))
    Filter.atTop (nhds 0) →
  ∀ ε : ℝ, 0 < ε →
  Filter.Tendsto (fun t : ℕ =>
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 6*t
  let a := 3*t
  let W := Fin n → F
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  let next := fun i : Fin n =>
    (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
  let h := fun (i : Fin n) (b : Fin 4) =>
    if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
    then (1:F) else 0
  let good := fun U : Submodule F W =>
    (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
    (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
  let supp := fun U : Submodule F W =>
    Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
  let sites := fun (S : Finset (Fin n)) (p : ℕ) =>
    (S.filter (fun i => i.val % 2 = p)).card
  let spaces := (Finset.univ : Finset (Submodule F W)).filter good
  let mixed := spaces.filter (fun U => 0 < sites (supp U) 0 ∧ 0 < sites (supp U) 1)
  let d := D t
  let layer := mixed.filter (fun U : Submodule F W => Module.finrank F U = d)
  let host := fun U : Submodule F W =>
    (spaces.filter (fun E : Submodule F W => U ≤ E)).sup (fun E => Module.finrank F E)
  let L := 1 + Real.sqrt ((2 : ℝ)^d - 1)
  let typical := layer.filter (fun U : Submodule F W =>
    |2*(L+1)*((a-host U : ℕ) : ℝ)/(n : ℝ)-1| ≤ ε)
  (typical.card : ℝ)/(layer.card : ℝ)) Filter.atTop (nhds 1)) := by
  intro D hD hgrowth ε hε
  let η : ℝ := min ε (1 / 2)
  have hη0 : 0 < η := lt_min hε (by norm_num)
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  have hηε : η ≤ ε := min_le_left _ _
  let L₀ : ℝ := max 10 (24 / η)
  have hL0_ge : 24 / η ≤ L₀ := le_max_right _ _
  have hL0_10 : 10 ≤ L₀ := le_max_left _ _
  have hhalf0 : Filter.Tendsto (fun m : ℕ => (L₀ + 3) * (1 / 2 : ℝ) ^ m) Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨M, hM0⟩ := (hhalf0.eventually (Iio_mem_nhds (by positivity : 0 < η / 6))).exists
  have hM : (L₀ + 1) / (2 : ℝ) ^ (2 * M + 2) + 1 / (2 : ℝ) ^ (2 * M + 1) ≤ η / 6 := by
    have hp1 : (1 / 2 : ℝ) ^ (2 * M + 2) ≤ (1 / 2 : ℝ) ^ M := by
      rw [one_div, inv_pow, inv_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
    have hp2 : (1 / 2 : ℝ) ^ (2 * M + 1) ≤ (1 / 2 : ℝ) ^ M := by
      rw [one_div, inv_pow, inv_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
    have hL0pos : 0 ≤ L₀ + 1 := by linarith
    have hd1 : (L₀ + 1) / (2 : ℝ) ^ (2 * M + 2) = (L₀ + 1) * (1 / 2 : ℝ) ^ (2 * M + 2) := by
      rw [one_div, inv_pow, div_eq_mul_inv]
    have hd2 : (1 : ℝ) / (2 : ℝ) ^ (2 * M + 1) = (1 / 2 : ℝ) ^ (2 * M + 1) := by
      rw [one_div, one_div, inv_pow]
    have hpow0 : 0 ≤ (1 / 2 : ℝ) ^ M := by positivity
    calc (L₀ + 1) / (2 : ℝ) ^ (2 * M + 2) + 1 / (2 : ℝ) ^ (2 * M + 1)
        = (L₀ + 1) * (1 / 2 : ℝ) ^ (2 * M + 2) + (1 / 2 : ℝ) ^ (2 * M + 1) := by rw [hd1, hd2]
      _ ≤ (L₀ + 1) * (1 / 2 : ℝ) ^ M + 2 * (1 / 2 : ℝ) ^ M := by
          linarith [mul_le_mul_of_nonneg_left hp1 hL0pos]
      _ = (L₀ + 3) * (1 / 2 : ℝ) ^ M := by ring
      _ ≤ η / 6 := hM0.le
  let errTot : ℕ → ℝ := fun t =>
    let d := D t; let n := 6 * t
    (1 + 2 * (L_lib_927_aux.Join.M 4 d - 1) * (L_lib_927_aux.Join.L d) ^ n * (L_lib_927_aux.Join.t d) ^ t +
      2 * L_lib_927_aux.Join.M 4 d * L_lib_927_aux.Join.q d * (L_lib_927_aux.Join.L (d - 1)) ^ n +
      2 * ((2 : ℝ) ^ d) ^ (3 * t)) / (L_lib_927_aux.Join.L d) ^ n
  let badW : ℕ → ℝ := fun t =>
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    let d := D t; let n := 6 * t
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ¬ L_lib_927_aux.Asymp.goodS d t L₀ M η S),
      L_lib_927_aux.Transfer.wt (Real.sqrt (L_lib_927_aux.Join.q d)) S) / (L_lib_927_aux.Join.L d) ^ n
  have herr : Filter.Tendsto errTot Filter.atTop (nhds 0) :=
    L_lib_927_aux.Asymp.error_div_L_tendsto D hD hgrowth
  have hbad : Filter.Tendsto badW Filter.atTop (nhds 0) :=
    L_lib_927_aux.Asymp.bad_weight_tendsto D hD hgrowth hη0 hL0_ge M
  have hLn_div : Filter.Tendsto (fun t : ℕ => (L_lib_927_aux.Join.L (D t) + 1) / ((6 * t : ℕ) : ℝ))
      Filter.atTop (nhds 0) :=
    L_lib_927_aux.Asymp.growth_L_div_n_tendsto D hgrowth
  have hlow_tend : Filter.Tendsto (fun t : ℕ => 1 - 2 * (badW t + errTot t)) Filter.atTop (nhds 1) := by
    have hsub : Filter.Tendsto (fun t : ℕ => 2 * (badW t + errTot t)) Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul (hbad.add herr)
    simpa using tendsto_const_nhds.sub hsub
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_tend tendsto_const_nhds ?_ ?_
  · have hev_step : ∀ᶠ t : ℕ in Filter.atTop, 8 * (L_lib_927_aux.Join.L (D t) + 1) / ((6 * t : ℕ) : ℝ) ≤ η / 2 := by
      have h8 : Filter.Tendsto (fun t : ℕ => 8 * ((L_lib_927_aux.Join.L (D t) + 1) / ((6 * t : ℕ) : ℝ)))
          Filter.atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul hLn_div
      filter_upwards [h8.eventually (Iio_mem_nhds (by positivity : 0 < η / 2))] with t ht
      linarith [show 8 * ((L_lib_927_aux.Join.L (D t) + 1) / ((6 * t : ℕ) : ℝ)) =
        8 * (L_lib_927_aux.Join.L (D t) + 1) / ((6 * t : ℕ) : ℝ) by ring]
    have hev_err : ∀ᶠ t : ℕ in Filter.atTop, errTot t ≤ 1 / 2 :=
      herr.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)) |>.mono fun _ h => h.le
    filter_upwards [Filter.eventually_ge_atTop 1, hev_step, hev_err] with t ht1 hstep herr_le
    dsimp only
    have hn_ge3 : 3 ≤ 6 * t := by omega
    have hn_gt1 : 1 < 6 * t := by omega
    have hn_pos : 0 < 6 * t := by omega
    have hdiv2 : 2 * t / 2 = t := by omega
    have hn_even : Even (6 * t) := ⟨3 * t, by omega⟩
    have h1lt2 : 1 < 2 := by omega
    have hhalf_pos : (0 : ℝ) < 1 / 2 := by norm_num
    have hM4pos : 0 < L_lib_927_aux.Join.M 4 (D t) := by
      unfold L_lib_927_aux.Join.M; positivity
    have h2pow_nn : 0 ≤ 2 * ((2 : ℝ) ^ (D t)) ^ (3 * t) := by positivity
    have herr'_aux : ∀ a b : ℝ, b ≠ 0 → a = b * (a / b) := fun a b hb => (mul_div_cancel₀ a hb).symm
    have hmul_div_aux : ∀ a b : ℝ, b ≠ 0 → a = b * a / b := fun a b hb => (mul_div_cancel_left₀ a hb).symm
    have hratio_aux : ∀ x1 y1 c1 d1 : ℝ, c1 ≠ 0 → d1 ≠ 0 → y1 ≠ 0 →
        x1 / y1 = (c1 * x1 / d1) / (c1 * y1 / d1) := fun x1 y1 c1 d1 hc hd hy => by
      field_simp
    have hsub_aux : ∀ x1 y1 z1 : ℝ, z1 ≠ 0 → x1 + y1 = z1 → y1 / z1 = 1 - x1 / z1 :=
      fun x1 y1 z1 hz hxy => by rw [eq_sub_iff_add_eq, ← add_div, add_comm y1 x1, hxy, div_self hz]
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    let F := ZMod 2
    let n := 6 * t
    let a := 3 * t
    let W := Fin n → F
    letI : Fintype (Submodule F W) := Fintype.ofFinite _
    let next := fun i : Fin n =>
      (⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
    let h := fun (i : Fin n) (b : Fin 4) =>
      if i.val % 2 = b.val / 2 ∧ (i.val / 2 % 3 = b.val % 2 ∨ i.val / 2 % 3 = 2)
      then (1 : F) else 0
    let good := fun U : Submodule F W =>
      (∀ x ∈ U, ∀ b : Fin 4, (∑ i, h i b * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
    let supp := fun U : Submodule F W =>
      Finset.univ.filter (fun i : Fin n => ∃ x ∈ U, x i ≠ 0)
    let sites := fun (S : Finset (Fin n)) (p : ℕ) =>
      (S.filter (fun i => i.val % 2 = p)).card
    let spaces := (Finset.univ : Finset (Submodule F W)).filter good
    let mixed := spaces.filter (fun U => 0 < sites (supp U) 0 ∧ 0 < sites (supp U) 1)
    let d := D t
    let layer := mixed.filter (fun U : Submodule F W => Module.finrank F U = d)
    let host := fun U : Submodule F W =>
      (spaces.filter (fun E : Submodule F W => U ≤ E)).sup (fun E => Module.finrank F E)
    let L := 1 + Real.sqrt ((2 : ℝ) ^ d - 1)
    let typical := layer.filter (fun U : Submodule F W =>
      |2 * (L + 1) * ((a - host U : ℕ) : ℝ) / (n : ℝ) - 1| ≤ ε)
    let H := L_lib_927_aux.DualWeight.hCode t
    let r := Real.sqrt (L_lib_927_aux.Join.q d)
    have hd2 : 2 ≤ d := hD t
    obtain ⟨hL2, hr1⟩ := L_lib_927_aux.Asymp.L_lower hd2
    have hLdef : L = L_lib_927_aux.Join.L d := by dsimp [L]; unfold L_lib_927_aux.Join.L L_lib_927_aux.Join.q; rfl
    have hr0 : 0 ≤ r := by linarith
    have hLpos : 0 < L_lib_927_aux.Join.L d := by linarith
    have hLnpos : 0 < (L_lib_927_aux.Join.L d) ^ n := pow_pos hLpos n
    have hBpos : 0 < L_lib_927_aux.Census.B d := by
      unfold L_lib_927_aux.Census.B
      refine Finset.prod_pos fun i hi =>
        Nat.sub_pos_of_lt (Nat.pow_lt_pow_right h1lt2 (Finset.mem_range.mp hi))
    let c : ℝ := L_lib_927_aux.Join.M 4 d * (L_lib_927_aux.Census.B d : ℝ)
    have hcpos : 0 < c := mul_pos hM4pos (Nat.cast_pos.mpr hBpos)
    have hsupp_eq (U : Submodule F W) : supp U = L_lib_927_aux.SupportGeometry.support U := by
      ext i
      dsimp only [supp, L_lib_927_aux.SupportGeometry.support]
      simp only [Finset.mem_filter]
      rfl
    have hh_eq : ∀ (x : W) (b : Fin 4), (∑ i : Fin n, H i b * x i) = ∑ i : Fin n, h i b * x i := by
      intro x b
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      dsimp only [H, L_lib_927_aux.DualWeight.hCode, h]
      split_ifs <;> first | rfl | contradiction
    have hgood_iff (U : Submodule F W) :
        L_lib_927_aux.Census.Good d H U ↔ Module.finrank F U = d ∧ good U := by
      constructor
      · intro hG
        refine ⟨hG.1, fun x hx b => ?_, hG.2.2⟩
        rw [← hh_eq x b]
        exact hG.2.1 x hx b
      · rintro ⟨hrk, hg1, hg2⟩
        refine ⟨hrk, fun x hx b => ?_, hg2⟩
        rw [hh_eq x b]
        exact hg1 x hx b
    let isMixed (S : Finset (Fin n)) : Prop := 0 < sites S 0 ∧ 0 < sites S 1
    let S_mixed : Finset (Finset (Fin n)) := Finset.univ.filter isMixed
    have hlayer_card : (layer.card : ℝ) = ∑ S ∈ S_mixed, (L_lib_927_aux.Census.cells d H S : ℝ) := by
      rw [← Nat.cast_sum]
      congr 1
      rw [Finset.card_eq_sum_card_fiberwise (f := L_lib_927_aux.SupportGeometry.support) (t := S_mixed)
        (fun U hU => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          have hm := (Finset.mem_filter.mp (Finset.mem_filter.mp hU).1).2
          simpa [hsupp_eq U, isMixed] using hm⟩)]
      refine Finset.sum_congr rfl fun S hS => ?_
      have hSm : isMixed S := (Finset.mem_filter.mp hS).2
      unfold L_lib_927_aux.Census.cells
      refine Finset.card_bij (fun U _ => U) ?_ (fun _ _ _ _ h0 => h0) ?_
      · intro U hU
        rcases Finset.mem_filter.mp hU with ⟨hUlay, hUsupp⟩
        rcases Finset.mem_filter.mp hUlay with ⟨hUmix, hUrk⟩
        rcases Finset.mem_filter.mp hUmix with ⟨hUspc, _⟩
        have hUgood := (Finset.mem_filter.mp hUspc).2
        exact (L_lib_927_aux.Census.mem_cellsSet d H S U).mpr ⟨(hgood_iff U).mpr ⟨hUrk, hUgood⟩, hUsupp⟩
      · intro U hU
        rcases (L_lib_927_aux.Census.mem_cellsSet d H S U).mp hU with ⟨hUGood, hUsupp⟩
        have h1 := (hgood_iff U).mp hUGood
        have h2 : isMixed (supp U) := by rw [hsupp_eq U, hUsupp]; exact hSm
        refine ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1.2⟩, h2⟩, h1.1⟩, hUsupp⟩, rfl⟩
    have htot_err := L_lib_927_aux.Join.total_bound (m := 4) (w := 2 * t) (d := d) (n := n)
      hn_ge3 hd2 H (L_lib_927_aux.DualWeight.hCode_weight t)
    have herr_wt : ∑ S : Finset (Fin n),
        |c * (L_lib_927_aux.Census.cells d H S : ℝ) - L_lib_927_aux.Transfer.wt r S| ≤
        1 + 2 * (L_lib_927_aux.Join.M 4 d - 1) * (L_lib_927_aux.Join.L d) ^ n * (L_lib_927_aux.Join.t d) ^ t +
          2 * L_lib_927_aux.Join.M 4 d * L_lib_927_aux.Join.q d * (L_lib_927_aux.Join.L (d - 1)) ^ n := by
      have hwt_eq (S : Finset (Fin n)) :
          |c * (L_lib_927_aux.Census.cells d H S : ℝ) - L_lib_927_aux.Transfer.wt r S| =
          L_lib_927_aux.Join.err d H S := by
        dsimp only [r]
        rw [L_lib_927_aux.Transfer.wt_eq_q_pow_runs hn_gt1 S]
        rfl
      simp_rw [hwt_eq]
      rw [hdiv2] at htot_err
      exact htot_err
    have hnonmix_le : (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ¬ isMixed S),
        L_lib_927_aux.Transfer.wt r S) ≤ 2 * ((2 : ℝ) ^ d) ^ (3 * t) := by
      refine le_trans (le_of_eq ?_) (L_lib_927_aux.Asymp.nonMixed_weight_le_pred (t := t) hd2
        ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => ¬ isMixed S)) fun S => ?_)
      · refine Finset.sum_congr rfl fun S _ => by
          dsimp only [r]
          exact L_lib_927_aux.Transfer.wt_eq_q_pow_runs hn_gt1 S
      · rw [Finset.mem_filter]
        simp only [Finset.mem_univ, true_and, isMixed, not_and_or, sites]
        have hc0 : (S.filter fun i => i.val % 2 = 0).card =
            (@Finset.filter (Fin (6 * t)) (fun i => i.val % 2 = 0)
              (fun i => Nat.decEq (i.val % 2) 0) S).card :=
          L_lib_927_aux.HostDim.filter_card_congr S (fun i : Fin n => i.val % 2 = 0) _ _
        have hc1 : (S.filter fun i => i.val % 2 = 1).card =
            (@Finset.filter (Fin (6 * t)) (fun i => i.val % 2 = 1)
              (fun i => Nat.decEq (i.val % 2) 1) S).card :=
          L_lib_927_aux.HostDim.filter_card_congr S (fun i : Fin n => i.val % 2 = 1) _ _
        constructor
        · rintro (h0 | h0)
          · left; rw [← hc0]; exact Nat.eq_zero_of_not_pos h0
          · right; rw [← hc1]; exact Nat.eq_zero_of_not_pos h0
        · rintro (hz | hz)
          · left; intro hs0; rw [← hc0] at hz; rw [hz] at hs0; exact Nat.lt_irrefl 0 hs0
          · right; intro hs1; rw [← hc1] at hz; rw [hz] at hs1; exact Nat.lt_irrefl 0 hs1
    have hsum_all_lo : (L_lib_927_aux.Join.L d) ^ n ≤ ∑ S : Finset (Fin n), L_lib_927_aux.Transfer.wt r S := by
      have h1 := (L_lib_927_aux.Asymp.sum_wt_bounds (n := n) hn_pos hn_even r hr0).1
      change (1 + r) ^ n ≤ _ at h1
      have hL_eq : 1 + r = L_lib_927_aux.Join.L d := rfl
      rwa [hL_eq] at h1
    have hmix_wt_lo : (L_lib_927_aux.Join.L d) ^ n - 2 * ((2 : ℝ) ^ d) ^ (3 * t) ≤
        ∑ S ∈ S_mixed, L_lib_927_aux.Transfer.wt r S := by
      have hpart : (∑ S : Finset (Fin n), L_lib_927_aux.Transfer.wt r S) =
          (∑ S ∈ S_mixed, L_lib_927_aux.Transfer.wt r S) +
          (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ¬ isMixed S),
            L_lib_927_aux.Transfer.wt r S) := by
        have hd : Disjoint S_mixed ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => ¬ isMixed S)) := by
          rw [Finset.disjoint_left]; intro S h1 h2
          exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
        have hu : S_mixed ∪ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ¬ isMixed S) = Finset.univ := by
          ext S; simp only [S_mixed, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
        rw [← Finset.sum_union hd, hu]
      linarith
    have hmix_diff : |c * (layer.card : ℝ) - ∑ S ∈ S_mixed, L_lib_927_aux.Transfer.wt r S| ≤
        ∑ S : Finset (Fin n), |c * (L_lib_927_aux.Census.cells d H S : ℝ) - L_lib_927_aux.Transfer.wt r S| := by
      rw [hlayer_card, Finset.mul_sum, ← Finset.sum_sub_distrib]
      calc |∑ S ∈ S_mixed, _|
          ≤ ∑ S ∈ S_mixed, |c * (L_lib_927_aux.Census.cells d H S : ℝ) - L_lib_927_aux.Transfer.wt r S| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ S : Finset (Fin n), |c * (L_lib_927_aux.Census.cells d H S : ℝ) - L_lib_927_aux.Transfer.wt r S| :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
    have hlayer_lo : 1 / 2 ≤ c * (layer.card : ℝ) / (L_lib_927_aux.Join.L d) ^ n := by
      have hge1 : (L_lib_927_aux.Join.L d) ^ n * (1 - errTot t) ≤ c * (layer.card : ℝ) := by
        have h1 : (∑ S ∈ S_mixed, L_lib_927_aux.Transfer.wt r S) -
            (∑ S : Finset (Fin n), |c * (L_lib_927_aux.Census.cells d H S : ℝ) - L_lib_927_aux.Transfer.wt r S|) ≤
            c * (layer.card : ℝ) := by
          linarith [(abs_le.mp hmix_diff).1]
        have herr' : (1 + 2 * (L_lib_927_aux.Join.M 4 d - 1) * (L_lib_927_aux.Join.L d) ^ n * (L_lib_927_aux.Join.t d) ^ t +
            2 * L_lib_927_aux.Join.M 4 d * L_lib_927_aux.Join.q d * (L_lib_927_aux.Join.L (d - 1)) ^ n +
            2 * ((2 : ℝ) ^ d) ^ (3 * t)) = (L_lib_927_aux.Join.L d) ^ n * errTot t := by
          dsimp only [errTot, d, n]
          exact herr'_aux _ _ hLnpos.ne'
        linarith
      calc 1 / 2 ≤ 1 - errTot t := by linarith
        _ = (L_lib_927_aux.Join.L d) ^ n * (1 - errTot t) / (L_lib_927_aux.Join.L d) ^ n :=
            hmul_div_aux _ _ hLnpos.ne'
        _ ≤ c * (layer.card : ℝ) / (L_lib_927_aux.Join.L d) ^ n :=
            div_le_div_of_nonneg_right hge1 hLnpos.le
    have hlayer_pos : (0 : ℝ) < (layer.card : ℝ) := by
      by_contra! hle
      have h0 : c * (layer.card : ℝ) / (L_lib_927_aux.Join.L d) ^ n ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hcpos.le hle) hLnpos.le
      linarith
    let S_bad : Finset (Finset (Fin n)) :=
      (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ¬ L_lib_927_aux.Asymp.goodS d t L₀ M η S)
    have hbad_mem (U : Submodule F W) (hU : U ∈ layer \ typical) :
        L_lib_927_aux.SupportGeometry.support U ∈ S_bad := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun hgoodS => ?_⟩
      rcases Finset.mem_sdiff.mp hU with ⟨hUlay, hUntyp⟩
      have hUmix := (Finset.mem_filter.mp hUlay).1
      have hUspc := (Finset.mem_filter.mp hUmix).1
      have hUgood := (Finset.mem_filter.mp hUspc).2
      have hUrk := (Finset.mem_filter.mp hUlay).2
      have hUGood : L_lib_927_aux.Census.Good d H U := (hgood_iff U).mpr ⟨hUrk, hUgood⟩
      have hSites0 : 0 < sites (supp U) 0 := (Finset.mem_filter.mp hUmix).2.1
      have hSne : (L_lib_927_aux.SupportGeometry.support U).Nonempty := by
        obtain ⟨i, hi⟩ := Finset.card_pos.mp hSites0
        exact ⟨i, (hsupp_eq U) ▸ (Finset.mem_filter.mp hi).1⟩
      have hhb' : (L_lib_927_aux.HostDim.oddZSet (L_lib_927_aux.SupportGeometry.support U) hSne).card - 4 ≤
          host U ∧ host U ≤ (L_lib_927_aux.HostDim.oddZSet (L_lib_927_aux.SupportGeometry.support U) hSne).card :=
        L_lib_927_aux.HostDim.host_bounds_pred hd2 H U hUGood hSne spaces (fun E => by
          dsimp only [spaces]
          rw [Finset.mem_filter]
          exact ⟨fun h0 => ⟨fun x hx b => (hh_eq x b) ▸ h0.2.1 x hx b, h0.2.2⟩,
            fun h0 => ⟨Finset.mem_univ _, fun x hx b => (hh_eq x b).symm ▸ h0.1 x hx b, h0.2⟩⟩) _
      have htyp_ineq := L_lib_927_aux.Asymp.goodS_implies_typical ht1 hd2 hη0 hηhalf hL0_ge hM hstep
        (L_lib_927_aux.SupportGeometry.support U) hSne hgoodS hhb'.1 hhb'.2
      have hUtyp : U ∈ typical := Finset.mem_filter.mpr ⟨hUlay, by
        rw [hLdef]
        exact htyp_ineq.trans hηε⟩
      exact hUntyp hUtyp
    have hsdiff_card : ((layer \ typical).card : ℝ) ≤ ∑ S ∈ S_bad, (L_lib_927_aux.Census.cells d H S : ℝ) := by
      rw [← Nat.cast_sum]
      refine Nat.cast_le.mpr ?_
      rw [Finset.card_eq_sum_card_fiberwise (f := L_lib_927_aux.SupportGeometry.support) (t := S_bad)
        hbad_mem]
      refine Finset.sum_le_sum fun S _ => ?_
      unfold L_lib_927_aux.Census.cells
      refine Finset.card_le_card_of_injOn (fun U => U) ?_ (fun _ _ _ _ h => h)
      intro U hU
      rcases Finset.mem_filter.mp hU with ⟨hUdiff, hUsupp⟩
      have hUlay := (Finset.mem_sdiff.mp hUdiff).1
      have hUGood := (hgood_iff U).mpr ⟨(Finset.mem_filter.mp hUlay).2,
        (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hUlay).1).1).2⟩
      exact (L_lib_927_aux.Census.mem_cellsSet d H S U).mpr ⟨hUGood, hUsupp⟩
    have hsdiff_up : c * ((layer \ typical).card : ℝ) / (L_lib_927_aux.Join.L d) ^ n ≤ badW t + errTot t := by
      have hdiff : c * (∑ S ∈ S_bad, (L_lib_927_aux.Census.cells d H S : ℝ)) -
          (∑ S ∈ S_bad, L_lib_927_aux.Transfer.wt r S) ≤
          ∑ S : Finset (Fin n), |c * (L_lib_927_aux.Census.cells d H S : ℝ) - L_lib_927_aux.Transfer.wt r S| := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        calc (∑ S ∈ S_bad, (c * (L_lib_927_aux.Census.cells d H S : ℝ) - L_lib_927_aux.Transfer.wt r S))
            ≤ ∑ S ∈ S_bad, |c * (L_lib_927_aux.Census.cells d H S : ℝ) - L_lib_927_aux.Transfer.wt r S| :=
              Finset.sum_le_sum fun S _ => le_abs_self _
          _ ≤ ∑ S : Finset (Fin n), |c * (L_lib_927_aux.Census.cells d H S : ℝ) - L_lib_927_aux.Transfer.wt r S| :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
      have h1 : c * ((layer \ typical).card : ℝ) ≤ (∑ S ∈ S_bad, L_lib_927_aux.Transfer.wt r S) +
          (1 + 2 * (L_lib_927_aux.Join.M 4 d - 1) * (L_lib_927_aux.Join.L d) ^ n * (L_lib_927_aux.Join.t d) ^ t +
            2 * L_lib_927_aux.Join.M 4 d * L_lib_927_aux.Join.q d * (L_lib_927_aux.Join.L (d - 1)) ^ n +
            2 * ((2 : ℝ) ^ d) ^ (3 * t)) := by
        have hm := mul_le_mul_of_nonneg_left hsdiff_card hcpos.le
        have h2p : 0 ≤ 2 * ((2 : ℝ) ^ d) ^ (3 * t) := h2pow_nn
        linarith
      have hdiv := div_le_div_of_nonneg_right h1 hLnpos.le
      rw [add_div] at hdiv
      exact hdiv
    have hratio_le : ((layer \ typical).card : ℝ) / (layer.card : ℝ) ≤ 2 * (badW t + errTot t) := by
      have hid := hratio_aux ((layer \ typical).card : ℝ) (layer.card : ℝ) c ((L_lib_927_aux.Join.L d) ^ n)
        hcpos.ne' hLnpos.ne' hlayer_pos.ne'
      rw [hid]
      have hnn : 0 ≤ c * ((layer \ typical).card : ℝ) / (L_lib_927_aux.Join.L d) ^ n := by
        exact div_nonneg (mul_nonneg hcpos.le (Nat.cast_nonneg _)) hLnpos.le
      calc (c * ((layer \ typical).card : ℝ) / (L_lib_927_aux.Join.L d) ^ n) /
            (c * (layer.card : ℝ) / (L_lib_927_aux.Join.L d) ^ n)
          ≤ (badW t + errTot t) /
            (c * (layer.card : ℝ) / (L_lib_927_aux.Join.L d) ^ n) :=
            div_le_div_of_nonneg_right hsdiff_up (by linarith)
        _ ≤ (badW t + errTot t) / (1 / 2) :=
            div_le_div_of_nonneg_left (hnn.trans hsdiff_up) hhalf_pos hlayer_lo
        _ = 2 * (badW t + errTot t) := by ring
    have hsub_typ : typical ⊆ layer := Finset.filter_subset _ _
    have hcard_eq : (typical.card : ℝ) / (layer.card : ℝ) =
        1 - ((layer \ typical).card : ℝ) / (layer.card : ℝ) := by
      have hnat : (layer \ typical).card + typical.card = layer.card :=
        Finset.card_sdiff_add_card_eq_card hsub_typ
      have hreal : ((layer \ typical).card : ℝ) + (typical.card : ℝ) = (layer.card : ℝ) := by
        exact_mod_cast hnat
      exact hsub_aux _ _ _ hlayer_pos.ne' hreal
    rw [hcard_eq]
    linarith
  · refine Filter.Eventually.of_forall fun t => ?_
    exact div_le_one_of_le₀ (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (Nat.cast_nonneg _)
