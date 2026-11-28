import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_921
open scoped BigOperators
variable {κ ι : Type*} [Fintype κ] [Fintype ι]
private def ip (v x : κ → ℚ) : ℚ := ∑ r, v r*x r
private theorem ips (v x : κ → ℚ) : ip v x=ip x v := by simp only [ip,mul_comm]
private theorem ipa (v x y : κ → ℚ) : ip v (x+y)=ip v x+ip v y := by simp [ip,mul_add,Finset.sum_add_distrib]
private theorem ipd (v x y : κ → ℚ) : ip v (x-y)=ip v x-ip v y := by simp [ip,mul_sub,Finset.sum_sub_distrib]
private theorem ipm (v x : κ → ℚ) (c : ℚ) : ip v (c • x)=c*ip v x := by
  simp only [ip,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro r _; ring
private def ann (x : κ → ℚ) : Submodule ℚ (κ → ℚ) := {
  carrier := {v | ip v x=0}
  zero_mem' := by simp [ip], add_mem' := by
    intro a b ha hb
    change ip a x=0 at ha
    change ip b x=0 at hb
    change ip (a+b) x=0
    rw [ips,ipa,ips x a,ips x b,ha,hb,add_zero]
  smul_mem' := by
    intro c v h
    change ip v x=0 at h
    change ip (c • v) x=0
    rw [ips,ipm,ips x v,h,mul_zero] }
private theorem positive (x : κ → ℚ) (h : ip x x=0) : x=0 := by
  funext r
  have ge (k : κ) : 0 ≤ x k*x k := mul_self_nonneg _
  have le : x r*x r ≤ ip x x := Finset.single_le_sum (fun k _ => ge k) (Finset.mem_univ r)
  rw [h] at le
  change x r=0
  nlinarith [ge r]
private theorem project (A : Finset (κ → ℚ)) (x : κ → ℚ) :
    ∃ y∈Submodule.span ℚ (A : Set (κ → ℚ)), ∀a∈A, ip a (x-y)=0 := by
  classical
  induction A using Finset.induction_on generalizing x with
  | empty => exact ⟨0,Submodule.zero_mem _,by simp⟩
  | @insert a S ha ih =>
    let K := Submodule.span ℚ (S : Set (κ → ℚ))
    let K' := Submodule.span ℚ ((insert a S : Finset (κ → ℚ)) : Set (κ → ℚ))
    have incl : K ≤ K' := Submodule.span_mono (by intro v hv; exact Finset.mem_insert_of_mem hv)
    have am : a∈K' := Submodule.subset_span (Finset.mem_insert_self _ _)
    obtain ⟨b,bm,hb⟩ := ih a
    obtain ⟨y,ym,hy⟩ := ih x
    let u := a-b
    have ku : K ≤ ann u := Submodule.span_le.mpr (by intro v hv; exact hb v hv)
    have ky : K ≤ ann (x-y) := Submodule.span_le.mpr (by intro v hv; exact hy v hv)
    have bu : ip b u=0 := ku bm
    have uu : ip u u=ip a u := by
      calc
        ip u u = ip u a-ip u b := ipd u a b
        _ = ip a u := by rw [ips u a,ips u b,bu,sub_zero]
    by_cases h : ip a u=0
    · have ab : a=b := sub_eq_zero.mp (positive u (uu.trans h))
      refine ⟨y,incl ym,?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|vs
      · rw [ab]; exact ky bm
      · exact hy _ vs
    · let c := ip a (x-y)/ip a u
      refine ⟨y+c • u,K'.add_mem (incl ym) (K'.smul_mem _ (K'.sub_mem am (incl bm))),?_⟩
      intro v hv
      have e : x-(y+c • u)=(x-y)-c • u := by abel
      rw [e,ipd,ipm]
      rcases Finset.mem_insert.mp hv with rfl|vs
      · dsimp [c]; field_simp <;> ring
      · rw [hy _ vs,show ip v u=0 from hb _ vs,mul_zero,sub_self]
private def synth (B : ι → κ → ℚ) : (ι → ℚ) →ₗ[ℚ] (κ → ℚ) where
  toFun w r := ∑i,B i r*w i
  map_add' u v := by funext r; simp [mul_add,Finset.sum_add_distrib]
  map_smul' c w := by
    funext r
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
private theorem least (B : ι → κ → ℚ) :
    ∃w : ι → ℚ, ∀i, ∑ r,B i r*(∑j,B j r*w j)=∑r,B i r := by
  classical
  let S := Finset.univ.image B
  obtain ⟨y,hy,eq⟩ := project S (fun _ => 1)
  have sub : Submodule.span ℚ (S : Set (κ → ℚ)) ≤ LinearMap.range (synth B) :=
    Submodule.span_le.mpr (by
      intro b hb
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
      refine ⟨fun j => if j=i then 1 else 0,?_⟩
      funext r
      change (∑j,B j r*(if j=i then 1 else 0))=B i r
      simp [mul_ite])
  obtain ⟨w,rfl⟩ := sub hy
  refine ⟨w,fun i => ?_⟩
  have z := eq (B i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  rw [ipd] at z
  have h : ip (B i) (fun _ => 1) = ∑r,B i r := by simp [ip]
  rw [h] at z
  exact (sub_eq_zero.mp z).symm
variable {κ ι : Type*} [Fintype κ] [Fintype ι]
private def load (B : ι → κ → ℚ) (w : ι → ℚ) (r : κ) := ∑i,B i r*w i
private def obj (x : κ → ℚ) : ℚ := ∑r,(2*x r-x r*x r)
private theorem mix (B : ι → κ → ℚ) (w : ι → ℚ) (y : κ → ℚ) :
    ip (load B w) y = ∑i,w i*ip (B i) y := by
  simp only [load,ip,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro r _; ring
private theorem drow (B : ι → κ → ℚ) (w : ι → ℚ) (i : ι) :
    ∑j,ip (B i) (B j)*w j=ip (B i) (load B w) := by
  rw [ips (B i) (load B w),mix]
  apply Finset.sum_congr rfl; intro j _; rw [ips (B i),mul_comm]
private theorem normalBest (B : ι → κ → ℚ) (w : ι → ℚ)
    (h : ∀ i,ip (B i) (load B w)=∑r,B i r) (v : ι → ℚ) :
    obj (load B v) ≤ obj (load B w) := by
  let y := load B w
  let x := load B v
  let one : κ → ℚ := fun _ => 1
  have ann' (u : ι → ℚ) : ip (load B u) (one-y)=0 := by
    rw [mix]
    apply Finset.sum_eq_zero
    intro i _
    rw [ipd,show ip (B i) one=∑r,B i r by simp [ip,one],show ip (B i) y=∑r,B i r from h i,sub_self,mul_zero]
  have cancel : ip (x-y) (one-y)=0 := by
    rw [ips,ipd,ips _ x,ips _ y,show ip x (one-y)=0 from ann' v,show ip y (one-y)=0 from ann' w,sub_self]
  have e : obj x-obj y=2*ip (x-y) (one-y)-∑r,(x r-y r)^2 := by
    simp only [obj,ip,←Finset.sum_sub_distrib,Finset.mul_sum,Pi.sub_apply]
    apply Finset.sum_congr rfl
    intro r _
    dsimp [one]
    ring
  have pos : 0 ≤ ∑r,(x r-y r)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change obj x ≤ obj y
  linarith
private theorem objForm (B : ι → κ → ℚ) (w : ι → ℚ)
    (bi : ∀i, ip (B i) (B i)=∑r,B i r) :
    (∑i,w i*(2*ip (B i) (B i)-∑j,ip (B i) (B j)*w j))=obj (load B w) := by
  let one : κ → ℚ := fun _ => 1
  have diag (i : ι) : ip (B i) (B i)=ip (B i) one := (bi i).trans (by simp [one,ip])
  simp only [diag,drow,mul_sub,Finset.sum_sub_distrib]
  have a : (∑i,w i*(2*ip (B i) one))=2*ip (load B w) one := by
    rw [mix,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [a,←mix]
  simp [obj,ip,one,Finset.sum_sub_distrib,Finset.mul_sum]

variable {m : ℕ}
private abbrev V (m : ℕ) := Fin m
private def fam (q : ℕ) (P : Finset (V m)) := (Finset.univ.powersetCard q).filter (P ⊆ ·)
private theorem inFam {q : ℕ} {P S : Finset (V m)} : S∈fam q P ↔ P⊆S ∧ S.card=q := by
  simp [fam,Finset.mem_powersetCard,and_comm]
private theorem famSize (q : ℕ) (P : Finset (V m)) (hp : P.card ≤ q) :
    (fam q P).card=Nat.choose (m-P.card) (q-P.card) := by
  classical
  let U := (Finset.univ : Finset (V m)) \ P
  have e : (fam q P).card=(U.powersetCard (q-P.card)).card := by
    apply Finset.card_bij (fun S _ => S \ P)
    · intro S hs
      obtain ⟨inc,cc⟩ := inFam.mp hs
      apply Finset.mem_powersetCard.mpr
      refine ⟨fun z hz => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp hz).2⟩,?_⟩
      rw [Finset.card_sdiff_of_subset inc,cc]
    · intro S hs T ht eq
      have si := (inFam.mp hs).1
      have ti := (inFam.mp ht).1
      simp only [Finset.ext_iff,Finset.subset_iff,Finset.mem_sdiff] at *
      grind
    · intro T ht
      obtain ⟨sub,sz⟩ := Finset.mem_powersetCard.mp ht
      have dis : Disjoint P T := Finset.disjoint_left.mpr (by
        intro v hv h; exact (Finset.mem_sdiff.mp (sub h)).2 hv)
      refine ⟨P∪T,inFam.mpr ⟨Finset.subset_union_left,?_⟩,?_⟩
      · rw [Finset.card_union_of_disjoint dis,sz]; omega
      · ext v
        have h : v∈P → v∈T → False := fun a b => Finset.disjoint_left.mp dis a b
        simp only [Finset.mem_union,Finset.mem_sdiff]
        tauto
  rw [e,Finset.card_powersetCard]
  congr 1
  simp [U,Finset.card_sdiff_of_subset]
private def xx (P A S : Finset (V m)) := (A∩S) \ P
private def yy (P A B S : Finset (V m)) := S \ (P∪A∪B)
private def both (P A B : Finset (V m)) := (A∩B) \ P
private def neither (P A B : Finset (V m)) := (Finset.univ : Finset (V m)) \ (P∪A∪B)
private theorem splitSets (P A B S : Finset (V m)) (sub : P⊆S) (hs : A∩S=B∩S) :
    let X := xx P A S
    let Y := yy P A B S
    X⊆both P A B ∧ Y⊆neither P A B ∧ P∪X∪Y=S ∧
    (A∩P)∪X=A∩S ∧ (A∩P)=(B∩P) := by
  dsimp [xx,yy,both,neither]
  simp only [Finset.ext_iff,Finset.subset_iff,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,Finset.mem_univ,true_and] at *
  grind
private theorem joinSets (P A B X Y : Finset (V m)) (hx : X⊆both P A B) (hy : Y⊆neither P A B) :
    let S := P∪X∪Y
    P⊆S ∧ A∩S=(A∩P)∪X ∧ B∩S=(B∩P)∪X ∧
    xx P A S=X ∧ yy P A B S=Y ∧ Disjoint P X ∧ Disjoint (P∪X) Y ∧ Disjoint (A∩P) X := by
  dsimp [xx,yy,both,neither] at *
  simp only [Finset.ext_iff,Finset.subset_iff,Finset.disjoint_left,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,Finset.mem_univ,true_and] at *
  grind
private def good (q t : ℕ) (P A B : Finset (V m)) := (fam q P).filter fun S => A∩S=B∩S ∧ (A∩S).card=t
private def formula (q t : ℕ) (P A B : Finset (V m)) :=
  let locked := A∩P
  let e := t-locked.card
  let l := q-P.card
  if locked=B∩P ∧ locked.card ≤ t ∧ e ≤ l then ((both P A B).card.choose e)*((neither P A B).card.choose (l-e)) else 0
private theorem goodSize (q t : ℕ) (P A B : Finset (V m)) (hp : P.card ≤ q) :
    (good q t P A B).card=formula q t P A B := by
  classical
  let e := t-(A∩P).card
  let l := q-P.card
  have enc (S : Finset (V m)) (hs : S∈good q t P A B) :
      let X := xx P A S
      let Y := yy P A B S
      X∈(both P A B).powersetCard e ∧ Y∈(neither P A B).powersetCard (l-e) ∧
      P∪X∪Y=S ∧ A∩P=B∩P ∧ (A∩P).card ≤ t ∧ e ≤ l := by
    have ⟨f,se,tc⟩ := Finset.mem_filter.mp hs
    obtain ⟨inc,sc⟩ := inFam.mp f
    obtain ⟨hx,hy,j,k,lock⟩ := splitSets P A B S inc se
    obtain ⟨_,_,_,_,_,dx,dy,dh⟩ := joinSets P A B _ _ hx hy
    have a := congrArg Finset.card j
    have b := congrArg Finset.card k
    rw [Finset.card_union_of_disjoint dy,Finset.card_union_of_disjoint dx,sc] at a
    rw [Finset.card_union_of_disjoint dh,tc] at b
    dsimp [e,l]
    exact ⟨Finset.mem_powersetCard.mpr ⟨hx,by omega⟩,Finset.mem_powersetCard.mpr ⟨hy,by omega⟩,j,lock,by omega,by omega⟩
  by_cases h : A∩P=B∩P ∧ (A∩P).card ≤ t ∧ e ≤ l
  · rw [formula,if_pos h]
    change (good q t P A B).card=(both P A B).card.choose e*(neither P A B).card.choose (l-e)
    rw [←Finset.card_powersetCard,←Finset.card_powersetCard,←Finset.card_product]
    apply Finset.card_bij (fun S _ => (xx P A S,yy P A B S))
    · intro S hs
      exact Finset.mem_product.mpr ⟨(enc S hs).1,(enc S hs).2.1⟩
    · intro S hs T ht eq
      obtain ⟨a,b⟩ := Prod.mk.inj eq
      rw [←(enc S hs).2.2.1,a,b,(enc T ht).2.2.1]
    · rintro ⟨X,Y⟩ xy
      obtain ⟨xm,ym⟩ := Finset.mem_product.mp xy
      obtain ⟨xs,xc⟩ := Finset.mem_powersetCard.mp xm
      obtain ⟨ys,yc⟩ := Finset.mem_powersetCard.mp ym
      obtain ⟨inc,a,b,x,y,dx,dy,dh⟩ := joinSets P A B X Y xs ys
      refine ⟨P∪X∪Y,Finset.mem_filter.mpr ⟨inFam.mpr ⟨inc,?_⟩,?_,?_⟩,Prod.ext x y⟩
      · rw [Finset.card_union_of_disjoint dy,Finset.card_union_of_disjoint dx,xc,yc]
        dsimp [e,l] at *; omega
      · rw [a,b,h.1]
      · rw [a,Finset.card_union_of_disjoint dh,xc]; dsimp [e]; omega
  · rw [formula,if_neg h,Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hs
    exact h (enc S hs).2.2.2

variable {m n d : ℕ}
private abbrev Panel (m : ℕ) := Finset (Fin m)
private abbrev Weights (n d : ℕ) := Fin d → Fin n → ℚ
private def bit (A : Fin n → Panel m) (t : ℕ) (S T : Panel m) (i : Fin n) : ℚ :=
  if T=A i∩S ∧ T.card=t then 1 else 0
private def feature (A : Fin n → Panel m) (t : ℕ) (F : Finset (Panel m)) (i : Fin n)
    (z : Panel m × Panel m) : ℚ := if z.1∈F then bit A t z.1 z.2 i else 0
private def entry (q : ℕ) (P : Panel m) (A : Fin n → Panel m) (t : ℕ) (i j : Fin n) : ℚ :=
  let locked := A i∩P
  let e := t-locked.card
  let l := q-P.card
  if locked=A j∩P ∧ locked.card ≤ t ∧ e ≤ l then
    (((both P (A i) (A j)).card.choose e)*((neither P (A i) (A j)).card.choose (l-e)) : ℕ) else 0
private theorem entryVal (q : ℕ) (P : Panel m) (A : Fin n → Panel m) (t : ℕ) (i j : Fin n) :
    entry q P A t i j=(formula q t P (A i) (A j) : ℚ) := by
  dsimp only [entry,formula]; split_ifs <;> rfl
private theorem sumBits (A : Fin n → Panel m) (t : ℕ) (S : Panel m) (i j : Fin n) :
    (∑T,bit A t S T i*bit A t S T j)=
      if A i∩S=A j∩S ∧ (A i∩S).card=t then 1 else 0 := by
  classical
  rw [Finset.sum_eq_single (A i∩S)]
  · simp only [bit]
    split_ifs <;> grind
  · intro T _ ne; simp [bit,ne]
  · simp
private theorem denGram (q t : ℕ) (P : Panel m) (A : Fin n → Panel m) (hp : P.card ≤ q) (i j : Fin n) :
    entry q P A t i j=ip (feature A t (fam q P) i) (feature A t (fam q P) j) := by
  classical
  rw [entryVal,←goodSize q t P (A i) (A j) hp]
  unfold ip
  rw [Fintype.sum_prod_type]
  have inner (S : Panel m) : (∑T : Panel m,feature A t (fam q P) i (S,T)*
      feature A t (fam q P) j (S,T))=
      if S∈good q t P (A i) (A j) then 1 else 0 := by
    by_cases h : S∈fam q P
    · simp only [feature,if_true,sumBits,good,Finset.mem_filter,h,true_and]
    · simp [feature,h,good]
  simp_rw [inner]
  simp [←Finset.sum_filter]
private theorem diagBit (A : Fin n → Panel m) (t : ℕ) (F : Finset (Panel m)) (i : Fin n) :
    ip (feature A t F i) (feature A t F i)=∑r,feature A t F i r := by
  apply Finset.sum_congr rfl
  intro r _
  simp only [feature,bit]; split_ifs <;> norm_num
private def levelLoad (A : Fin n → Panel m) (S : Panel m) (t : Fin d) (w : Weights n d) (T : Panel m) :=
  ∑i,bit A (t.val+1) S T i*w t i
private def response (A : Fin n → Panel m) (w : Weights n d) (S : Panel m) : ℚ :=
  ∑t : Fin d,obj (levelLoad A S t w)
private def raw (A : Fin n → Panel m) (q : ℕ) (P : Panel m) (w : Weights n d) : ℚ :=
  ∑t : Fin d, ∑i,w t i*(2*entry q P A (t.val+1) i i-∑j,entry q P A (t.val+1) i j*w t j)
private def normal (A : Fin n → Panel m) (q : ℕ) (P : Panel m) (w : Weights n d) :=
  ∀ (t : Fin d) (i : Fin n), (∑ j,entry q P A (t.val+1) i j*w t j)=entry q P A (t.val+1) i i
private theorem objPanels (A : Fin n → Panel m) (t : Fin d) (F : Finset (Panel m)) (w : Weights n d) :
    obj (load (feature A (t.val+1) F) (w t))=∑S∈F,obj (levelLoad A S t w) := by
  classical
  unfold obj
  rw [Fintype.sum_prod_type]
  have e (S : Panel m) : (∑T : Panel m,(2*load (feature A (t.val+1) F) (w t) (S,T)-
      load (feature A (t.val+1) F) (w t) (S,T)*load (feature A (t.val+1) F) (w t) (S,T)))=
      if S∈F then ∑T,(2*levelLoad A S t w T-levelLoad A S t w T*levelLoad A S t w T) else 0 := by
    by_cases h : S∈F <;> simp [load,feature,levelLoad,h]
  simp_rw [e]
  simp [←Finset.sum_filter]
private theorem rawPanels (A : Fin n → Panel m) (q : ℕ) (P : Panel m) (hp : P.card ≤ q) (w : Weights n d) :
    raw A q P w=∑S∈fam q P,response A w S := by
  unfold raw response
  simp_rw [denGram q _ P A hp,objForm _ _ (diagBit A _ _),objPanels]
  rw [Finset.sum_comm]
private theorem fit (A : Fin n → Panel m) (q : ℕ) (P : Panel m) (hp : P.card ≤ q) :
    ∃w : Weights n d,normal A q P w ∧ ∀ v : Weights n d,raw A q P v ≤ raw A q P w := by
  classical
  choose w hw using fun t : Fin d => least (feature A (t.val+1) (fam q P))
  refine ⟨w,?_,?_⟩
  · intro t i
    simp only [denGram q _ P A hp,drow,diagBit]
    exact hw t i
  · intro v
    unfold raw
    apply Finset.sum_le_sum
    intro t _
    simp only [denGram q _ P A hp,objForm _ _ (diagBit A _ _)]
    exact normalBest _ _ (hw t) _

variable {m : ℕ}
private def deg (q : ℕ) (P : Finset (Fin m)) : ℚ := (Nat.choose (m-P.card) (q-P.card) : ℕ)
private def children (P : Finset (Fin m)) := (Finset.univ : Finset (Fin m)) \ P
private theorem childCard (P : Finset (Fin m)) : (children P).card=m-P.card := by
  simp [children,Finset.card_sdiff_of_subset]
private theorem famOne (q : ℕ) (P : Finset (Fin m)) (hp : P.card=q) : fam q P={P} := by
  ext S
  simp only [inFam,Finset.mem_singleton]
  exact ⟨fun h => (Finset.eq_of_subset_of_card_le h.1 (by omega)).symm,fun h => by subst S; exact ⟨Finset.Subset.rfl,hp⟩⟩
private theorem degPos {q : ℕ} {P : Finset (Fin m)} (hm : q ≤ m) (hp : P.card ≤ q) : 0<deg q P := by
  unfold deg
  exact_mod_cast Nat.choose_pos (show q-P.card ≤ m-P.card by omega)
private theorem countChildren {q : ℕ} (P : Finset (Fin m)) (f : Finset (Fin m) → ℚ) :
    (∑ j∈children P,∑ S∈fam q (insert j P),f S)=((q-P.card : ℕ) : ℚ)*∑ S∈fam q P,f S := by
  classical
  have famIns (j : Fin m) : fam q (insert j P)=(fam q P).filter (j∈·) := by
    ext S; simp only [inFam,Finset.mem_filter,Finset.insert_subset_iff]; tauto
  simp_rw [famIns,Finset.sum_filter]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hs
  have e : (children P).filter (·∈S)=S\P := by ext j; simp [children,and_comm]
  have c : (S\P).card=q-P.card := by
    obtain ⟨sub,cc⟩ := inFam.mp hs
    rw [Finset.card_sdiff_of_subset sub,cc]
  rw [←Finset.sum_filter,e,Finset.sum_const,c,nsmul_eq_mul]
private theorem avgFixed {q : ℕ} (hm : q ≤ m) (P : Finset (Fin m)) (hp : P.card<q)
    (f : Finset (Fin m) → ℚ) :
    ((m-P.card : ℕ) : ℚ)*((∑S∈fam q P,f S)/deg q P)=
      ∑j∈children P,(∑S∈fam q (insert j P),f S)/deg q (insert j P) := by
  classical
  let k : ℚ := (Nat.choose (m-(P.card+1)) (q-(P.card+1)) : ℕ)
  have hk : 0<k := by
    dsimp [k]; exact_mod_cast Nat.choose_pos (show q-(P.card+1) ≤ m-(P.card+1) by omega)
  have hd (j : Fin m) (hj : j∈children P) : deg q (insert j P)=k := by
    have ne := (Finset.mem_sdiff.mp hj).2
    simp [deg,k,Finset.card_insert_of_notMem ne]
  have hc (j : Fin m) (hj : j∈children P) : ((fam q (insert j P)).card : ℚ)=k := by
    rw [←hd j hj]
    unfold deg
    rw [famSize]
    have ne := (Finset.mem_sdiff.mp hj).2
    rw [Finset.card_insert_of_notMem ne]; omega
  have hn := countChildren (q:=q) P (fun _ => (1:ℚ))
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hn
  rw [Finset.sum_congr rfl hc,Finset.sum_const,nsmul_eq_mul,childCard,famSize q P (by omega)] at hn
  change ((m-P.card : ℕ) : ℚ)*k=((q-P.card : ℕ) : ℚ)*deg q P at hn
  calc
    _ = (((q-P.card : ℕ) : ℚ)*(∑S∈fam q P,f S))/k := by
      have hd0 := (degPos hm (le_of_lt hp)).ne'
      field_simp [hd0,hk.ne']
      linear_combination (∑S∈fam q P,f S)*hn
    _ = (∑j∈children P,(∑S∈fam q (insert j P),f S))/k := by rw [countChildren]
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj; rw [hd j hj]
private theorem descend {q : ℕ} (hm : q ≤ m) (val tr : Finset (Fin m) → ℚ)
    (terminal : ∀ P, P.card=q → val P=tr P)
    (step : ∀ P, P.card<q → ((m-P.card : ℕ) : ℚ)*val P ≤ ∑j∈children P,val (insert j P))
    (P : Finset (Fin m)) (hp : P.card ≤ q) :
    ∃S,P⊆S ∧ S.card=q ∧ val P ≤ tr S := by
  classical
  generalize h : q-P.card=k
  induction k using Nat.strong_induction_on generalizing P with
  | ind k ih =>
    by_cases eq : P.card=q
    · exact ⟨P,Finset.Subset.rfl,eq,(terminal P eq).le⟩
    have lt : P.card<q := by omega
    have nn : (children P).Nonempty := by rw [←Finset.card_pos,childCard]; omega
    obtain ⟨j,hj,maxj⟩ := Finset.exists_max_image (children P) (fun j => val (insert j P)) nn
    have b := (step P lt).trans (Finset.sum_le_sum (s:=children P) (fun i hi => maxj i hi))
    rw [Finset.sum_const,nsmul_eq_mul,childCard] at b
    have pos : (0:ℚ)<((m-P.card : ℕ) : ℚ) := by exact_mod_cast (show 0 < m-P.card by omega)
    have up := le_of_mul_le_mul_left b pos
    have ne := (Finset.mem_sdiff.mp hj).2
    have sz := Finset.card_insert_of_notMem ne
    obtain ⟨S,sub,cost,yes⟩ := ih (q-(insert j P).card) (by omega) (insert j P) (by omega) rfl
    exact ⟨S,(Finset.subset_insert _ _).trans sub,cost,up.trans yes⟩

private def rowTraces (A : Fin n → Panel m) (S : Panel m) := Finset.univ.image (fun i => A i∩S)
private def traceCount (d : ℕ) (A : Fin n → Panel m) (S : Panel m) :=
  ((rowTraces A S).filter (fun T => T.Nonempty ∧ T.card ≤ d)).card
private theorem endEntry {q : ℕ} (S : Panel m) (sc : S.card=q) (A : Fin n → Panel m)
    (t : ℕ) (i j : Fin n) : entry q S A t i j=bit A t S (A i∩S) j := by
  classical
  rw [entryVal,←goodSize q t S (A i) (A j) (by omega)]
  unfold good
  rw [famOne q S sc]
  rw [Finset.filter_singleton]
  unfold bit
  split_ifs <;> simp_all
private theorem terminalValue {q : ℕ} (S : Panel m) (sc : S.card=q) (A : Fin n → Panel m)
    (w : Weights n d) (hw : normal A q S w) : response A w S=(traceCount d A S : ℚ) := by
  classical
  have loadVal (t : Fin d) (T : Panel m) : levelLoad A S t w T=if T∈rowTraces A S ∧ T.card=t.val+1 then 1 else 0 := by
    by_cases h : T∈rowTraces A S ∧ T.card=t.val+1
    · rw [if_pos h]
      obtain ⟨i,_,e⟩ := Finset.mem_image.mp h.1
      have hi := hw t i
      simp only [endEntry S sc A] at hi
      rw [e] at hi
      simpa [levelLoad,bit,e,h.2] using hi
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬(T=A i∩S ∧ T.card=t.val+1) := by
        intro hh
        exact h ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hh.1.symm⟩,hh.2⟩
      simp [bit,hn]
  unfold response obj
  have value (t : Fin d) (T : Panel m) :
      2*levelLoad A S t w T-levelLoad A S t w T*levelLoad A S t w T=
        if T∈rowTraces A S ∧ T.card=t.val+1 then (1:ℚ) else 0 := by
    rw [loadVal]
    split_ifs <;> norm_num
  simp_rw [value]
  rw [Finset.sum_comm]
  have col (T : Panel m) : (∑t : Fin d,if T∈rowTraces A S ∧ T.card=t.val+1 then (1:ℚ) else 0)=
      if T∈rowTraces A S ∧ T.Nonempty ∧ T.card ≤ d then 1 else 0 := by
    split_ifs with h
    · have pos := Finset.card_pos.mpr h.2.1
      let k : Fin d := ⟨T.card-1,by omega⟩
      rw [Finset.sum_eq_single k]
      · have hk : T.card=k.val+1 := by dsimp [k]; omega
        simp [h.1,hk]
      · intro a _ ne
        have hh : T.card≠a.val+1 := by
          intro eq; apply ne; apply Fin.ext; dsimp [k]; omega
        simp [hh]
      · simp
    · apply Finset.sum_eq_zero
      intro t _
      have hn : ¬(T∈rowTraces A S ∧ T.card=t.val+1) := by
        rintro ⟨mem,eq⟩
        exact h ⟨mem,Finset.card_pos.mp (by omega),by have := t.isLt; omega⟩
      simp [hn]
  simp_rw [col]
  unfold traceCount
  have e : (Finset.univ : Finset (Panel m)).filter (fun T => T∈rowTraces A S ∧ T.Nonempty ∧ T.card ≤ d)=
      (rowTraces A S).filter (fun T => T.Nonempty ∧ T.card ≤ d) := by ext T; simp
  rw [←Finset.sum_filter,e,Finset.sum_const,nsmul_eq_mul,mul_one]

private theorem finish (m n q d : ℕ) (A : Fin n → Panel m) (hm : q ≤ m) :
    ∃val : Panel m → ℚ, ∀P,P.card ≤ q →
      (∃w : Weights n d, normal A q P w ∧ raw A q P w/deg q P=val P) ∧
      (∀w : Weights n d, raw A q P w/deg q P ≤ val P) ∧
      (P.card=q → val P=(traceCount d A P : ℚ)) ∧
      (P.card<q → ((m-P.card : ℕ) : ℚ)*val P ≤ ∑j∈children P,val (insert j P)) ∧
      ∃S,P⊆S ∧ S.card=q ∧ val P ≤ (traceCount d A S : ℚ) := by
  classical
  let winner (P : Panel m) : Weights n d := if h:P.card ≤ q then (fit (d:=d) A q P h).choose else 0
  let val (P : Panel m) := raw A q P (winner P)/deg q P
  have best (P : Panel m) (h : P.card ≤ q) : normal A q P (winner P) ∧
      ∀w : Weights n d,raw A q P w/deg q P ≤ val P := by
    have hh := (fit (d:=d) A q P h).choose_spec
    have e : winner P=(fit (d:=d) A q P h).choose := by simp [winner,h]
    refine ⟨by rw [e]; exact hh.1,?_⟩
    intro w
    change raw A q P w/deg q P ≤ raw A q P (winner P)/deg q P
    rw [e]
    exact div_le_div_of_nonneg_right (hh.2 w) (degPos hm h).le
  have terminal (P : Panel m) (h : P.card=q) : val P=(traceCount d A P : ℚ) := by
    change raw A q P (winner P)/deg q P=_
    rw [rawPanels A q P (by omega),famOne q P h,Finset.sum_singleton,terminalValue P h A _ (best P (by omega)).1]
    simp [deg,h]
  have step (P : Panel m) (h : P.card<q) : ((m-P.card : ℕ) : ℚ)*val P ≤ ∑j∈children P,val (insert j P) := by
    change ((m-P.card : ℕ) : ℚ)*(raw A q P (winner P)/deg q P) ≤ _
    rw [rawPanels A q P (by omega),avgFixed hm P h]
    apply Finset.sum_le_sum
    intro j hj
    have ne := (Finset.mem_sdiff.mp hj).2
    have le : (insert j P).card ≤ q := by rw [Finset.card_insert_of_notMem ne]; omega
    rw [←rawPanels A q (insert j P) le]
    exact (best _ le).2 _
  refine ⟨val,fun P hp => ⟨⟨winner P,(best P hp).1,rfl⟩,(best P hp).2,terminal P,step P,?_⟩⟩
  exact descend hm val (fun S => (traceCount d A S : ℚ)) terminal step P hp

end PEqualNP.Outside.L_lib_921

theorem PEqualNP.Outside.L_lib_921 : ∀ (m n q d : ℕ) (A : Fin n → Finset (Fin m)), q ≤ m →
  let traces := fun P : Finset (Fin m) =>
    ((Finset.univ.image (fun i : Fin n => A i ∩ P)).filter
      (fun T => T.Nonempty ∧ T.card ≤ d)).card
  let panels := fun P : Finset (Fin m) => Nat.choose (m-P.card) (q-P.card)
  let gram := fun (P : Finset (Fin m)) (level : Fin d) (i j : Fin n) =>
    let t := level.val+1
    let locked := A i ∩ P
    let extra := t-locked.card
    let left := q-P.card
    let both := (A i ∩ A j) \ P
    let neither := (Finset.univ : Finset (Fin m)) \ (P ∪ A i ∪ A j)
    if locked = A j ∩ P ∧ locked.card ≤ t ∧ extra ≤ left then
      ((Nat.choose both.card extra * Nat.choose neither.card (left-extra) : ℕ) : ℚ)
    else 0
  let W := Fin d → Fin n → ℚ
  let ga := fun (P : Finset (Fin m)) (w : W) (t : Fin d) (i : Fin n) =>
    ∑ j : Fin n, gram P t i j * w t j
  let score := fun (P : Finset (Fin m)) (w : W) =>
    (∑ t : Fin d, ∑ i : Fin n, w t i * (2*gram P t i i - ga P w t i)) / (panels P : ℚ)
  ∃ value : Finset (Fin m) → ℚ, ∀ P : Finset (Fin m), P.card ≤ q →
    (∃ w : W, (∀ t i, ga P w t i = gram P t i i) ∧ score P w = value P) ∧
    (∀ w : W, score P w ≤ value P) ∧
    (P.card = q → value P = (traces P : ℚ)) ∧
    (P.card < q → ((m-P.card : ℕ) : ℚ) * value P ≤
      ∑ j ∈ (Finset.univ \ P), value (insert j P)) ∧
    ∃ S : Finset (Fin m), P ⊆ S ∧ S.card = q ∧ value P ≤ (traces S : ℚ) := by
  intro m n q d A hm
  exact PEqualNP.Outside.L_lib_921.finish m n q d A hm
