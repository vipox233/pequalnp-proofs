import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1442_aux.Semantic
open scoped Classical
abbrev SetOf (n : ℕ) := Finset (Fin n)
def Cover (A B : Fin m → SetOf r) (a f : Fin m → ℕ) (P N : Fin m → SetOf k) :=
  ∀i j,(A i ⊆ B j → Disjoint (P i) (N j)) ∧ (¬A i ⊆ B j → a i+f j<((P i)∩(N j)).card)
def Possible (A B : Fin m → SetOf r) (a f : Fin m → ℕ) (k : ℕ) :=
  ∃ (g : SetOf r → SetOf k) (h : SetOf k → SetOf r),Monotone g ∧ Monotone h ∧
   ∀i X Y,A i ⊆ X → X ⊆ B i → (g X\Y).card ≤ a i → (Y\g X).card ≤ f i → A i ⊆ h Y ∧ h Y ⊆ B i
theorem necessity (A B : Fin m → SetOf r) (a f : Fin m → ℕ) (ok : ∀i,A i ⊆ B i) (h : Possible A B a f k) :
    ∃P N : Fin m → SetOf k,Cover A B a f P N := by
  classical
  obtain ⟨g,h,gm,hm,rec⟩ := h
  refine ⟨fun i => g (A i),fun j => Finset.univ\g (B j),?_⟩
  intro i j
  constructor
  · intro sub
    exact Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 (gm sub hx))
  · intro conflict
    let S := g (A i)
    let T := g (B j)
    let D := S\T
    have eq : (g (A i))∩(Finset.univ\g (B j))=D := by ext z; simp [D,S,T]
    rw [eq]
    by_contra! small
    obtain ⟨Z,zd,sz⟩ := Finset.exists_subset_card_eq (s:=D) (Nat.min_le_right (a i) D.card)
    let X := S\Z
    let Y := T∪(D\Z)
    have sub : X ⊆ Y := by
      intro v hv
      simp only [X,Y,D,Finset.mem_union,Finset.mem_sdiff] at *
      tauto
    have zs : Z ⊆ S := zd.trans Finset.sdiff_subset
    have e : S\X=Z := by ext v; simp only [X,Finset.mem_sdiff]; have := fun (m : v∈Z) => zs m; tauto
    have gain : (Y\T).card ≤ f j := by
      have inc : Y\T ⊆ D\Z := by intro v hv; simp only [Y,Finset.mem_union,Finset.mem_sdiff] at *; tauto
      have bound := Finset.card_le_card inc
      rw [Finset.card_sdiff_of_subset zd,sz] at bound
      omega
    have left := (rec i (A i) X (fun _ h => h) (ok i) (by change (S\X).card ≤ _; rw [e,sz]; exact Nat.min_le_left ..)
      (by change (X\S).card ≤ _; simp [Finset.sdiff_eq_empty_iff_subset.mpr (show X ⊆ S from Finset.sdiff_subset)])).1
    have right := (rec j (B j) Y (ok j) (fun _ h => h) (by change (T\Y).card ≤ _; simp [Finset.sdiff_eq_empty_iff_subset.mpr (show T ⊆ Y from Finset.subset_union_left)]) gain).2
    exact conflict (left.trans ((hm sub).trans right))

noncomputable def outputs (test : Fin m → X → Prop) (O : Fin m → SetOf k) (x : X) :=
  Finset.univ.filter (fun j => ∃i,test i x ∧ j∈O i)

noncomputable def enc (A : Fin m → SetOf r) (P : Fin m → SetOf k) := outputs (fun i X => A i ⊆ X) P
noncomputable def dec (P : Fin m → SetOf k) (A : Fin m → SetOf r) (a : Fin m → ℕ) :=
  outputs (fun i Y => (P i\Y).card ≤ a i) A
theorem member (test : Fin m → X → Prop) (O : Fin m → SetOf k) (x : X) (b) :
    b∈outputs test O x ↔ ∃ i,test i x ∧ b∈O i := by simp [outputs]
theorem sem (A B : Fin m → SetOf r) (P N : Fin m → SetOf k) (a f : Fin m → ℕ) (cv : Cover A B a f P N) :
    (∀i X,A i ⊆ X → X ⊆ B i → P i ⊆ enc A P X ∧ Disjoint (N i) (enc A P X)) ∧
    ∀i Y,(P i\Y).card ≤ a i → ((N i)∩Y).card ≤ f i → A i ⊆ dec P A a Y ∧ dec P A a Y ⊆ B i := by
  constructor
  · intro i X ax xb
    refine ⟨fun x hx => (member _ _ _ _).mpr ⟨i,ax,hx⟩,Finset.disjoint_left.mpr ?_⟩
    intro x nx gx
    obtain ⟨j,sub,px⟩ := (member _ _ _ _).mp gx
    exact Finset.disjoint_left.mp ((cv j i).1 (sub.trans xb)) px nx
  · intro i Y lost gained
    refine ⟨fun x hx => (member _ _ _ _).mpr ⟨i,lost,hx⟩,?_⟩
    intro x hx
    obtain ⟨j,accept,mem⟩ := (member _ _ _ _).mp hx
    by_contra miss
    have gap := (cv j i).2 (fun h => miss (h mem))
    have cover : P j∩N i ⊆ (P j\Y)∪(N i∩Y) := by
      intro b hb
      simp only [Finset.mem_inter,Finset.mem_union,Finset.mem_sdiff] at *
      tauto
    have cap := (Finset.card_le_card cover).trans (Finset.card_union_le ..)
    omega

theorem possible (A B : Fin m → SetOf r) (a f : Fin m → ℕ) (P N : Fin m → SetOf k) (cv : Cover A B a f P N) : Possible A B a f k := by
  obtain ⟨en,de⟩ := sem A B P N a f cv
  refine ⟨enc A P,dec P A a,?_,?_,?_⟩
  · intro X Y xy b mem
    obtain ⟨i,ok,hit⟩ := (member _ _ _ _).mp mem
    exact (member _ _ _ _).mpr ⟨i,ok.trans xy,hit⟩
  · intro X Y xy b mem
    obtain ⟨i,ok,hit⟩ := (member _ _ _ _).mp mem
    exact (member _ _ _ _).mpr ⟨i,(Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) xy)).trans ok,hit⟩
  · intro i X Y ax xb lost gain
    obtain ⟨ps,ns⟩ := en i X ax xb
    apply de
    · exact (Finset.card_le_card (Finset.sdiff_subset_sdiff ps (Finset.Subset.refl _))).trans lost
    · apply le_trans (Finset.card_le_card (t:=Y\enc A P X) _) gain
      intro x hx
      obtain ⟨neg,yy⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_sdiff.mpr ⟨yy,Finset.disjoint_left.mp ns neg⟩
end PEqualNP.Outside.L_lib_1442_aux.Semantic

namespace PEqualNP.Outside.L_lib_1442_aux
open scoped BigOperators Classical
variable {I J : Type} [Fintype I] [Fintype J]
abbrev Vec (I J : Type) := ℕ × (I → ℕ) × (J → ℕ)
def Good (allowed : I → Prop) (row : J → Finset I) (t : ℕ) (w : I → ℕ) :=
  (∀i, ¬ allowed i → w i=0) ∧ ∀j,t ≤ (row j).sum w
def mass (w : I → ℕ) := ∑i,w i
def validVec (allowed : I → Prop) (row : J → Finset I) (v : Vec I J) :=
  (∀i, ¬ allowed i → v.2.1 i=0) ∧ ∀j,v.1+v.2.2 j=(row j).sum v.2.1
def vectors (allowed : I → Prop) (row : J → Finset I) : AddSubmonoid (Vec I J) := by
  refine { carrier := {x | validVec allowed row x}, zero_mem' := ?_, add_mem' := ?_ }
  · rintro x y ⟨hx,hs⟩ ⟨hy,ht⟩
    constructor
    · intro i bad; change x.2.1 i+y.2.1 i=0; rw [hx i bad,hy i bad]
    · intro j
      change (x.1+y.1)+(x.2.2 j+y.2.2 j)=(row j).sum (fun i => x.2.1 i+y.2.1 i)
      rw [Finset.sum_add_distrib,←hs,←ht]; omega
  · constructor <;> simp
theorem vectorsFG (allowed : I → Prop) (row : J → Finset I) : (vectors allowed row).FG := by
  apply AddSubmonoid.fg_of_subtractive
  rintro x ⟨hx,hs⟩ y ⟨hy,ht⟩
  constructor
  · intro i bad; have h := hy i bad; change x.2.1 i+y.2.1 i=0 at h; omega
  · intro j; have h := ht j
    change (x.1+y.1)+(x.2.2 j+y.2.2 j)=(row j).sum (fun i => x.2.1 i+y.2.1 i) at h
    rw [Finset.sum_add_distrib,←hs] at h
    have hh : (x.1+x.2.2 j)+(y.1+y.2.2 j)=(x.1+x.2.2 j)+(row j).sum y.2.1 := by
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h
    exact Nat.add_left_cancel hh
def lift (row : J → Finset I) (t : ℕ) (w : I → ℕ) : Vec I J :=
  (t,w,fun j => (row j).sum w-t)
theorem goodLift {allowed : I → Prop} {row : J → Finset I} (h : Good allowed row t w) :
    lift row t w ∈ vectors allowed row := by
  exact ⟨h.1,fun j => Nat.add_sub_of_le (h.2 j)⟩
theorem vecGood {allowed : I → Prop} {row : J → Finset I} {x : Vec I J} (h : x∈vectors allowed row) :
    Good allowed row x.1 x.2.1 := ⟨h.1,fun j => by have := h.2 j; omega⟩
theorem fromGenerators {K : Finset (Vec I J)} {P : Vec I J → Prop} (zero : P 0)
    (join : ∀x y,P x → P y → P (x+y)) (gens : ∀x∈K,P x) {v} (mem : v∈AddSubmonoid.closure (K : Set (Vec I J))) : P v :=
  AddSubmonoid.closure_induction (motive:=fun x _ => P x) gens zero (fun x y _ _ => join x y) mem

theorem best {allowed : I → Prop} {row : J → Finset I} {initial : I → ℕ}
    (init : Good allowed row 1 initial) :
    ∃ v : ℕ, ∃ w : I → ℕ, 0<v ∧ Good allowed row v w ∧
      ∀ t w', Good allowed row t w' → mass w*t ≤ v*mass w' := by
  classical
  obtain ⟨S,hS,finite⟩ := (AddSubmonoid.fg_iff _).mp (vectorsFG allowed row)
  let K := finite.toFinset
  have gen : AddSubmonoid.closure (K : Set (Vec I J))=vectors allowed row := by simpa [K] using hS
  let live := K.filter (fun x => 0<x.1)
  have ne : live.Nonempty := by
    by_contra empty
    have each (x) (mem : x∈K) : x.1=0 := by
      by_contra h
      exact empty ⟨x,Finset.mem_filter.mpr ⟨mem,Nat.pos_of_ne_zero h⟩⟩
    have h := fromGenerators (P:=fun x => x.1=0) rfl (fun x y hx hy => by change x.1+y.1=0; omega)
      each (v:=lift row 1 initial) (gen.symm ▸ goodLift init)
    exact Nat.one_ne_zero h
  let ratio (x : Vec I J) := (mass x.2.1 : ℚ)/x.1
  obtain ⟨v,hv,lowest⟩ := live.exists_min_image ratio ne
  obtain ⟨vk,vpos⟩ := Finset.mem_filter.mp hv
  have vc : v∈AddSubmonoid.closure (K : Set _) := AddSubmonoid.subset_closure vk
  refine ⟨v.1,v.2.1,vpos,vecGood (gen ▸ vc),?_⟩
  intro t w' feasible
  let P (x : Vec I J) := mass v.2.1*x.1 ≤ v.1*mass x.2.1
  have each (x) (hx : x∈K) : P x := by
    by_cases h : 0<x.1
    · have cmp := lowest x (Finset.mem_filter.mpr ⟨hx,h⟩)
      have q := (div_le_div_iff₀ (show (0:ℚ)<v.1 by exact_mod_cast vpos) (show (0:ℚ)<x.1 by exact_mod_cast h)).mp cmp
      dsimp [P]
      rw [Nat.mul_comm v.1]; exact_mod_cast q
    · simp [P,show x.1=0 by omega]
  have join (x y) (hx : P x) (hy : P y) : P (x+y) := by
    change _ ≤ _ at hx hy
    have eq : mass (x+y).2.1=mass x.2.1+mass y.2.1 := Finset.sum_add_distrib
    simpa only [P,Prod.fst_add,eq,Nat.mul_add] using Nat.add_le_add hx hy
  exact fromGenerators (P:=P) (by simp [P,mass]) join each (v:=lift row t w') (gen.symm ▸ goodLift feasible)
end PEqualNP.Outside.L_lib_1442_aux

namespace PEqualNP.Outside.L_lib_1442_aux
theorem eventual {u v : ℕ} (pos : 0<v) (W : ℕ → ℕ)
    (floorB : ∀t,u*t≤v*W t) (increment : ∀t,W (t+v)≤W t+u) :
    ∃n₀,∀t≥n₀,W (t+v)=W t+u := by
  classical
  let E (t : ℕ) := v*W t-u*t
  have step (t) : E (t+v) ≤ E t := by
    have h := Nat.mul_le_mul_left v (increment t)
    have lo := floorB t
    dsimp [E]
    rw [Nat.mul_add] at h ⊢
    rw [Nat.mul_comm v u] at h; omega
  have walk (t j : ℕ) : E (t+j*v)≤E t := by
    induction j with
    | zero => simp
    | succ j ih => simpa only [Nat.succ_mul,Nat.add_assoc] using (step (t+j*v)).trans ih
  have minima (i : Fin v) : ∃b,∀j,E (i.val+b*v)≤E (i.val+j*v) := by
    have ex : ∃n,∃b,E (i.val+b*v)=n := ⟨_,0,rfl⟩
    obtain ⟨b,hb⟩ := Nat.find_spec ex
    exact ⟨b,fun j => hb ▸ Nat.find_min' ex ⟨j,rfl⟩⟩
  choose ix least using minima
  let cap := Finset.univ.sup ix
  refine ⟨(cap+1)*v,?_⟩
  intro t large
  let i : Fin v := ⟨t%v,Nat.mod_lt _ pos⟩
  have ixcap : ix i≤cap := Finset.le_sup (f:=ix) (Finset.mem_univ i)
  have capdiv : cap+1≤t/v := (Nat.le_div_iff_mul_le pos).mpr large
  let j := t/v-ix i
  have kj : ix i+j=t/v := by dsimp [j]; omega
  have repr : i.val+(ix i+j)*v=t := by rw [kj,Nat.mul_comm]; exact Nat.mod_add_div _ _
  have low := least i (ix i+j+1)
  rw [Nat.succ_mul,←Nat.add_assoc,repr] at low
  have capwalk := walk (i.val+ix i*v) j
  have repr' : i.val+ix i*v+j*v=t := by simpa [Nat.add_mul,Nat.add_assoc] using repr
  rw [repr'] at capwalk
  have eq : E t=E (t+v) := le_antisymm (capwalk.trans low) (step _)
  have a := floorB t
  have b := floorB (t+v)
  unfold E at eq
  rw [Nat.mul_add] at eq b
  have product : v*W (t+v)=v*(W t+u) := by rw [Nat.mul_add,Nat.mul_comm v u]; omega
  exact Nat.eq_of_mul_eq_mul_left pos product
end PEqualNP.Outside.L_lib_1442_aux

namespace PEqualNP.Outside.L_lib_1442_aux
open scoped BigOperators Classical
variable {I J : Type} [Fintype I] [Fintype J]
def Frac (allowed : I → Prop) (row : J → Finset I) (w : I → ℚ) :=
  (∀i,0≤w i) ∧ (∀i,¬allowed i → w i=0) ∧ ∀j,1≤(row j).sum w
def Can (allowed : I → Prop) (row : J → Finset I) (k t : ℕ) := ∃w,Good allowed row t w ∧ mass w≤k
theorem scale {allowed : I → Prop} {row : J → Finset I} (h : Good allowed row t w) (j : ℕ) :
    Good allowed row (j*t) (fun i => j*w i) := by
  refine ⟨fun i no => by simp only [h.1 i no,Nat.mul_zero],?_⟩
  intro a; rw [←Finset.mul_sum]; exact Nat.mul_le_mul_left _ (h.2 a)
theorem joinGood {allowed : I → Prop} {row : J → Finset I} (h : Good allowed row t w) (g : Good allowed row v z) :
    Good allowed row (t+v) (fun i => w i+z i) := by
  exact ⟨fun i no => by simp only [h.1 i no,g.1 i no,Nat.add_zero],fun j => by rw [Finset.sum_add_distrib]; exact Nat.add_le_add (h.2 j) (g.2 j)⟩
theorem clearFractions {allowed : I → Prop} {row : J → Finset I} {p : I → ℚ}
    (fp : Frac allowed row p) :
    ∃s : ℕ,∃w : I → ℕ, 0<s ∧ Good allowed row s w ∧ ∀i,(w i : ℚ)=p i*s := by
  classical
  let s := ∏i,(p i).den
  have pos : 0<s := Finset.prod_pos fun i _ => (p i).den_pos
  have dvd (i) : (p i).den ∣ s := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  choose mult hm using dvd
  let w i := (p i).num.toNat*mult i
  have hw i : (w i : ℚ)=p i*s := by
    dsimp [w]
    rw [Nat.cast_mul,←Int.cast_natCast,Int.toNat_of_nonneg (Rat.num_nonneg.mpr (fp.1 i))]
    rw [hm i,Nat.cast_mul,←mul_assoc,Rat.mul_den_eq_num]
  refine ⟨s,w,pos,⟨?_,?_⟩,hw⟩
  · intro i no
    have hh := hw i
    rw [fp.2.1 i no,zero_mul] at hh
    exact_mod_cast hh
  · intro j
    have le := mul_le_mul_of_nonneg_right (fp.2.2 j) (show (0:ℚ) ≤ (s:ℚ) by positivity)
    rw [one_mul,Finset.sum_mul] at le
    simp_rw [←hw] at le
    exact_mod_cast le

theorem optimum {allowed : I → Prop} {row : J → Finset I} {one : I → ℕ}
    (base : Good allowed row 1 one) :
    ∃(W : ℕ → ℕ) (u v n₀ : ℕ), 0<v ∧ (∀k t,Can allowed row k t ↔ W t≤k) ∧
      (∃p,Frac allowed row p ∧ ∑i,p i=(u:ℚ)/v) ∧
      (∀p,Frac allowed row p → (u:ℚ)/v≤∑i,p i) ∧
      (∀t,u*t≤v*W t) ∧ (∀j,W (j*v)=j*u) ∧ ∀t≥n₀,W (t+v)=W t+u := by
  classical
  obtain ⟨v,w,pos,hw,bound⟩ := best base
  let u := mass w
  have ex t : ∃k,Can allowed row k t := ⟨_,_,by simpa using scale base t,le_rfl⟩
  let W t := Nat.find (ex t)
  have spec t : Can allowed row (W t) t := Nat.find_spec (ex t)
  have small {k t} (can : Can allowed row k t) : W t≤k := Nat.find_min' (ex t) can
  have equival k t : Can allowed row k t ↔ W t≤k := by
    refine ⟨small,?_⟩
    intro h
    obtain ⟨z,hz,b⟩ := spec t
    exact ⟨z,hz,b.trans h⟩
  have lower t : u*t≤v*W t := by
    obtain ⟨z,hz,b⟩ := spec t
    exact (bound t z hz).trans (Nat.mul_le_mul_left _ b)
  have step t : W (t+v)≤W t+u := by
    obtain ⟨z,hz,b⟩ := spec t
    exact small ⟨_,joinGood hz hw,by simpa [mass,u,Finset.sum_add_distrib] using Nat.add_le_add_right b (mass w)⟩
  obtain ⟨n₀,last⟩ := eventual pos W lower step
  refine ⟨W,u,v,n₀,pos,equival,?_,?_,lower,?_,last⟩
  · let p i := (w i : ℚ)/v
    have qpos : (0:ℚ)<v := by exact_mod_cast pos
    refine ⟨p,⟨fun i => div_nonneg (by positivity) qpos.le,fun i no => by simp [p,hw.1 i no],?_⟩,?_⟩
    · intro j; dsimp [p]; rw [←Finset.sum_div,le_div_iff₀ qpos,one_mul]; exact_mod_cast hw.2 j
    · simp only [p,←Finset.sum_div,u,mass,Nat.cast_sum]
  · intro p hp
    obtain ⟨s,z,hs,hz,vals⟩ := clearFractions hp
    have cmp : (u:ℚ)*s≤(v:ℚ)*((∑i,z i:ℕ):ℚ) := by exact_mod_cast bound s z hz
    simp only [Nat.cast_sum,vals,←Finset.sum_mul] at cmp
    rw [←mul_assoc] at cmp
    have q := (le_of_mul_le_mul_right cmp (show (0:ℚ)<s by exact_mod_cast hs))
    exact (div_le_iff₀ (by exact_mod_cast pos : (0:ℚ)<v)).mpr (by simpa [mul_comm] using q)
  · intro j
    apply le_antisymm
    · exact small ⟨_,scale hw j,by simp only [mass,←Finset.mul_sum,u,le_refl]⟩
    · have low := lower (j*v)
      exact Nat.le_of_mul_le_mul_left (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using low : v*(j*u) ≤ v*W (j*v)) pos
end PEqualNP.Outside.L_lib_1442_aux

namespace PEqualNP.Outside.L_lib_1442_aux
open scoped BigOperators Classical
variable {I J : Type} [Fintype I] [Fintype J]
noncomputable def hit (C : Fin k → I) (S : Finset I) :=
  (Finset.univ.filter (fun z => C z∈S)).card
def Columns (allowed : I → Prop) (row : J → Finset I) (k t : ℕ) :=
  ∃ C : Fin k → I, (∀z,allowed (C z)) ∧ ∀j,t≤hit C (row j)
theorem columns_iff {allowed : I → Prop} {row : J → Finset I} (safe : I) (ok : allowed safe) :
    Columns allowed row k t ↔ Can allowed row k t := by
  classical
  constructor
  · rintro ⟨C,valid,cover⟩
    let w i := (Finset.univ.filter (fun z => C z=i)).card
    have sum (S : Finset I) : S.sum w=hit C S := by
      exact Finset.sum_card_fiberwise_eq_card_filter _ _ C
    refine ⟨w,⟨?_,fun j => (sum (row j)).symm ▸ cover j⟩,?_⟩
    · intro i bad
      apply Finset.card_eq_zero.mpr; apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz; have eq := (Finset.mem_filter.mp hz).2
      exact bad (eq ▸ valid z)
    · unfold mass; rw [sum]; simp [hit]
  · rintro ⟨w,h,b⟩
    let K := (i : I) × Fin (w i)
    have room : Fintype.card K≤k := by simpa [K,Fintype.card_sigma,mass] using b
    let e : K ↪ Fin k := (Fintype.equivFin K).toEmbedding.trans (Fin.castLEEmb room)
    let C (z : Fin k) := if ex : ∃x,e x=z then (Classical.choose ex).1 else safe
    have ec (x : K) : C (e x)=x.1 := by
      have h : ∃y,e y=e x := ⟨_,rfl⟩
      simp only [C,dif_pos h]; exact congrArg Sigma.fst (e.injective (Classical.choose_spec h))
    refine ⟨C,?_,?_⟩
    · intro z
      by_cases ex : ∃x,e x=z
      · obtain ⟨x,rfl⟩ := ex
        rw [ec]
        by_contra no
        have bad := h.1 x.1 no
        have sm := x.2.isLt
        omega
      · simpa only [C,dif_neg ex] using ok
    · intro j
      let M := (row j).sigma (fun i => (Finset.univ : Finset (Fin (w i))))
      have sub : M.map e ⊆ Finset.univ.filter (fun z => C z∈row j) := by
        intro z hz
        obtain ⟨x,mem,rfl⟩ := Finset.mem_map.mp hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ec x ▸ (Finset.mem_sigma.mp mem).1⟩
      have size : M.card=(row j).sum w := by dsimp [M]; rw [Finset.card_sigma]; simp
      have count := Finset.card_le_card sub
      rw [Finset.card_map,size] at count
      exact (h.2 j).trans count
end PEqualNP.Outside.L_lib_1442_aux

namespace PEqualNP.Outside.L_lib_1442_aux
open scoped Classical
open PEqualNP.Outside.L_lib_1442_aux.Semantic
abbrev Rect (m : ℕ) := SetOf m × SetOf m
abbrev Conflict (A B : Fin m → SetOf r) := {e : Fin m × Fin m // ¬ A e.1 ⊆ B e.2}
def Allowed (A B : Fin m → SetOf r) (c : Rect m) := ¬ ∃i∈c.1, ∃j∈c.2, A i ⊆ B j
def rows (A B : Fin m → SetOf r) (e : Conflict A B) := Finset.univ.filter (fun c : Rect m => e.val.1∈c.1 ∧ e.val.2∈c.2)
theorem inRow {A B : Fin m → SetOf r} (e : Conflict A B) (c : Rect m) : c∈rows A B e ↔ e.val.1∈c.1 ∧ e.val.2∈c.2 := by simp [rows]
def Fits (A B : Fin m → SetOf r) (k t : ℕ) :=
   ∃(g : SetOf r → SetOf k) (h : SetOf k → SetOf r), Monotone g ∧ Monotone h ∧
   ∀ i X Y, A i ⊆ X → X ⊆ B i → Y ⊆ g X → (g X \ Y).card<t → A i ⊆ h Y ∧ h Y ⊆ B i
theorem fitsSucc (A B : Fin m → SetOf r) (ok : ∀i,A i⊆B i) (s k : ℕ) :
    Fits A B k (s+1) ↔ ∃P N : Fin m → SetOf k,Cover A B (fun _ => s) (fun _ => 0) P N := by
  constructor
  · rintro ⟨g,h,gm,hm,ev⟩
    apply necessity A B _ _ ok
    refine ⟨g,h,gm,hm,?_⟩
    intro i X Y ax xb lost gain
    dsimp only at lost gain
    apply ev i X Y ax xb _ (by omega)
    apply Finset.sdiff_eq_empty_iff_subset.mp
    exact Finset.card_eq_zero.mp (by omega)
  · rintro ⟨P,N,hc⟩
    obtain ⟨g,h,gm,hm,ev⟩ := possible A B _ _ P N hc
    refine ⟨g,h,gm,hm,?_⟩
    intro i X Y ax xb sub lost
    exact ev i X Y ax xb (show (g X \ Y).card ≤ s by omega) (by rw [Finset.sdiff_eq_empty_iff_subset.mpr sub]; simp)
theorem covered (A B : Fin m → SetOf r) (s k : ℕ) :
    (∃P N : Fin m → SetOf k,Cover A B (fun _ => s) (fun _ => 0) P N) ↔
      Columns (Allowed A B) (rows A B) k (s+1) := by
  classical
  constructor
  · rintro ⟨P,N,cv⟩
    let C (z : Fin k) : Rect m := (Finset.univ.filter (fun i => z∈P i),Finset.univ.filter (fun j => z∈N j))
    refine ⟨C,?_,?_⟩
    · rintro z ⟨i,pi,j,nj,sub⟩
      exact Finset.disjoint_left.mp ((cv i j).1 sub) (Finset.mem_filter.mp pi).2 (Finset.mem_filter.mp nj).2
    · intro e
      have eq : hit C (rows A B e)=(P e.val.1 ∩ N e.val.2).card := by
        unfold hit; congr 1; ext z; simp [C,inRow,rows]
      rw [eq]; simpa using (cv _ _).2 e.property
  · rintro ⟨C,allowed,covers⟩
    let P i := Finset.univ.filter (fun z => i∈(C z).1)
    let N j := Finset.univ.filter (fun z => j∈(C z).2)
    refine ⟨P,N,?_⟩
    intro i j
    constructor
    · intro sub
      apply Finset.disjoint_left.mpr
      intro z pi nj; exact allowed z ⟨i,(Finset.mem_filter.mp pi).2,j,(Finset.mem_filter.mp nj).2,sub⟩
    · intro miss
      let e : Conflict A B := ⟨(i,j),miss⟩
      have eq : hit C (rows A B e)=(P i∩N j).card := by
        unfold hit; congr 1; ext z; simp [P,N,rows,e]
      have h := covers e
      rw [eq] at h; simpa using h

theorem fitsCan (A B : Fin m → SetOf r) (ok : ∀i,A i⊆B i) (k t : ℕ) :
    Fits A B k t ↔ Can (Allowed A B) (rows A B) k t := by
  have safe : Allowed A B (∅,∅) := by simp [Allowed]
  cases t with
  | zero =>
    have ff : Fits A B k 0 := ⟨fun _ => ∅,fun _ => ∅,monotone_const,monotone_const,fun _ _ _ _ _ _ h => (Nat.not_lt_zero _ h).elim⟩
    have cc : Can (Allowed A B) (rows A B) k 0 :=
      ⟨fun _ => 0,⟨fun _ _ => rfl,fun _ => Nat.zero_le _⟩,by simp [mass]⟩
    exact ⟨fun _ => cc,fun _ => ff⟩
  | succ s => exact (fitsSucc A B ok s k).trans ((covered A B s k).trans (columns_iff _ safe))
theorem unitExists (A B : Fin m → SetOf r) : ∃w,Good (Allowed A B) (rows A B) 1 w := by
  classical
  let w (c : Rect m) := if Allowed A B c then 1 else 0
  refine ⟨w,⟨fun i bad => by simp [w,bad],?_⟩⟩
  intro e
  let c : Rect m := ({e.val.1},{e.val.2})
  have valid : Allowed A B c := by simpa [Allowed,c] using e.property
  have mem : c∈rows A B e := (inRow _ _).mpr (by simp [c])
  simpa [w,valid] using (Finset.single_le_sum (fun i _ => Nat.zero_le (w i)) mem : w c≤(rows A B e).sum w)
end PEqualNP.Outside.L_lib_1442_aux

namespace PEqualNP.Outside.L_lib_1442_aux
open PEqualNP.Outside.L_lib_1442_aux.Semantic
def minus (A B : SetOf n) := A \ B
theorem sameDiff (d : DecidableEq (Fin n)) (A B : SetOf n) :
    @SDiff.sdiff _ (@Finset.instSDiff _ d) A B=minus A B := by ext x; simp only [minus,Finset.mem_sdiff]
noncomputable def select {α : Type*} (P : α → Prop) (A : Finset α) := @Finset.filter α P (fun _ => Classical.propDecidable _) A
theorem sameFilter {α : Type*} (P : α → Prop) (d : DecidablePred P) (A : Finset α) : @Finset.filter α P d A=select P A := by
  ext x; simp only [select,Finset.mem_filter]
end PEqualNP.Outside.L_lib_1442_aux
open PEqualNP.Outside.L_lib_1442_aux in
theorem PEqualNP.Outside.L_lib_1442 : letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
∀ (m r : Nat) (A B : Fin m → Finset (Fin r)), (∀ i, A i ⊆ B i) →
  let fits := fun (k t : Nat) => ∃ (g : Finset (Fin r) → Finset (Fin k)) (h : Finset (Fin k) → Finset (Fin r)),
    Monotone g ∧ Monotone h ∧ ∀ i X Y, A i ⊆ X → X ⊆ B i → Y ⊆ g X →
      (g X \ Y).card < t → A i ⊆ h Y ∧ h Y ⊆ B i
  let R := Finset (Fin m) × Finset (Fin m)
  let frac := fun (w : R → ℚ) => (∀ c, 0 ≤ w c) ∧
    (∀ c, (∃ i ∈ c.1, ∃ j ∈ c.2, A i ⊆ B j) → w c=0) ∧
    (∀ i j, ¬ A i ⊆ B j → 1 ≤ ((Finset.univ : Finset R).filter (fun c => i ∈ c.1 ∧ j ∈ c.2)).sum w)
  ∃ (width : Nat → Nat) (u v n₀ : Nat), 0<v ∧ (∀ k t, fits k t ↔ width t ≤ k) ∧
    (∃ w, frac w ∧ (Finset.univ : Finset R).sum w=(u:ℚ)/(v:ℚ)) ∧
    (∀ w, frac w → (u:ℚ)/(v:ℚ) ≤ (Finset.univ : Finset R).sum w) ∧
    (∀ t, u*t ≤ v*width t) ∧ (∀ j, width (j*v)=j*u) ∧
    ∀ t ≥ n₀, width (t+v)=width t+u := by
  classical
  intro m r A B ok fits R frac
  have fitEq (k t : ℕ) : fits k t ↔ Fits A B k t := by simp only [fits,Fits,sameDiff]
  have fracEq (p : Rect m → ℚ) : frac p ↔ Frac (Allowed A B) (rows A B) p := by
    constructor
    · rintro ⟨nonneg,bad,edges⟩
      refine ⟨nonneg,fun c h => bad c (Classical.not_not.mp h),?_⟩
      intro e; simpa only [rows,sameFilter] using edges e.val.1 e.val.2 e.property
    · rintro ⟨nonneg,bad,edges⟩
      refine ⟨nonneg,fun c h => bad c (fun allowed => allowed h),?_⟩
      intro i j miss; simpa only [rows,sameFilter] using edges (⟨(i,j),miss⟩ : Conflict A B)
  obtain ⟨one,ho⟩ := unitExists A B
  obtain ⟨W,u,v,n₀,pos,eqv,⟨p,hp,value⟩,lower,lb,mult,tail⟩ := optimum ho
  exact ⟨W,u,v,n₀,pos,fun k t => (fitEq k t).trans ((fitsCan A B ok k t).trans (eqv k t)),
    ⟨p,(fracEq p).mpr hp,value⟩,fun w hw => lower w ((fracEq w).mp hw),lb,mult,tail⟩
