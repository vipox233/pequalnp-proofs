import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.Helpers.GraphSampleDistance

namespace PEqualNP.Outside.L_meta_53207_aux
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
end PEqualNP.Outside.L_meta_53207_aux

namespace PEqualNP.Outside.L_meta_53207_aux
open scoped Classical
variable {I : Type} [Fintype I]
theorem erased (P : Finset I → Prop) (up : ∀ A B, A⊆B → P A → P B) (D : ℕ) (w : I → ℕ) :
    (∀ lost : I → ℕ, (∑ i,lost i)<D → P (Finset.univ.filter (fun x => lost x<w x))) ↔
    Good (fun _ => True) (fun j : {s : Finset I // ¬ P s} => Finset.univ \ j.val) D w := by
  classical
  constructor
  · intro h; refine ⟨fun _ no => (no trivial).elim,?_⟩
    intro j; by_contra! small
    let ell (i : I) := if i∈j.val then 0 else w i
    have cost : (∑ i,ell i)=(Finset.univ \ j.val).sum w := by
      have eq : ell = fun i => if i∈Finset.univ \ j.val then w i else 0 := by
        funext i; by_cases m : i∈j.val <;> simp [ell,m]
      rw [eq,←Finset.sum_filter]
      congr 1; ext i; simp
    apply j.property
    apply up _ _ _ (h ell (cost.trans_lt small))
    intro i hi
    by_contra no
    have hh := (Finset.mem_filter.mp hi).2
    simp [ell,no] at hh
  · rintro ⟨_,h⟩ lost small
    by_contra bad
    let B := Finset.univ.filter (fun x => lost x<w x)
    have lb := h ⟨B,bad⟩
    have one : (Finset.univ \ B).sum w ≤ (Finset.univ \ B).sum lost := by
      apply Finset.sum_le_sum
      intro i hi; have hh := (Finset.mem_sdiff.mp hi).2
      simpa [B,not_lt] using hh
    exact (Nat.not_le_of_lt small) (lb.trans (one.trans (Finset.sum_le_sum_of_subset (Finset.subset_univ _))))
end PEqualNP.Outside.L_meta_53207_aux

namespace PEqualNP.Outside.L_meta_53207_aux
open scoped Classical
variable {I J : Type} [Fintype I] [Fintype J]
def degree : Vec I J →+ ℕ := AddMonoidHom.fst ℕ _
theorem splitGood (row : J → Finset I) :
    ∃ q T : ℕ,0<q ∧ ∀ D≥T,∀ w : I → ℕ,
    Good (fun _ => True) row (D+q) w ↔ ∃ u v : I → ℕ,
      Good (fun _ => True) row D u ∧ Good (fun _ => True) row q v ∧ ∀i,w i=u i+v i := by
  classical
  let M := vectors (fun _ => True) row
  obtain ⟨S,hS,finite⟩ := (AddSubmonoid.fg_iff _).mp (vectorsFG (fun _ => True) row)
  let K := finite.toFinset
  have gen : AddSubmonoid.closure (K : Set (Vec I J))=M := by simpa [M,K] using hS
  let e (j : K) := degree j.val
  let factor (j : K) := max (e j) 1
  let q := ∏ j : K,factor j
  have pos : 0<q := Finset.prod_pos (fun j _ => (Nat.zero_lt_succ 0).trans_le (le_max_right _ _))
  refine ⟨q,Fintype.card K*q+1,pos,?_⟩
  intro D large w
  constructor
  · intro good
    let x := lift row (D+q) w
    have mem : x∈AddSubmonoid.closure (K : Set (Vec I J)) := gen ▸ goodLift good
    obtain ⟨a,ha⟩ := AddSubmonoid.mem_closure_finset'.mp mem
    have degrees := congrArg (degree (I:=I) (J:=J)) ha
    change degree x = degree (∑ j : K, a j • j.val) at degrees
    simp only [map_sum,map_nsmul,nsmul_eq_mul] at degrees
    change D+q=∑ j : K,a j*e j at degrees
    have big : ∃ j : K,q≤a j*e j := by
      by_contra! h
      have upper := Finset.sum_le_sum (s:=(Finset.univ : Finset K)) (fun j _ => (h j).le)
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at upper
      omega
    obtain ⟨j,hj⟩ := big
    have ej : 0<e j := by by_contra! z; simp [Nat.eq_zero_of_le_zero z] at hj; omega
    have dv : e j ∣ q := by
      have fd := Finset.dvd_prod_of_mem factor (Finset.mem_univ j)
      change max (e j) 1 ∣ q at fd
      rw [max_eq_left (show 1≤e j from ej)] at fd; exact fd
    obtain ⟨m,hm⟩ := dv
    have small : m ≤ a j := Nat.le_of_mul_le_mul_right (by simpa [hm,Nat.mul_comm] using hj) ej
    let b (k : K) := if k=j then m else 0
    have below (k : K) : b k≤a k := by by_cases hk : k=j <;> simp_all [b]
    let v := ∑ k : K,b k • k.val
    let u := ∑ k : K,(a k-b k) • k.val
    have equal : x=u+v := by
      rw [ha]; unfold u v; rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _
      rw [←add_nsmul,Nat.sub_add_cancel (below k)]
    have vm : v∈M := M.sum_mem fun k _ => M.nsmul_mem (gen ▸ AddSubmonoid.subset_closure k.property) _
    have um : u∈M := M.sum_mem fun k _ => M.nsmul_mem (gen ▸ AddSubmonoid.subset_closure k.property) _
    have vd : degree v=q := by simp [v,b,map_sum,hm,e,degree,Nat.mul_comm]
    have ud : degree u=D := by
      have t := congrArg (degree (I:=I) (J:=J)) equal
      rw [map_add,vd] at t
      change D+q=degree u+q at t; omega
    have uv := vecGood um; have vv := vecGood vm
    change u.1=D at ud; change v.1=q at vd
    rw [ud] at uv; rw [vd] at vv
    exact ⟨u.2.1,v.2.1,uv,vv,fun i => congrArg (fun z : Vec I J => z.2.1 i) equal⟩
  · rintro ⟨u,v,hu,hv,h⟩
    refine ⟨fun _ no => (no trivial).elim,fun j => ?_⟩
    simp only [h,Finset.sum_add_distrib]
    exact Nat.add_le_add (hu.2 j) (hv.2 j)
end PEqualNP.Outside.L_meta_53207_aux

namespace PEqualNP.Outside.L_meta_53207_aux
open scoped Classical
variable {I : Type} [Fintype I]
def Optimal (V : ℕ → (I → ℕ) → Prop) (d : ℕ) (w : I → ℕ) :=
  V d w ∧ ∀ u,V d u → mass w ≤ mass u
theorem optimalSplit {V : ℕ → (I → ℕ) → Prop} {D q : ℕ}
    (split : ∀ w,V (D+q) w ↔ ∃u v,V D u ∧ V q v ∧ ∀i,w i=u i+v i) (w : I → ℕ) :
    Optimal V (D+q) w ↔ ∃u v,Optimal V D u ∧ Optimal V q v ∧ ∀i,w i=u i+v i := by
  have weight (u v : I → ℕ) : mass (fun i => u i+v i) = mass u+mass v := Finset.sum_add_distrib
  constructor
  · rintro ⟨ok,best⟩
    obtain ⟨u,v,hu,hv,eq⟩ := (split w).mp ok
    have e : mass w=mass u+mass v := by rw [funext eq,weight]
    refine ⟨u,v,⟨hu,?_⟩,⟨hv,?_⟩,eq⟩
    · intro a ha
      have t := best _ ((split _).mpr ⟨a,v,ha,hv,fun _ => rfl⟩)
      change mass w ≤ mass (fun i => a i+v i) at t
      rw [weight,e] at t; omega
    · intro a ha
      have t := best _ ((split _).mpr ⟨u,a,hu,ha,fun _ => rfl⟩)
      change mass w ≤ mass (fun i => u i+a i) at t
      rw [weight,e] at t; omega
  · rintro ⟨u,v,⟨hu,lu⟩,⟨hv,lv⟩,eq⟩
    refine ⟨(split w).mpr ⟨u,v,hu,hv,eq⟩,?_⟩
    intro a ha
    obtain ⟨b,c,hb,hc,eq'⟩ := (split a).mp ha
    rw [funext eq,funext eq',weight,weight]
    exact Nat.add_le_add (lu b hb) (lv c hc)
theorem eventual (P : Finset I → Prop) (up : ∀ A B,A⊆B → P A → P B) :
    let V := fun (d : ℕ) (w : I → ℕ) => ∀ lost : I → ℕ,(∑i,lost i)<d →
      P (Finset.univ.filter (fun i => lost i<w i))
    ∃ q T : ℕ,0<q ∧ ∀D≥T,∀w,(V (D+q) w ↔ ∃u v,V D u ∧ V q v ∧ ∀i,w i=u i+v i) ∧
      (Optimal V (D+q) w ↔ ∃u v,Optimal V D u ∧ Optimal V q v ∧ ∀i,w i=u i+v i) := by
  classical
  intro V
  let row (s : {s : Finset I // ¬P s}) := Finset.univ \ s.val
  obtain ⟨q,T,hq,h⟩ := splitGood row
  refine ⟨q,T,hq,?_⟩
  intro D hD w
  have step (a : I → ℕ) : V (D+q) a ↔ ∃ u v,V D u ∧ V q v ∧ ∀i,a i=u i+v i := by
    simpa only [V,erased P up,row] using h D hD a
  exact ⟨step w,optimalSplit step w⟩
end PEqualNP.Outside.L_meta_53207_aux

namespace PEqualNP.Outside.L_meta_53207_aux
open scoped Classical
open PEqualNP GraphSampleDistance GraphInversionSeeds
theorem zeroTest (P : Finset α → Prop) (A : Finset α) :
    (∀ lost : α → ℕ, A.sum lost ≤ 0 → P (A.filter (fun x => lost x < 1))) ↔ P A := by
  constructor
  · intro h; simpa using h (fun _ => 0) (by simp)
  · intro h lost z
    have hz (x) (hx : x∈A) : lost x<1 := by
      exact Nat.lt_succ_of_le ((Finset.single_le_sum (f:=lost) (fun i _ => Nat.zero_le (lost i)) hx).trans z)
    rw [Finset.filter_true_of_mem hz]; exact h
theorem upward (E : Finset (Edge n)) (color : Fin n → Fin c)
    (sorted : ∀ e∈E,e.1<e.2) (onto : Function.Surjective color) (part : GraphPriceCalibration.classes E color)
    {A B : Finset (W n)} (sub : A⊆B) (h : keeps A E color) : keeps B E color := by
  classical
  have eq (X : Finset (W n)) := GraphSampleDistance.criterion n c E color onto sorted part X (fun _ => 1) 0 (by simp)
  have r := (eq A).mp ((zeroTest (fun x => keeps x E color) A).mpr h)
  apply (zeroTest (fun x => keeps x E color) B).mp
  apply (eq B).mpr
  simp only [min_self, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_pos, Finset.filter_nonempty_iff] at r ⊢
  obtain ⟨h1,h2,h3⟩ := r
  refine ⟨?_,?_,?_⟩
  · intro j; obtain ⟨x,hx,hd,hy⟩ := h1 j
    exact ⟨x,sub hx,hd,sub hy⟩
  · intro f hf g hg ne; obtain ⟨x,hx,hd⟩ := h2 f hf g hg ne
    exact ⟨x,sub hx,hd⟩
  · intro f hf g hg; obtain ⟨x,hx,hd⟩ := h3 f hf g hg
    exact ⟨x,sub hx,hd⟩
end PEqualNP.Outside.L_meta_53207_aux

namespace PEqualNP.Outside.L_meta_53207_aux
noncomputable def chooseF {α : Type*} (P : α → Prop) (A : Finset α) := @Finset.filter α P (fun _ => Classical.propDecidable _) A
theorem normFilter {α : Type*} (P : α → Prop) (d : DecidablePred P) (A : Finset α) : @Finset.filter α P d A=chooseF P A := by
  ext j; simp only [chooseF,Finset.mem_filter]
end PEqualNP.Outside.L_meta_53207_aux
open PEqualNP PEqualNP.Outside.L_meta_53207_aux in
theorem PEqualNP.Outside.L_meta_53207 : ∀ (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
  (∀ e ∈ E, e.1 < e.2) → Function.Surjective color →
  (∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
    ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) →
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  let bit := fun (i : Fin n) (x : W) => decide (i ∈ x)
  let neg := fun (i : Fin n) (x : W) => !(bit i x)
  let same := fun (e : Fin n × Fin n) (x : W) => bit e.1 x == bit e.2 x
  let raw : Finset (W → Bool) := {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪
    E.image same ∪ E.image (fun e x => !(same e x))
  let need := Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
    E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x)
  let keeps := fun A : Finset W => ∀ (S : W) (p : Nat),
    let L := (raw ∪ S.image neg).toList
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
      C.output < L.length+C.size ∧ C.size ≤ p ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
        ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x) ↔
    (∀ j, ∃ i ∈ S, color i = j) ∧ n+3*E.card-S.card ≤ p
  let valid := fun (D : Nat) (w : W → Nat) =>
    ∀ lost : W → Nat, (∑ x, lost x) < D →
      keeps (Finset.univ.filter (fun x => lost x < w x))
  let total := fun w : W → Nat => ∑ x, w x
  let opt := fun (D : Nat) (w : W → Nat) => valid D w ∧
    ∀ u : W → Nat, valid D u → total w ≤ total u
  ∃ q T : Nat, 0 < q ∧ ∀ D ≥ T, ∀ w : W → Nat,
    (valid (D+q) w ↔ ∃ u v : W → Nat, valid D u ∧ valid q v ∧
      ∀ x : W, w x = u x + v x) ∧
    (opt (D+q) w ↔ ∃ u v : W → Nat, opt D u ∧ opt q v ∧
      ∀ x : W, w x = u x + v x) := by
  classical
  intro n c E color sorted onto part
  intro W' bit' neg' same' raw' need' keeps' valid' total' opt'
  have bitEq (i : Fin n) (x : W') : bit' i x=GraphSeedSamples.bit i x := by
    dsimp only [bit',GraphSeedSamples.bit]; congr 1
  have negEq (i : Fin n) : neg' i=GraphSeedSamples.inv i := by
    funext x; by_cases h : i∈x <;> simp [neg',bit',GraphSeedSamples.inv,h]
  have sameEq (e : Fin n × Fin n) : same' e=GraphSeedSamples.same e := by
    funext x; by_cases h : e.1∈x <;> by_cases k : e.2∈x <;> simp [same',bit',GraphSeedSamples.same,h,k]
  have valEq (i : Fin n) (x : W') (dec : Decidable (i∈x)) : @decide _ dec=bit' i x := by
    dsimp only [bit']; congr 1
  have valN (i : Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.neg i)=(fun x => !bit' i x) := by
    funext x
    dsimp only [GraphSampleDistance.asWord,GraphInversionSeeds.neg]
    simp only [valEq]
  have valZ (e : Fin n × Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.zz e)=(fun x => !bit' e.1 x && !bit' e.2 x) := by
    funext x
    dsimp only [GraphSampleDistance.asWord,GraphInversionSeeds.zz]
    simp only [valEq]
  have valO (e : Fin n × Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.oz e)=(fun x => bit' e.1 x && !bit' e.2 x) := by
    funext x
    dsimp only [GraphSampleDistance.asWord,GraphInversionSeeds.oz]
    simp only [valEq]
  have valT (e : Fin n × Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.zo e)=(fun x => !bit' e.1 x && bit' e.2 x) := by
    funext x
    dsimp only [GraphSampleDistance.asWord,GraphInversionSeeds.zo]
    simp only [valEq]
  have reqEq : GraphSampleDistance.req E=need' := by
    ext f
    simp only [GraphSampleDistance.req,GraphInversionSeeds.target,Finset.image_union,
      Finset.image_image,Function.comp_def,Finset.mem_union,Finset.mem_image,
      Finset.mem_univ,true_and,need',neg',valN,valZ,valO,valT]
  have keepEq (A : Finset W') : keeps' A ↔ GraphSampleDistance.keeps A E color := by
    unfold keeps' GraphSampleDistance.keeps
    apply forall_congr'; intro S
    apply forall_congr'; intro p
    dsimp only
    generalize hl : Finset.toList _ = actual
    have eq : actual=GraphSampleDistance.wire E S := by
      rw [←hl]
      congr 1
      ext f
      simp only [raw',GraphSeedSamples.bank,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.mem_image,Finset.mem_univ,true_and,funext (fun i => funext (bitEq i)),funext negEq,
        funext sameEq,GraphSeedSamples.cross]
      rfl
    rw [eq]
    simp only [GraphSampleDistance.fitsAt,reqEq,GraphSeedSamples.cover]
    rfl
  have up A B (sub : A⊆B) (h : keeps' A) : keeps' B :=
    (keepEq B).mpr (upward E color sorted onto part sub ((keepEq A).mp h))
  have sol := eventual keeps' up
  dsimp only at sol
  dsimp only [opt',valid',total',Optimal,mass]
  simpa only [Optimal,mass,normFilter] using sol
