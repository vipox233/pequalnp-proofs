import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_930_aux



namespace LoosePathRoot
open Finset

def triple (t : Nat) : Finset Nat := {2*t,2*t+1,2*t+2}

def pairAt (r t : Nat) : Finset Nat :=
  if 2*t+2 ≤ r then {2*t,2*t+1}
  else if r ≤ 2*t then {2*t+1,2*t+2}
  else {2*t,2*t+2}

theorem pair_cases (t : Nat) (A : Finset Nat) (hs : A ⊆ triple t) (hc : A.card=2) :
    A={2*t,2*t+1} ∨ A={2*t,2*t+2} ∨ A={2*t+1,2*t+2} := by
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hc
  have hx := hs (Finset.mem_insert_self x {y})
  have hy := hs (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
  simp only [triple,Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
    simp_all [Finset.pair_comm]

theorem add_right (e r : Nat) (hr : r ≤ 2*e) :
    (Finset.range (2*e+1) \ {r}) ∪ {2*e+1,2*e+2} =
      Finset.range (2*(e+1)+1) \ {r} := by
  ext x
  simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_range,
    Finset.mem_insert,Finset.mem_singleton]
  omega

theorem add_left (e : Nat) :
    (Finset.range (2*e+1) \ {2*e}) ∪ {2*e,2*e+1} =
      Finset.range (2*(e+1)+1) \ {2*e+2} := by
  ext x
  simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_range,
    Finset.mem_insert,Finset.mem_singleton]
  omega

theorem add_outer (e : Nat) :
    (Finset.range (2*e+1) \ {2*e}) ∪ {2*e,2*e+2} =
      Finset.range (2*(e+1)+1) \ {2*e+1} := by
  ext x
  simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_range,
    Finset.mem_insert,Finset.mem_singleton]
  omega

theorem canonical_end (e t : Nat) (ht : t<e) :
    pairAt (2*e) t = pairAt (2*e+1) t ∧ pairAt (2*e) t = pairAt (2*e+2) t := by
  have h0 : 2*t+2 ≤ 2*e := by omega
  have h1 : 2*t+2 ≤ 2*e+1 := by omega
  have h2 : 2*t+2 ≤ 2*e+2 := by omega
  simp only [pairAt,if_pos h0,if_pos h1,if_pos h2,and_self]

theorem root_exists (e : Nat) (f : Nat → Finset Nat)
    (hs : ∀ t<e, f t ⊆ triple t)
    (hc : ∀ t<e, (f t).card=2)
    (hd : ∀ i<e, ∀ j<e, i≠j → Disjoint (f i) (f j)) :
    ∃ r, r≤2*e ∧ (∀ t<e, f t=pairAt r t) ∧
      (Finset.range e).biUnion f = Finset.range (2*e+1) \ {r} := by
  induction e with
  | zero =>
    refine ⟨0,by omega,by omega,?_⟩
    simp
  | succ e ih =>
    obtain ⟨r,hr,hf,hunion⟩ := ih (fun t ht => hs t (by omega))
      (fun t ht => hc t (by omega)) (fun i hi j hj hij => hd i (by omega) j (by omega) hij)
    have hdis : Disjoint ((Finset.range e).biUnion f) (f e) := by
      apply Finset.disjoint_left.mpr
      intro x hx hxe
      obtain ⟨t,ht,hxt⟩ := Finset.mem_biUnion.mp hx
      exact Finset.disjoint_left.mp (hd t (by have := Finset.mem_range.mp ht; omega) e (by omega)
        (Nat.ne_of_lt (Finset.mem_range.mp ht))) hxt hxe
    have hforce (he : 2*e ∈ f e) : r=2*e := by
      by_contra hne
      have hm : 2*e ∈ (Finset.range e).biUnion f := by
        rw [hunion]
        simp only [Finset.mem_sdiff,Finset.mem_range,Finset.mem_singleton]
        exact ⟨by omega,Ne.symm hne⟩
      exact Finset.disjoint_left.mp hdis hm he
    have hbi : (Finset.range (e+1)).biUnion f = (Finset.range e).biUnion f ∪ f e := by
      rw [Finset.range_add_one,Finset.biUnion_insert,Finset.union_comm]
    rcases pair_cases e (f e) (hs e (by omega)) (hc e (by omega)) with he|he|he
    · have hre : r=2*e := hforce (by simp [he])
      subst r
      refine ⟨2*e+2,by omega,?_,?_⟩
      · intro t ht
        by_cases hte : t<e
        · exact (hf t hte).trans (canonical_end e t hte).2
        · have hte : t=e := by omega
          subst t
          simp [he,pairAt]
      · rw [hbi,hunion,he]
        exact add_left e
    · have hre : r=2*e := hforce (by simp [he])
      subst r
      refine ⟨2*e+1,by omega,?_,?_⟩
      · intro t ht
        by_cases hte : t<e
        · exact (hf t hte).trans (canonical_end e t hte).1
        · have hte : t=e := by omega
          subst t
          simp [he,pairAt]
      · rw [hbi,hunion,he]
        exact add_outer e
    · refine ⟨r,by omega,?_,?_⟩
      · intro t ht
        by_cases hte : t<e
        · exact hf t hte
        · have hte : t=e := by omega
          subst t
          have hn : ¬2*e+2≤r := by omega
          simp [he,pairAt,hn,hr]
      · rw [hbi,hunion,he]
        exact add_right e r hr

theorem pairAt_subset (r t : Nat) : pairAt r t ⊆ triple t := by
  intro x hx
  unfold pairAt at hx
  split_ifs at hx <;> simp only [Finset.mem_insert,Finset.mem_singleton,triple] at * <;> aesop

theorem pairAt_card (r t : Nat) : (pairAt r t).card=2 := by
  have h1 : 2*t≠2*t+1 := by omega
  have h2 : 2*t≠2*t+2 := by omega
  have h3 : 2*t+1≠2*t+2 := by omega
  unfold pairAt
  split_ifs <;> simp [h1,h2,h3]

theorem pairAt_not_root (r t : Nat) : r ∉ pairAt r t := by
  unfold pairAt
  split_ifs <;> simp only [Finset.mem_insert,Finset.mem_singleton,not_or] <;> omega

theorem pairAt_disjoint (r i j : Nat) (hij : i≠j) : Disjoint (pairAt r i) (pairAt r j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  unfold pairAt at hx hy
  split_ifs at hx hy <;> simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy <;> omega

theorem root_unique (e : Nat) (f : Nat → Finset Nat) (r s : Nat)
    (hr : r≤2*e) (hs : s≤2*e)
    (hunion : (Finset.range e).biUnion f=Finset.range (2*e+1) \ {r})
    (hf : ∀ t<e, f t=pairAt s t) : r=s := by
  by_contra hne
  have hm : s ∈ (Finset.range e).biUnion f := by
    rw [hunion]
    simp only [Finset.mem_sdiff,Finset.mem_range,Finset.mem_singleton]
    exact ⟨by omega,Ne.symm hne⟩
  obtain ⟨t,ht,hst⟩ := Finset.mem_biUnion.mp hm
  rw [hf t (Finset.mem_range.mp ht)] at hst
  exact pairAt_not_root s t hst

theorem pairAt_union (e r : Nat) (hr : r≤2*e) :
    (Finset.range e).biUnion (pairAt r) = Finset.range (2*e+1) \ {r} := by
  obtain ⟨s,hs,hf,hunion⟩ := root_exists e (pairAt r)
    (fun t _ => pairAt_subset r t) (fun t _ => pairAt_card r t)
    (fun i _ j _ hij => pairAt_disjoint r i j hij)
  have he : s=r := root_unique e (pairAt r) s r hs hr hunion (fun _ _ => rfl)
  simpa only [he] using hunion

theorem root_exists_unique (e : Nat) (f : Nat → Finset Nat)
    (hs : ∀ t<e, f t ⊆ triple t) (hc : ∀ t<e, (f t).card=2)
    (hd : ∀ i<e, ∀ j<e, i≠j → Disjoint (f i) (f j)) :
    ∃! r, r≤2*e ∧ ∀ t<e, f t=pairAt r t := by
  obtain ⟨r,hr,hf,hunion⟩ := root_exists e f hs hc hd
  refine ⟨r,⟨hr,hf⟩,?_⟩
  intro s hs
  exact (root_unique e f r s hr hs.1 hunion hs.2).symm

def Valid (e : Nat) (f : Fin e → Finset Nat) : Prop :=
  (∀ t, f t ⊆ triple t.val ∧ (f t).card=2) ∧
  ∀ i j, i≠j → Disjoint (f i) (f j)

def canonical (e : Nat) (r : Fin (2*e+1)) : {f : Fin e → Finset Nat // Valid e f} :=
  ⟨fun t => pairAt r.val t.val,
    (fun t => ⟨pairAt_subset _ _,pairAt_card _ _⟩),
    fun i j hij => pairAt_disjoint _ _ _ (fun he => hij (Fin.ext he))⟩

theorem canonical_injective (e : Nat) : Function.Injective (canonical e) := by
  intro r s he
  apply Fin.ext
  apply root_unique e (pairAt r.val) r.val s.val (by omega) (by omega) (pairAt_union e r.val (by omega))
  intro t ht
  exact congrFun (congrArg Subtype.val he) ⟨t,ht⟩

theorem canonical_surjective (e : Nat) : Function.Surjective (canonical e) := by
  classical
  intro f
  let g (t : Nat) := if ht : t<e then f.val ⟨t,ht⟩ else ∅
  have hg (t : Fin e) : g t.val=f.val t := by simp only [g,dif_pos t.isLt]
  obtain ⟨r,hr,hf,hunion⟩ := root_exists e g
    (fun t ht => by simpa only [g,dif_pos ht] using (f.property.1 ⟨t,ht⟩).1)
    (fun t ht => by simpa only [g,dif_pos ht] using (f.property.1 ⟨t,ht⟩).2)
    (fun i hi j hj hij => by
      simpa only [g,dif_pos hi,dif_pos hj] using f.property.2 ⟨i,hi⟩ ⟨j,hj⟩ (by simpa using hij))
  refine ⟨⟨r,by omega⟩,?_⟩
  apply Subtype.ext
  funext t
  exact (hf t.val t.isLt).symm.trans (hg t)

noncomputable def rootEquiv (e : Nat) : Fin (2*e+1) ≃ {f : Fin e → Finset Nat // Valid e f} :=
  Equiv.ofBijective (canonical e) ⟨canonical_injective e,canonical_surjective e⟩

theorem card_local_pairings (e : Nat) : Nat.card {f : Fin e → Finset Nat // Valid e f}=2*e+1 := by
  rw [← Nat.card_congr (rootEquiv e),Nat.card_fin]

theorem triple_separated (i j x y : Nat) (hx : x ∈ triple i) (hy : y ∈ triple i)
    (hx' : x ∈ triple j) (hy' : y ∈ triple j) (hne : x≠y) : i=j := by
  simp only [triple,Finset.mem_insert,Finset.mem_singleton] at hx hy hx' hy'
  omega

def Paired (p : Nat → Nat) (A : Finset Nat) : Prop :=
  ∀ x ∈ A, p x ∈ A ∧ p x ≠ x

theorem orbit_paired (p : Nat → Nat) (hp : Function.Involutive p) (a : Nat) (ha : p a≠a) :
    Paired p {a,p a} := by
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl|rfl
  · exact ⟨by simp,ha⟩
  · rw [hp a]
    exact ⟨by simp,Ne.symm ha⟩

theorem orbit_eq (p : Nat → Nat) (hp : Function.Involutive p) (a x : Nat)
    (hx : x ∈ ({a,p a} : Finset Nat)) : ({x,p x} : Finset Nat)={a,p a} := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl|rfl
  · rfl
  · rw [hp a,Finset.pair_comm]

theorem winning_root (e : Nat) (p : Nat → Nat) (hp : Function.Involutive p)
    (hw : ∀ t<e, ∃ x, x∈triple t ∧ p x∈triple t ∧ p x≠x) :
    ∃ r, r≤2*e ∧ ∀ t<e, Paired p (pairAt r t) := by
  classical
  have hw' (t : Fin e) : ∃ x, x∈triple t.val ∧ p x∈triple t.val ∧ p x≠x := hw t.val t.isLt
  choose a ha hpa hne using hw'
  let f (t : Nat) := if ht : t<e then ({a ⟨t,ht⟩,p (a ⟨t,ht⟩)} : Finset Nat) else ∅
  have hf (t : Fin e) : f t.val={a t,p (a t)} := by simp only [f,dif_pos t.isLt]
  have hs (t : Nat) (ht : t<e) : f t ⊆ triple t := by
    rw [hf ⟨t,ht⟩]
    exact Finset.insert_subset_iff.mpr ⟨ha _,Finset.singleton_subset_iff.mpr (hpa _)⟩
  have hc (t : Nat) (ht : t<e) : (f t).card=2 := by
    rw [hf ⟨t,ht⟩]
    simp [Ne.symm (hne ⟨t,ht⟩)]
  have hd (i : Nat) (hi : i<e) (j : Nat) (hj : j<e) (hij : i≠j) : Disjoint (f i) (f j) := by
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    rw [hf ⟨i,hi⟩] at hxi
    rw [hf ⟨j,hj⟩] at hxj
    have he := (orbit_eq p hp (a ⟨i,hi⟩) x hxi).symm.trans (orbit_eq p hp (a ⟨j,hj⟩) x hxj)
    have hsub : ({a ⟨i,hi⟩,p (a ⟨i,hi⟩)} : Finset Nat) ⊆ triple j := by
      rw [he]
      exact Finset.insert_subset_iff.mpr ⟨ha _,Finset.singleton_subset_iff.mpr (hpa _)⟩
    exact hij (triple_separated i j (a ⟨i,hi⟩) (p (a ⟨i,hi⟩)) (ha ⟨i,hi⟩) (hpa ⟨i,hi⟩)
      (hsub (by simp)) (hsub (by simp)) (Ne.symm (hne ⟨i,hi⟩)))
  obtain ⟨r,hr,hroot,hunion⟩ := root_exists e f hs hc hd
  refine ⟨r,hr,?_⟩
  intro t ht
  rw [← hroot t ht,hf ⟨t,ht⟩]
  exact orbit_paired p hp _ (hne _)

theorem nonroot_paired (e r : Nat) (hr : r≤2*e) (p : Nat → Nat)
    (hpaired : ∀ t<e, Paired p (pairAt r t))
    (x : Nat) (hx : x<2*e+1) (hxr : x≠r) :
    ∃ t<e, x∈pairAt r t ∧ p x∈pairAt r t ∧ p x≠x := by
  have hm : x∈(Finset.range e).biUnion (pairAt r) := by
    rw [pairAt_union e r hr]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hx,by simpa using hxr⟩
  obtain ⟨t,ht,hxt⟩ := Finset.mem_biUnion.mp hm
  exact ⟨t,Finset.mem_range.mp ht,hxt,hpaired t (Finset.mem_range.mp ht) x hxt⟩

end LoosePathRoot


namespace LoosePathStructure
open Finset

def leaf (e j : Nat) := if j = 0 then 0 else if j = e+1 then 2*e else 2*j-1
def pathTest (e : Nat) (z : Nat × Nat) : Finset Nat :=
  {z.1*(2*e+1)+2*z.2, z.1*(2*e+1)+2*z.2+1, z.1*(2*e+1)+2*z.2+2}
def switchTest (v e m : Nat) (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (z : Fin m × Bool) : Finset Nat :=
  {v*(2*e+1)+2*z.1.val, v*(2*e+1)+2*z.1.val+1,
    (wire z).1.val*(2*e+1)+leaf e (wire z).2.val}

lemma leaf_lt {e j : Nat} (h : j < e+2) : leaf e j < 2*e+1 := by
  unfold leaf
  split_ifs <;> omega

lemma leaf_inj {e : Nat} (he : 0 < e) :
    Function.Injective (fun j : Fin (e+2) => leaf e j.val) := by
  intro i j h
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  dsimp only [leaf] at h
  split_ifs at h <;> omega

lemma block_inj {q u u' a a' : Nat} (ha : a < q) (ha' : a' < q)
    (h : u*q+a = u'*q+a') : u = u' ∧ a = a' := by
  have hu : u = u' := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hh | hh
    · have : u+1 ≤ u' := hh
      nlinarith
    · have : u'+1 ≤ u := hh
      nlinarith
  subst u'
  exact ⟨rfl, by omega⟩

lemma port_lt {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (z : Fin m × Bool) :
    (wire z).1.val*(2*e+1)+leaf e (wire z).2.val < v*(2*e+1) := by
  have ha := leaf_lt (wire z).2.isLt
  have hb := (wire z).1.isLt
  nlinarith

lemma pathTest_card (e : Nat) (z : Nat × Nat) : (pathTest e z).card = 3 := by
  simp [pathTest, card_insert_of_notMem]

lemma pathTest_inj {v : Nat} (e : Nat) :
    Set.InjOn (pathTest e) (↑((range v ×ˢ range e)) : Set (Nat × Nat)) := by
  intro a ha b hb hab
  simp only [mem_coe, mem_product, mem_range] at ha hb
  have hmin : a.1*(2*e+1)+2*a.2 = b.1*(2*e+1)+2*b.2 := by
    have h1 : a.1*(2*e+1)+2*a.2 ∈ pathTest e b := by rw [← hab]; simp [pathTest]
    have h2 : b.1*(2*e+1)+2*b.2 ∈ pathTest e a := by rw [hab]; simp [pathTest]
    simp only [pathTest, mem_insert, mem_singleton] at h1 h2
    omega
  have hh := block_inj (q:=2*e+1) (by omega : 2*a.2 < 2*e+1)
    (by omega : 2*b.2 < 2*e+1) hmin
  exact Prod.ext hh.1 (by omega)

lemma switchTest_card {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (z : Fin m × Bool) : (switchTest v e m wire z).card = 3 := by
  have hp := port_lt wire z
  unfold switchTest
  rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · simp only [mem_singleton]; omega
  · simp only [mem_insert, mem_singleton]; omega

lemma switchTest_inj {v e m : Nat} (he : 0 < e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) :
    Function.Injective (switchTest v e m wire) := by
  intro a b hab
  have ha := port_lt wire a
  have hb := port_lt wire b
  have hport : (wire a).1.val*(2*e+1)+leaf e (wire a).2.val =
      (wire b).1.val*(2*e+1)+leaf e (wire b).2.val := by
    have hh : (wire a).1.val*(2*e+1)+leaf e (wire a).2.val ∈ switchTest v e m wire b := by
      rw [← hab]; simp [switchTest]
    simp only [switchTest, mem_insert, mem_singleton] at hh
    omega
  have hh := block_inj (leaf_lt (wire a).2.isLt) (leaf_lt (wire b).2.isLt) hport
  apply wire.injective
  exact Prod.ext (Fin.ext hh.1) (leaf_inj he hh.2)

lemma path_mem_lt {v e : Nat} {z : Nat × Nat} (hz : z ∈ (range v ×ˢ range e))
    {x : Nat} (hx : x ∈ pathTest e z) : x < v*(2*e+1) := by
  simp only [mem_product, mem_range] at hz
  simp only [pathTest, mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> nlinarith [hz.1, hz.2]

theorem basic {v e m : Nat} (he : 0 < e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) :
    let A := ((range v ×ˢ range e)).image (pathTest e)
    let B := univ.image (switchTest v e m wire)
    (A ∪ B).card = v*e+2*m ∧ ∀ R ∈ A ∪ B, R.card = 3 := by
  dsimp
  have hd : Disjoint (((range v ×ˢ range e)).image (pathTest e))
      (univ.image (switchTest v e m wire)) := by
    rw [disjoint_left]
    intro R ha hb
    obtain ⟨a, hidx, rfl⟩ := mem_image.mp ha
    obtain ⟨b, _, h⟩ := mem_image.mp hb
    have hmem : v*(2*e+1)+2*b.1.val ∈ pathTest e a := by rw [← h]; simp [switchTest]
    have := path_mem_lt hidx hmem
    omega
  constructor
  · rw [card_union_of_disjoint hd, card_image_of_injOn (pathTest_inj e),
      card_image_of_injective _ (switchTest_inj he wire), card_product,
      card_range, card_range, card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool]
    omega
  · intro R hR
    rcases mem_union.mp hR with hR | hR
    · obtain ⟨a, _, rfl⟩ := mem_image.mp hR
      exact pathTest_card e a
    · obtain ⟨a, _, rfl⟩ := mem_image.mp hR
      exact switchTest_card wire a

lemma local_degree (e x : Nat) (he : 0 < e) (hx : x ≤ 2*e) :
    (∑ t ∈ range e, if x ∈ ({2*t,2*t+1,2*t+2} : Finset Nat) then 1 else 0) +
      (if x = 0 ∨ x = 2*e ∨ x % 2 = 1 then 1 else 0) = 2 := by
  induction e with
  | zero => omega
  | succ e ih =>
    by_cases he0 : e = 0
    · subst e
      have : x ≤ 2 := by omega
      interval_cases x <;> decide
    · have he : 0 < e := by omega
      rw [sum_range_succ]
      simp only [mem_insert, mem_singleton]
      by_cases hsmall : x ≤ 2*e
      · have hi := ih he hsmall
        simp only [mem_insert, mem_singleton] at hi
        have hp : ((if x = 2*e ∨ x = 2*e+1 ∨ x = 2*e+2 then 1 else 0) +
            (if x = 0 ∨ x = 2*(e+1) ∨ x%2 = 1 then 1 else 0) : Nat) =
            (if x = 0 ∨ x = 2*e ∨ x%2 = 1 then 1 else 0) := by
          split_ifs <;> omega
        rw [Nat.add_assoc, hp]
        exact hi
      · have hz : ∑ t ∈ range e, (if x ∈ ({2*t,2*t+1,2*t+2} : Finset Nat) then 1 else 0) = 0 := by
          apply sum_eq_zero
          intro t ht
          have ht' : t < e := mem_range.mp ht
          simp only [mem_insert, mem_singleton]
          rw [if_neg (by omega)]
        simp only [mem_insert, mem_singleton] at hz
        rw [hz]
        split_ifs <;> omega

lemma path_mem_iff {e a u x t : Nat} (hx : x < 2*e+1) (ht : t < e) :
    a*(2*e+1)+x ∈ pathTest e (u,t) ↔ u = a ∧ x ∈ ({2*t,2*t+1,2*t+2} : Finset Nat) := by
  simp only [pathTest, mem_insert, mem_singleton]
  constructor
  · intro h
    rcases h with h | h | h
    · have hh := block_inj hx (by omega : 2*t < 2*e+1) h
      exact ⟨hh.1.symm, Or.inl hh.2⟩
    · have hh := block_inj hx (by omega : 2*t+1 < 2*e+1) (by omega : a*(2*e+1)+x = u*(2*e+1)+(2*t+1))
      exact ⟨hh.1.symm, Or.inr (Or.inl hh.2)⟩
    · have hh := block_inj hx (by omega : 2*t+2 < 2*e+1) (by omega : a*(2*e+1)+x = u*(2*e+1)+(2*t+2))
      exact ⟨hh.1.symm, Or.inr (Or.inr hh.2)⟩
  · rintro ⟨rfl, h⟩
    rcases h with rfl | rfl | rfl <;> omega

lemma path_count {v e a x : Nat} (ha : a < v) (hx : x < 2*e+1) :
    ((((range v ×ˢ range e).image (pathTest e)).filter
      (fun R => a*(2*e+1)+x ∈ R)).card) =
      ∑ t ∈ range e, if x ∈ ({2*t,2*t+1,2*t+2} : Finset Nat) then 1 else 0 := by
  rw [card_eq_sum_ones, sum_filter, sum_image (pathTest_inj e), sum_product]
  have hi : ∀ u ∈ range v, ∀ t ∈ range e,
      (if a*(2*e+1)+x ∈ pathTest e (u,t) then 1 else 0) =
      if u = a then (if x ∈ ({2*t,2*t+1,2*t+2} : Finset Nat) then 1 else 0) else 0 := by
    intro u hu t ht
    simp only [path_mem_iff hx (mem_range.mp ht)]
    split_ifs <;> simp_all
  trans ∑ u ∈ range v, ∑ t ∈ range e,
      if u = a then (if x ∈ ({2*t,2*t+1,2*t+2} : Finset Nat) then 1 else 0) else 0
  · apply sum_congr rfl
    intro u hu
    exact sum_congr rfl (hi u hu)
  · simp only [sum_ite_irrel, sum_const_zero]
    simp [ha]

lemma leaf_exists {e x : Nat} (he : 0 < e) (hx : x < 2*e+1) :
    (∃ j : Fin (e+2), leaf e j.val = x) ↔ x = 0 ∨ x = 2*e ∨ x%2 = 1 := by
  constructor
  · rintro ⟨j,hj⟩
    have ht := j.isLt
    dsimp only [leaf] at hj
    split_ifs at hj <;> omega
  · rintro (h | h | h)
    · exact ⟨⟨0,by omega⟩, by simp [leaf,h]⟩
    · exact ⟨⟨e+1,by omega⟩, by simp [leaf,h]⟩
    · refine ⟨⟨(x+1)/2,by omega⟩, ?_⟩
      dsimp only [leaf]
      split_ifs <;> omega

lemma port_inj {v e m : Nat} (he : 0 < e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) :
    Function.Injective (fun z => (wire z).1.val*(2*e+1)+leaf e (wire z).2.val) := by
  intro a b h
  have hh := block_inj (leaf_lt (wire a).2.isLt) (leaf_lt (wire b).2.isLt) h
  apply wire.injective
  exact Prod.ext (Fin.ext hh.1) (leaf_inj he hh.2)

lemma switch_low {v e m x : Nat}
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (hx : x < v*(2*e+1)) (z : Fin m × Bool) :
    x ∈ switchTest v e m wire z ↔ x = (wire z).1.val*(2*e+1)+leaf e (wire z).2.val := by
  simp only [switchTest, mem_insert, mem_singleton]
  omega

lemma switch_count_low {v e m a x : Nat} (he : 0 < e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) (ha : a < v) (hx : x < 2*e+1) :
    ((univ.image (switchTest v e m wire)).filter (fun R => a*(2*e+1)+x ∈ R)).card =
      if x = 0 ∨ x = 2*e ∨ x%2 = 1 then 1 else 0 := by
  have hlow : a*(2*e+1)+x < v*(2*e+1) := by nlinarith
  by_cases hl : x = 0 ∨ x = 2*e ∨ x%2 = 1
  · rw [if_pos hl]
    obtain ⟨j,hj⟩ := (leaf_exists he hx).mpr hl
    let z := wire.symm (⟨a,ha⟩,j)
    have hz : wire z = (⟨a,ha⟩,j) := wire.apply_symm_apply _
    have hf : ((univ.image (switchTest v e m wire)).filter
        (fun R => a*(2*e+1)+x ∈ R)) = {switchTest v e m wire z} := by
      ext R
      simp only [mem_filter, mem_image, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨⟨w,rfl⟩,hw⟩
        have hp := (switch_low wire hlow w).mp hw
        have hwz : w = z := port_inj he wire (by dsimp only; rw [hz]; dsimp; omega)
        rw [hwz]
      · rintro rfl
        refine ⟨⟨z,rfl⟩, (switch_low wire hlow z).mpr ?_⟩
        rw [hz]
        dsimp
        omega
    rw [hf, card_singleton]
  · rw [if_neg hl]
    rw [card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro R hR
    obtain ⟨hR,hmem⟩ := mem_filter.mp hR
    obtain ⟨z,_,rfl⟩ := mem_image.mp hR
    have hp := (switch_low wire hlow z).mp hmem
    have hh := block_inj hx (leaf_lt (wire z).2.isLt) hp
    exact hl ((leaf_exists he hx).mp ⟨(wire z).2,hh.2.symm⟩)

lemma switch_count_high {v e m : Nat} (he : 0 < e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) (j : Fin m) (r : Nat) (hr : r < 2) :
    ((univ.image (switchTest v e m wire)).filter
      (fun R => v*(2*e+1)+2*j.val+r ∈ R)).card = 2 := by
  have hmem (z : Fin m × Bool) : v*(2*e+1)+2*j.val+r ∈ switchTest v e m wire z ↔ z.1 = j := by
    have hp := port_lt wire z
    simp only [switchTest, mem_insert, mem_singleton]
    constructor
    · intro h
      apply Fin.ext
      omega
    · intro h
      have hh := congrArg Fin.val h
      omega
  have hf : ((univ.image (switchTest v e m wire)).filter
      (fun R => v*(2*e+1)+2*j.val+r ∈ R)) =
      {switchTest v e m wire (j,false),switchTest v e m wire (j,true)} := by
    ext R
    simp only [mem_filter, mem_image, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨⟨z,b⟩,rfl⟩,hz⟩
      have hzj := (hmem (z,b)).mp hz
      dsimp at hzj
      subst z
      cases b <;> simp
    · rintro (rfl | rfl)
      · exact ⟨⟨(j,false),rfl⟩,(hmem _).mpr rfl⟩
      · exact ⟨⟨(j,true),rfl⟩,(hmem _).mpr rfl⟩
  rw [hf, card_pair]
  intro h
  have hh := switchTest_inj he wire h
  have := congrArg Prod.snd hh
  simp at this

 theorem degree {v e m : Nat} (he : 0 < e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) (i : Fin (v*(2*e+1)+2*m)) :
    ((((range v ×ˢ range e).image (pathTest e)) ∪
      (univ.image (switchTest v e m wire))).filter (fun R => i.val ∈ R)).card = 2 := by
  let A := (range v ×ˢ range e).image (pathTest e)
  let B := univ.image (switchTest v e m wire)
  have hd : Disjoint A B := by
    rw [disjoint_left]
    intro R hA hB
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hA
    obtain ⟨b,_,h⟩ := mem_image.mp hB
    have hh : v*(2*e+1)+2*b.1.val ∈ pathTest e a := by rw [←h]; simp [switchTest]
    have ht := path_mem_lt ha hh
    omega
  change ((A ∪ B).filter _).card = 2
  rw [filter_union, card_union_of_disjoint (hd.mono (filter_subset _ _) (filter_subset _ _))]
  by_cases hlow : i.val < v*(2*e+1)
  · let a := i.val/(2*e+1)
    let x := i.val %(2*e+1)
    have hq : 0 < 2*e+1 := by omega
    have ha : a < v := (Nat.div_lt_iff_lt_mul hq).mpr hlow
    have hx : x < 2*e+1 := Nat.mod_lt _ hq
    have hix : i.val = a*(2*e+1)+x := by dsimp [a,x]; simpa [Nat.mul_comm] using (Nat.div_add_mod i.val (2*e+1)).symm
    dsimp only [A,B]
    rw [hix,path_count ha hx,switch_count_low he wire ha hx]
    exact local_degree e x he (by omega)
  · have hz : (A.filter (fun R => i.val ∈ R)).card = 0 := by
      rw [card_eq_zero]
      apply eq_empty_iff_forall_notMem.mpr
      intro R hR
      obtain ⟨hR,hmem⟩ := mem_filter.mp hR
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hR
      exact hlow (path_mem_lt ha hmem)
    rw [hz, Nat.zero_add]
    let d := i.val-v*(2*e+1)
    have hd' : d < 2*m := by have := i.isLt; dsimp [d]; omega
    let j : Fin m := ⟨d/2,by omega⟩
    have hix : i.val = v*(2*e+1)+2*j.val+d%2 := by dsimp [j,d]; omega
    dsimp only [B]
    rw [hix]
    exact switch_count_high he wire j (d%2) (by omega)

end LoosePathStructure


namespace LoosePathConstruction
open Finset

def rootNode {v e : Nat} (r : Fin v → Fin (2*e+1)) (i : Fin v) : Nat :=
  i.val*(2*e+1)+(r i).val

def twin (v e : Nat) {m : Nat} (z : Fin m × Bool) : Nat :=
  v*(2*e+1)+2*z.1.val+z.2.toNat

def port {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (z : Fin m × Bool) : Nat :=
  (wire z).1.val*(2*e+1)+LoosePathStructure.leaf e (wire z).2.val

def pathPair {v e : Nat} (r : Fin v → Fin (2*e+1)) (it : Fin v × Fin e) : Finset Nat :=
  (LoosePathRoot.pairAt (r it.1).val it.2.val).image (fun x => it.1.val*(2*e+1)+x)

theorem local_bound {e r t x : Nat} (ht : t<e) (hx : x∈LoosePathRoot.pairAt r t) : x<2*e+1 := by
  have hh := LoosePathRoot.pairAt_subset r t hx
  simp only [LoosePathRoot.triple,Finset.mem_insert,Finset.mem_singleton] at hh
  omega

theorem pathPair_card {v e : Nat} (r : Fin v → Fin (2*e+1)) (it : Fin v × Fin e) :
    (pathPair r it).card=2 := by
  rw [pathPair,Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)]
  exact LoosePathRoot.pairAt_card _ _

theorem pathPair_low {v e : Nat} (r : Fin v → Fin (2*e+1)) (it : Fin v × Fin e)
    {x : Nat} (hx : x∈pathPair r it) : x<v*(2*e+1) := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have hyb := local_bound it.2.isLt hy
  have hib := it.1.isLt
  nlinarith

theorem rootNode_low {v e : Nat} (r : Fin v → Fin (2*e+1)) (i : Fin v) :
    rootNode r i<v*(2*e+1) := by
  have hi := i.isLt
  have hr := (r i).isLt
  dsimp [rootNode]
  nlinarith

theorem root_not_pathPair {v e : Nat} (r : Fin v → Fin (2*e+1)) (i : Fin v)
    (it : Fin v × Fin e) : rootNode r i∉pathPair r it := by
  intro hh
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hh
  have hxb := local_bound it.2.isLt hx
  have hb := LoosePathStructure.block_inj hxb (r i).isLt he
  have hi : it.1=i := Fin.ext hb.1
  rw [hi,hb.2] at hx
  exact LoosePathRoot.pairAt_not_root _ _ hx

theorem pathPair_disjoint {v e : Nat} (r : Fin v → Fin (2*e+1))
    (a b : Fin v × Fin e) (hab : a≠b) : Disjoint (pathPair r a) (pathPair r b) := by
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hxa
  obtain ⟨z,hz,hf⟩ := Finset.mem_image.mp hxb
  have hb := LoosePathStructure.block_inj (local_bound a.2.isLt hy) (local_bound b.2.isLt hz)
    (he.trans hf.symm)
  have hi : a.1=b.1 := Fin.ext hb.1
  have ht : a.2.val≠b.2.val := by
    intro ht
    exact hab (Prod.ext hi (Fin.ext ht))
  rw [hi,hb.2] at hy
  exact Finset.disjoint_left.mp (LoosePathRoot.pairAt_disjoint _ _ _ ht) hy hz

theorem twin_high (v e : Nat) {m : Nat} (z : Fin m × Bool) : v*(2*e+1) ≤ twin v e z := by
  simp only [twin]
  omega

theorem twin_bound (v e : Nat) {m : Nat} (z : Fin m × Bool) :
    twin v e z<v*(2*e+1)+2*m := by
  have hz := z.1.isLt
  rcases z with ⟨j,b⟩
  have hj := j.isLt
  cases b <;> simp [twin] <;> omega

theorem twin_injective (v e m : Nat) : Function.Injective (twin v e (m:=m)) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ he
  cases a <;> cases b <;> simp [twin] at he
  all_goals first | (exfalso; omega) | (apply Prod.ext; exact Fin.ext (by omega); rfl)

theorem port_low {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (z : Fin m × Bool) : port wire z<v*(2*e+1) := LoosePathStructure.port_lt wire z

theorem port_injective {v e m : Nat} (he : 0<e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) : Function.Injective (port wire) := by
  intro x y hh
  have hb := LoosePathStructure.block_inj
    (LoosePathStructure.leaf_lt (wire x).2.isLt) (LoosePathStructure.leaf_lt (wire y).2.isLt) hh
  apply wire.injective
  exact Prod.ext (Fin.ext hb.1) (LoosePathStructure.leaf_inj he hb.2)

def inactivePair (v e : Nat) {m : Nat} (j : Fin m) : Finset Nat :=
  {twin v e (j,false),twin v e (j,true)}

def activePort {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (o : S → Bool) (z : S × Bool) : Nat :=
  port wire (z.1.val,Bool.xor z.2 (o z.1))

def activePair {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (o : S → Bool) (z : S × Bool) : Finset Nat :=
  {twin v e (z.1.val,z.2),activePort wire S o z}

theorem inactivePair_card (v e : Nat) {m : Nat} (j : Fin m) : (inactivePair v e j).card=2 := by
  have hne : twin v e (j,false)≠twin v e (j,true) := by
    intro hh
    have ht := twin_injective v e m hh
    exact Bool.false_ne_true (congrArg Prod.snd ht)
  simp [inactivePair,hne]

theorem activePair_card {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (o : S → Bool) (z : S × Bool) : (activePair wire S o z).card=2 := by
  have hlo := port_low wire (z.1.val,Bool.xor z.2 (o z.1))
  have hhi := twin_high v e (z.1.val,z.2)
  have hne : twin v e (z.1.val,z.2)≠activePort wire S o z := by
    unfold activePort
    omega
  simp [activePair,hne]

theorem activePort_injective {v e m : Nat} (he : 0<e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (o : S → Bool) : Function.Injective (activePort wire S o) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ hh
  have hp := port_injective he wire hh
  have hij : i=j := Subtype.ext (congrArg Prod.fst hp)
  subst j
  apply Prod.ext
  · rfl
  · have hb := congrArg (fun z : Fin m × Bool => z.2) hp
    cases a <;> cases b <;> cases ho : o i <;> simp_all

theorem inactivePair_disjoint (v e : Nat) {m : Nat} (i j : Fin m) (hij : i≠j) :
    Disjoint (inactivePair v e i) (inactivePair v e j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [inactivePair,Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl|rfl <;> rcases hy with h|h
  all_goals exact hij (congrArg Prod.fst (twin_injective v e m h))

theorem activePair_disjoint {v e m : Nat} (he : 0<e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (o : S → Bool) (a b : S × Bool) (hab : a≠b) :
    Disjoint (activePair wire S o a) (activePair wire S o b) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [activePair,Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with hx|hx <;> rcases hy with hy|hy
  · have hh := twin_injective v e m (hx.symm.trans hy)
    exact hab (Prod.ext (Subtype.ext (congrArg (fun z : Fin m × Bool => z.1) hh))
      (congrArg (fun z : Fin m × Bool => z.2) hh))
  · have hhi := twin_high v e (a.1.val,a.2)
    have hlo := port_low wire (b.1.val,Bool.xor b.2 (o b.1))
    change x=port wire (b.1.val,Bool.xor b.2 (o b.1)) at hy
    omega
  · have hhi := twin_high v e (b.1.val,b.2)
    have hlo := port_low wire (a.1.val,Bool.xor a.2 (o a.1))
    change x=port wire (a.1.val,Bool.xor a.2 (o a.1)) at hx
    omega
  · exact hab (activePort_injective he wire S o (hx.symm.trans hy))

def Pinned {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (r : Fin v → Fin (2*e+1)) : Prop :=
  ∀ z : Fin m × Bool, z.1∈S → rootNode r (wire z).1=port wire z

theorem path_inactive_disjoint {v e m : Nat} (r : Fin v → Fin (2*e+1))
    (it : Fin v × Fin e) (j : Fin m) : Disjoint (pathPair r it) (inactivePair v e j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hlo := pathPair_low r it hx
  simp only [inactivePair,Finset.mem_insert,Finset.mem_singleton] at hy
  rcases hy with rfl|rfl
  · have := twin_high v e (j,false); omega
  · have := twin_high v e (j,true); omega

theorem path_active_disjoint {v e m : Nat}
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (r : Fin v → Fin (2*e+1)) (o : S → Bool) (hpin : Pinned wire S r)
    (it : Fin v × Fin e) (z : S × Bool) :
    Disjoint (pathPair r it) (activePair wire S o z) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [activePair,Finset.mem_insert,Finset.mem_singleton] at hy
  rcases hy with rfl|rfl
  · have hlo := pathPair_low r it hx
    have := twin_high v e (z.1.val,z.2)
    omega
  · have hp := hpin (z.1.val,Bool.xor z.2 (o z.1)) z.1.property
    change port wire (z.1.val,Bool.xor z.2 (o z.1)) ∈ pathPair r it at hx
    rw [← hp] at hx
    exact root_not_pathPair r _ it hx

theorem inactive_active_disjoint {v e m : Nat}
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (o : S → Bool) (j : Fin m) (hj : j∉S) (z : S × Bool) :
    Disjoint (inactivePair v e j) (activePair wire S o z) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [inactivePair,activePair,Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hy with hy|hy
  · rcases hx with hx|hx
    all_goals
      have hh := twin_injective v e m (hx.symm.trans hy)
      have he : j=z.1.val := congrArg (fun z : Fin m × Bool => z.1) hh
      exact hj (he ▸ z.1.property)
  · have hlo := port_low wire (z.1.val,Bool.xor z.2 (o z.1))
    change x=port wire (z.1.val,Bool.xor z.2 (o z.1)) at hy
    rcases hx with hx|hx
    · have := twin_high v e (j,false); omega
    · have := twin_high v e (j,true); omega

def PairIndex (v e m : Nat) (S : Finset (Fin m)) :=
  (Fin v × Fin e) ⊕ ({j : Fin m // j∉S} ⊕ (S × Bool))

def fixedPair {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (r : Fin v → Fin (2*e+1)) (o : S → Bool) : PairIndex v e m S → Finset Nat :=
  Sum.elim (pathPair r) (Sum.elim (fun j => inactivePair v e j.val) (activePair wire S o))

theorem fixedPair_card {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (r : Fin v → Fin (2*e+1)) (o : S → Bool) (i : PairIndex v e m S) :
    (fixedPair wire S r o i).card=2 := by
  rcases i with i|i
  · exact pathPair_card r i
  · rcases i with i|i
    · exact inactivePair_card v e i.val
    · exact activePair_card wire S o i

theorem fixedPair_disjoint {v e m : Nat} (he : 0<e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (r : Fin v → Fin (2*e+1)) (o : S → Bool) (hpin : Pinned wire S r)
    (a b : PairIndex v e m S) (hab : a≠b) :
    Disjoint (fixedPair wire S r o a) (fixedPair wire S r o b) := by
  rcases a with a|a <;> rcases b with b|b
  · exact pathPair_disjoint r a b (fun h => hab (congrArg Sum.inl h))
  · rcases b with b|b
    · exact path_inactive_disjoint r a b.val
    · exact path_active_disjoint wire S r o hpin a b
  · rcases a with a|a
    · exact (path_inactive_disjoint r b a.val).symm
    · exact (path_active_disjoint wire S r o hpin b a).symm
  · rcases a with a|a <;> rcases b with b|b
    · exact inactivePair_disjoint v e a.val b.val
        (fun h => hab (congrArg (fun j => Sum.inr (Sum.inl j)) (Subtype.ext h)))
    · exact inactive_active_disjoint wire S o a.val a.property b
    · exact (inactive_active_disjoint wire S o b.val b.property a).symm
    · exact activePair_disjoint he wire S o a b
        (fun h => hab (congrArg (fun j => Sum.inr (Sum.inr j)) h))

theorem fixedPair_bound {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (r : Fin v → Fin (2*e+1)) (o : S → Bool)
    (i : PairIndex v e m S) {x : Nat} (hx : x∈fixedPair wire S r o i) :
    x<v*(2*e+1)+2*m := by
  rcases i with i|i
  · have := pathPair_low r i hx; omega
  · rcases i with i|i
    · change x∈inactivePair v e i.val at hx
      simp only [inactivePair,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl
      · exact twin_bound v e _
      · exact twin_bound v e _
    · change x∈activePair wire S o i at hx
      simp only [activePair,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl
      · exact twin_bound v e _
      · have := port_low wire (i.1.val,Bool.xor i.2 (o i.1)); exact lt_of_lt_of_le this (by omega)

noncomputable instance pairIndexFintype (v e m : Nat) (S : Finset (Fin m)) :
    Fintype (PairIndex v e m S) := by
  classical
  unfold PairIndex
  infer_instance

theorem pairIndex_card (v e m : Nat) (S : Finset (Fin m)) :
    Fintype.card (PairIndex v e m S)=v*e+m+S.card := by
  classical
  have hs : S.card≤m := by simpa using Finset.card_le_card (Finset.subset_univ S)
  change Fintype.card ((Fin v × Fin e) ⊕ ({j : Fin m // j∉S} ⊕ (S × Bool))) = _
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,
    Fintype.card_coe,Fintype.card_subtype_compl]
  omega

theorem free_count (v e m : Nat) (S : Finset (Fin m)) :
    v*(2*e+1)+2*m-2*Fintype.card (PairIndex v e m S)=v-2*S.card := by
  rw [pairIndex_card]
  have he : v*(2*e+1)+2*m=(2*(v*e+m))+v := by ring
  rw [he]
  omega

end LoosePathConstruction


namespace InvolutionGadget
open Finset

def Hits {α : Type*} [DecidableEq α] (P : α → α) (R : Finset α) : Prop :=
 ∃ z, z ∈ R ∧ P z ∈ R ∧ P z ≠ z

theorem active_end {α : Type*} [DecidableEq α] (P : α → α)
 (hP : Function.Involutive P) (u v x : α) (hn : P u ≠ v)
 (hh : Hits P {u,v,x}) : P x=u ∨ P x=v := by
 have hn' : P v ≠ u := by
  intro h
  have he := congrArg P h
  rw [hP] at he
  exact hn he.symm
 obtain ⟨z,hz,hpz,hne⟩ := hh
 simp only [mem_insert,mem_singleton] at hz hpz
 rcases hz with rfl|rfl|rfl
 · rcases hpz with h|h|h
   · exact (hne h).elim
   · exact (hn h).elim
   · left; rw [←h,hP]
 · rcases hpz with h|h|h
   · exact (hn' h).elim
   · exact (hne h).elim
   · right; rw [←h,hP]
 · rcases hpz with h|h|h
   · exact Or.inl h
   · exact Or.inr h
   · exact (hne h).elim

theorem wire_cases {α : Type*} [DecidableEq α] (P : α → α)
 (hP : Function.Involutive P) (u v x y : α) (hxy : x ≠ y)
 (hx : Hits P {u,v,x}) (hy : Hits P {u,v,y}) :
 P u=v ∨ (P u=x ∧ P v=y) ∨ (P u=y ∧ P v=x) := by
 by_cases hn : P u=v
 · exact Or.inl hn
 right
 have hx' := active_end P hP u v x hn hx
 have hy' := active_end P hP u v y hn hy
 have hne : P x ≠ P y := fun h => hxy (hP.injective h)
 rcases hx' with hx'|hx' <;> rcases hy' with hy'|hy'
 · exact (hne (hx'.trans hy'.symm)).elim
 · left; exact ⟨by rw [←hx',hP],by rw [←hy',hP]⟩
 · right; exact ⟨by rw [←hy',hP],by rw [←hx',hP]⟩
 · exact (hne (hx'.trans hy'.symm)).elim

end InvolutionGadget


namespace LoosePathNat

def natP {k : Nat} (P : Equiv.Perm (Fin k)) (x : Nat) : Nat :=
  if hx : x < k then (P ⟨x,hx⟩).val else x

theorem natP_apply {k : Nat} (P : Equiv.Perm (Fin k)) (x : Fin k) :
    natP P x.val = (P x).val := by
  simp [natP, x.isLt]

theorem natP_involutive {k : Nat} (P : Equiv.Perm (Fin k))
    (hP : Function.Involutive P) : Function.Involutive (natP P) := by
  intro x
  by_cases hx : x < k
  · let z : Fin k := ⟨x,hx⟩
    change natP P (natP P z.val) = z.val
    rw [natP_apply, natP_apply, hP]
  · simp [natP, hx]

def shift (p : Nat → Nat) (δ x : Nat) : Nat :=
  if δ ≤ p (δ+x) then p (δ+x)-δ else x

theorem shift_involutive (p : Nat → Nat) (hp : Function.Involutive p) (δ : Nat) :
    Function.Involutive (shift p δ) := by
  intro x
  by_cases hx : δ ≤ p (δ+x)
  · have hsub : δ+(p (δ+x)-δ) = p (δ+x) := by omega
    simp only [shift, if_pos hx]
    rw [hsub, hp]
    simp
  · simp [shift,hx]

theorem shift_of_pair (p : Nat → Nat) (δ x y : Nat) (h : p (δ+x) = δ+y) :
    shift p δ x = y := by
  simp [shift,h]

theorem pair_of_shift (p : Nat → Nat) (δ x y : Nat)
    (hne : y ≠ x) (h : shift p δ x = y) : p (δ+x) = δ+y := by
  unfold shift at h
  split_ifs at h with hx
  · omega
  · exact False.elim (hne h.symm)

theorem shift_fixed_of_left_outside (p : Nat → Nat) (δ x : Nat) (h : p (δ+x) < δ) :
    shift p δ x = x := by
  simp [shift,show ¬δ ≤ p (δ+x) by omega]

end LoosePathNat



namespace LoosePathRoot
open Finset

theorem paired_unique_in_triple (p : Nat → Nat) (t : Nat) (A B : Finset Nat)
    (hA : A ⊆ triple t) (hB : B ⊆ triple t) (hcA : A.card=2) (hcB : B.card=2)
    (hpA : Paired p A) (hpB : Paired p B) : A = B := by
  classical
  have hex : ∃ x, x∈A ∧ x∈B := by
    by_contra! hn
    have hd : Disjoint A B := disjoint_left.mpr (fun x ha hb => hn x ha hb)
    have hh : (A ∪ B).card ≤ (triple t).card := card_le_card (union_subset hA hB)
    rw [card_union_of_disjoint hd,hcA,hcB] at hh
    have htr : (triple t).card=3 := by simp [triple]
    omega
  obtain ⟨x,hxA,hxB⟩ := hex
  have ha := hpA x hxA
  have hb := hpB x hxB
  have hpa : ({x,p x} : Finset Nat) = A := by
    apply eq_of_subset_of_card_le
    · exact insert_subset_iff.mpr ⟨hxA,singleton_subset_iff.mpr ha.1⟩
    · rw [hcA,card_pair (Ne.symm ha.2)]
  have hpb : ({x,p x} : Finset Nat) = B := by
    apply eq_of_subset_of_card_le
    · exact insert_subset_iff.mpr ⟨hxB,singleton_subset_iff.mpr hb.1⟩
    · rw [hcB,card_pair (Ne.symm hb.2)]
  exact hpa.symm.trans hpb

theorem root_unique_of_paired (e r s : Nat) (hr : r≤2*e) (hs : s≤2*e)
    (p : Nat → Nat) (hpr : ∀ t<e, Paired p (pairAt r t))
    (hps : ∀ t<e, Paired p (pairAt s t)) : r=s := by
  apply root_unique e (pairAt r) r s hr hs
  · exact pairAt_union e r hr
  · intro t ht
    exact paired_unique_in_triple p t _ _ (pairAt_subset r t) (pairAt_subset s t)
      (pairAt_card r t) (pairAt_card s t) (hpr t ht) (hps t ht)

end LoosePathRoot


namespace LoosePathNat
open Finset LoosePathRoot

theorem winning_shifted_root (e δ : Nat) (p : Nat → Nat) (hp : Function.Involutive p)
    (hw : ∀ t<e, ∃ x, x∈(triple t).image (fun y => δ+y) ∧
      p x∈(triple t).image (fun y => δ+y) ∧ p x≠x) :
    ∃ r, r≤2*e ∧ ∀ t<e, Paired p ((pairAt r t).image (fun y => δ+y)) := by
  have hw' : ∀ t<e, ∃ x, x∈triple t ∧ shift p δ x∈triple t ∧ shift p δ x≠x := by
    intro t ht
    obtain ⟨z,hz,hpz,hne⟩ := hw t ht
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    obtain ⟨y,hy,hyz⟩ := mem_image.mp hpz
    have hs := shift_of_pair p δ x y hyz.symm
    exact ⟨x,hx,by rw [hs]; exact hy,by rw [hs]; omega⟩
  obtain ⟨r,hr,hpr⟩ := winning_root e (shift p δ) (shift_involutive p hp δ) hw'
  refine ⟨r,hr,?_⟩
  intro t ht z hz
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
  obtain ⟨hy,hne⟩ := hpr t ht x hx
  have hpair := pair_of_shift p δ x (shift p δ x) hne rfl
  exact ⟨mem_image.mpr ⟨shift p δ x,hy,hpair.symm⟩,by omega⟩

theorem outside_is_root (e δ r : Nat) (hr : r≤2*e) (p : Nat → Nat)
    (hpr : ∀ t<e, Paired p ((pairAt r t).image (fun y => δ+y)))
    (x : Nat) (hx : x<2*e+1)
    (hout : p (δ+x)<δ ∨ δ+(2*e+1)≤p (δ+x)) : x=r := by
  by_contra hne
  have hm : x∈(range e).biUnion (pairAt r) := by
    rw [pairAt_union e r hr]
    exact mem_sdiff.mpr ⟨mem_range.mpr hx,by simpa using hne⟩
  obtain ⟨t,ht,hxt⟩ := mem_biUnion.mp hm
  have ht' := mem_range.mp ht
  have hglob : δ+x∈(pairAt r t).image (fun y => δ+y) := mem_image.mpr ⟨x,hxt,rfl⟩
  obtain ⟨y,hy,hyz⟩ := mem_image.mp (hpr t ht' (δ+x) hglob).1
  have hyt := pairAt_subset r t hy
  simp only [triple,mem_insert,mem_singleton] at hyt
  omega

end LoosePathNat


namespace LoosePathExtraction
open Finset LoosePathConstruction LoosePathRoot LoosePathStructure LoosePathNat InvolutionGadget

theorem extract {v e m : Nat} (he : 0<e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) (S : Finset (Fin m))
    (p : Nat → Nat) (hp : Function.Involutive p)
    (hpath : ∀ i : Fin v, ∀ t : Fin e, Hits p (pathTest e (i.val,t.val)))
    (hswitch : ∀ z : Fin m × Bool, Hits p (switchTest v e m wire z))
    (hactive : ∀ j : Fin m, j∈S ↔ p (twin v e (j,false)) ≠ twin v e (j,true)) :
    ∃ r : Fin v → Fin (2*e+1), ∃ o : S → Bool,
      Pinned wire S r ∧ ∀ i : PairIndex v e m S, Paired p (fixedPair wire S r o i) := by
  classical
  have hroots (i : Fin v) : ∃ r : Fin (2*e+1),
      ∀ t : Fin e, Paired p ((pairAt r.val t.val).image (fun x => i.val*(2*e+1)+x)) := by
    have hw : ∀ t<e, ∃ x, x∈(triple t).image (fun y => i.val*(2*e+1)+y) ∧
        p x∈(triple t).image (fun y => i.val*(2*e+1)+y) ∧ p x≠x := by
      intro t ht
      have h := hpath i ⟨t,ht⟩
      simpa [Hits,pathTest,triple,Nat.add_assoc] using h
    obtain ⟨r,hr,hpr⟩ := winning_shifted_root e (i.val*(2*e+1)) p hp hw
    exact ⟨⟨r,by omega⟩,fun t => hpr t.val t.isLt⟩
  choose r hr using hroots
  have hsw (z : Fin m × Bool) : Hits p {twin v e (z.1,false),twin v e (z.1,true),port wire z} := by
    simpa [switchTest,twin,port] using hswitch z
  have hpin : Pinned wire S r := by
    intro z hz
    have hpz := active_end p hp (twin v e (z.1,false)) (twin v e (z.1,true))
      (port wire z) ((hactive z.1).mp hz) (hsw z)
    have hlim : (wire z).1.val*(2*e+1)+(2*e+1) ≤ v*(2*e+1) := by
      have := (wire z).1.isLt
      nlinarith
    have hrt : leaf e (wire z).2.val = (r (wire z).1).val := by
      apply outside_is_root e ((wire z).1.val*(2*e+1)) (r (wire z).1).val
        (by have := (r (wire z).1).isLt; omega) p
        (fun t ht => hr (wire z).1 ⟨t,ht⟩) _ (leaf_lt (wire z).2.isLt)
      right
      have h1 := twin_high v e (z.1,false)
      have h2 := twin_high v e (z.1,true)
      dsimp only [port] at hpz
      omega
    dsimp only [rootNode,port]
    rw [hrt]
  have horient (j : S) : ∃ o : Bool, ∀ b : Bool,
      p (twin v e (j.val,b)) = port wire (j.val,Bool.xor b o) := by
    have hxy : port wire (j.val,false) ≠ port wire (j.val,true) := by
      intro h
      have hh := LoosePathConstruction.port_injective he wire h
      have := congrArg Prod.snd hh
      simp at this
    have hc := wire_cases p hp (twin v e (j.val,false)) (twin v e (j.val,true))
      (port wire (j.val,false)) (port wire (j.val,true)) hxy (hsw (j.val,false)) (hsw (j.val,true))
    rcases hc with hc | hc | hc
    · exact False.elim (((hactive j.val).mp j.property) hc)
    · refine ⟨false,?_⟩
      intro b
      cases b
      · simpa using hc.1
      · simpa using hc.2
    · refine ⟨true,?_⟩
      intro b
      cases b
      · simpa using hc.1
      · simpa using hc.2
  choose o ho using horient
  refine ⟨r,o,hpin,?_⟩
  intro i
  rcases i with i | i
  · exact hr i.1 i.2
  · rcases i with j | z
    · have hpj : p (twin v e (j.val,false)) = twin v e (j.val,true) := by
        by_contra h
        exact j.property ((hactive j.val).mpr h)
      have hne : p (twin v e (j.val,false)) ≠ twin v e (j.val,false) := by
        rw [hpj]
        simp [twin]
      have hh := orbit_paired p hp (twin v e (j.val,false)) hne
      simpa [fixedPair,inactivePair,hpj] using hh
    · have hpz : p (twin v e (z.1.val,z.2)) = activePort wire S o z := ho z.1 z.2
      have hne : p (twin v e (z.1.val,z.2)) ≠ twin v e (z.1.val,z.2) := by
        rw [hpz]
        have hl := port_low wire (z.1.val,Bool.xor z.2 (o z.1))
        have hh := twin_high v e (z.1.val,z.2)
        dsimp only [activePort]
        omega
      have hh := orbit_paired p hp (twin v e (z.1.val,z.2)) hne
      simpa [fixedPair,activePair,hpz] using hh

theorem paired_shift_of_image (p : Nat → Nat) (δ : Nat) (A : Finset Nat)
    (h : Paired p (A.image (fun y => δ+y))) : Paired (shift p δ) A := by
  intro x hx
  have hh := h (δ+x) (mem_image.mpr ⟨x,hx,rfl⟩)
  obtain ⟨y,hy,hyx⟩ := mem_image.mp hh.1
  have hs := shift_of_pair p δ x y hyx.symm
  exact ⟨by rw [hs]; exact hy,by rw [hs]; have := hh.2; omega⟩

theorem parameters_unique {v e m : Nat} (he : 0<e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) (S : Finset (Fin m))
    (p : Nat → Nat) (r s : Fin v → Fin (2*e+1)) (o u : S → Bool)
    (hr : ∀ i : PairIndex v e m S, Paired p (fixedPair wire S r o i))
    (hs : ∀ i : PairIndex v e m S, Paired p (fixedPair wire S s u i)) : r=s ∧ o=u := by
  have hrs : r=s := by
    funext i
    apply Fin.ext
    apply root_unique_of_paired e (r i).val (s i).val
      (by have := (r i).isLt; omega) (by have := (s i).isLt; omega) (shift p (i.val*(2*e+1)))
    · intro t ht
      exact paired_shift_of_image p _ _ (hr (Sum.inl (i,⟨t,ht⟩)))
    · intro t ht
      exact paired_shift_of_image p _ _ (hs (Sum.inl (i,⟨t,ht⟩)))
  refine ⟨hrs,?_⟩
  funext j
  have hro := hr (Sum.inr (Sum.inr (j,false)))
  have hsu := hs (Sum.inr (Sum.inr (j,false)))
  have get (o : S → Bool) (hh : Paired p (activePair wire S o (j,false))) :
      p (twin v e (j.val,false)) = port wire (j.val,o j) := by
    have ha := hh (twin v e (j.val,false)) (by simp [activePair])
    simp only [activePair,mem_insert,mem_singleton] at ha
    rcases ha.1 with h | h
    · exact (ha.2 h).elim
    · simpa [activePort] using h
  have hpo := get o hro
  have hpu := get u hsu
  have hz := LoosePathConstruction.port_injective he wire (hpo.symm.trans hpu)
  exact congrArg Prod.snd hz

end LoosePathExtraction



namespace LoosePathParameters
open Finset

noncomputable def fixedFunctionEquiv {X Y : Type*} [DecidableEq X]
    (C : Finset X) (g : X → Y) :
    {r : X → Y // ∀ i ∈ C, r i = g i} ≃ ({i : X // i ∉ C} → Y) := by
  classical
  exact {
    toFun := fun r i => r.val i.val
    invFun := fun f => ⟨fun i => if hi : i ∈ C then g i else f ⟨i,hi⟩,
      by intro i hi; simp [hi]⟩
    left_inv := by
      intro r
      apply Subtype.ext
      funext i
      by_cases hi : i ∈ C
      · simp only [dif_pos hi]
        exact (r.property i hi).symm
      · simp [hi]
    right_inv := by
      intro f
      funext i
      simp [i.property]
  }

theorem card_fixedFunctions {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    (C : Finset X) (g : X → Y) :
    Nat.card {r : X → Y // ∀ i ∈ C, r i = g i} =
      Nat.card Y ^ (Fintype.card X - C.card) := by
  classical
  rw [Nat.card_congr (fixedFunctionEquiv C g)]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_subtype_compl,
    Fintype.card_coe, Nat.card_eq_fintype_card]

theorem endpoint_inj {v m : Nat} (S : Finset (Fin m)) (wire : Fin m × Bool → Fin v)
    (hcard : ((S ×ˢ (univ : Finset Bool)).image wire).card = 2*S.card) :
    Set.InjOn wire (↑(S ×ˢ (univ : Finset Bool)) : Set (Fin m × Bool)) := by
  apply (card_image_iff).mp
  rw [card_product, card_univ, Fintype.card_bool]
  omega

theorem endpoint_card {v m : Nat} (S : Finset (Fin m)) (wire : Fin m × Bool → Fin v)
    (h : Set.InjOn wire (↑(S ×ˢ (univ : Finset Bool)) : Set (Fin m × Bool))) :
    ((S ×ˢ (univ : Finset Bool)).image wire).card = 2*S.card := by
  rw [card_image_of_injOn h, card_product, card_univ, Fintype.card_bool]
  omega

theorem fixedRootChoices {v q : Nat} (C : Finset (Fin v)) (g : Fin v → Fin q) :
    Nat.card {r : Fin v → Fin q // ∀ i ∈ C, r i = g i} = q^(v-C.card) := by
  simpa using card_fixedFunctions C g

theorem card_constrainedFunctions {A X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq A] [DecidableEq X] (T : Finset A) (f : A → X) (h : A → Y)
    (hf : Set.InjOn f (↑T : Set A)) (y0 : Y) :
    Nat.card {r : X → Y // ∀ a ∈ T, r (f a) = h a} =
      Nat.card Y ^ (Fintype.card X - T.card) := by
  classical
  let f' : T → X := fun a => f a.val
  have hf' : Function.Injective f' := by
    intro a b hab
    exact Subtype.ext (hf a.property b.property hab)
  let h' : T → Y := fun a => h a.val
  let g : X → Y := Function.extend f' h' (fun _ => y0)
  have hg (a : A) (ha : a ∈ T) : g (f a) = h a := hf'.extend_apply h' _ ⟨a,ha⟩
  have heq (r : X → Y) : (∀ a ∈ T, r (f a) = h a) ↔
      (∀ x ∈ T.image f, r x = g x) := by
    constructor
    · intro hr x hx
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      rw [hr a ha,hg a ha]
    · intro hr a ha
      rw [hr (f a) (mem_image.mpr ⟨a,ha,rfl⟩),hg a ha]
  rw [Nat.card_congr (Equiv.subtypeEquivRight heq),card_fixedFunctions,
    card_image_of_injOn hf]

theorem card_activeParameters {v m q : Nat} (hq : 0 < q) (S : Finset (Fin m))
    (endpt : Fin m × Bool → Fin v) (port : Fin m × Bool → Fin q)
    (hc : ((S ×ˢ (univ : Finset Bool)).image endpt).card = 2*S.card) :
    Nat.card ((S → Bool) × {r : Fin v → Fin q //
      ∀ z ∈ S ×ˢ (univ : Finset Bool), r (endpt z) = port z}) =
      2^S.card * q^(v-2*S.card) := by
  classical
  rw [Nat.card_prod]
  have hh := card_constrainedFunctions (S ×ˢ (univ : Finset Bool)) endpt port
    (endpoint_inj S endpt hc) (⟨0,hq⟩ : Fin q)
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, card_product,
    card_univ, Fintype.card_bool] at hh
  simp only [Nat.card_eq_fintype_card]
  rw [hh]
  simp [Nat.card_eq_fintype_card, Fintype.card_fun, Nat.mul_comm]

theorem endpoint_inj_of_roots {A X Y : Type*} [DecidableEq A]
    (T : Finset A) (endpt : A → X) (port : A → Y)
    (hp : Function.Injective (fun a => (endpt a, port a)))
    (r : X → Y) (hr : ∀ a ∈ T, r (endpt a) = port a) :
    Set.InjOn endpt (↑T : Set A) := by
  intro a ha b hb hab
  apply hp
  refine Prod.ext hab ?_
  dsimp only
  rw [← hr a ha, ← hr b hb, hab]

theorem endpoint_card_of_roots {v m q : Nat} (S : Finset (Fin m))
    (endpt : Fin m × Bool → Fin v) (port : Fin m × Bool → Fin q)
    (hp : Function.Injective (fun a => (endpt a, port a)))
    (r : Fin v → Fin q) (hr : ∀ a ∈ S ×ˢ (univ : Finset Bool), r (endpt a) = port a) :
    ((S ×ˢ (univ : Finset Bool)).image endpt).card = 2*S.card :=
  endpoint_card S endpt (endpoint_inj_of_roots _ endpt port hp r hr)

end LoosePathParameters



namespace LoosePathSoundness
open Finset LoosePathConstruction

def Hits (p : Nat → Nat) (A : Finset Nat) : Prop := ∃ x, x∈A ∧ p x∈A ∧ p x≠x

theorem hits_of_paired (p : Nat → Nat) (A B : Finset Nat)
    (hc : A.card=2) (hp : LoosePathRoot.Paired p A) (hs : A⊆B) : Hits p B := by
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x,hx⟩ := hne
  exact ⟨x,hs hx,hs (hp x hx).1,(hp x hx).2⟩

theorem pathPair_subset {v e : Nat} (r : Fin v → Fin (2*e+1)) (it : Fin v × Fin e) :
    pathPair r it ⊆ LoosePathStructure.pathTest e (it.1.val,it.2.val) := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have hh := LoosePathRoot.pairAt_subset _ _ hy
  simp only [LoosePathRoot.triple,Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hh with rfl|rfl|rfl <;> simp [LoosePathStructure.pathTest,Nat.add_assoc]

theorem paired_apply (p : Nat → Nat) (a b : Nat)
    (hp : LoosePathRoot.Paired p {a,b}) : p a=b := by
  have hh := hp a (by simp)
  simp only [Finset.mem_insert,Finset.mem_singleton] at hh
  exact hh.1.resolve_left hh.2

theorem active_apply {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (r : Fin v → Fin (2*e+1)) (o : S → Bool) (p : Nat → Nat)
    (hp : ∀ i, LoosePathRoot.Paired p (fixedPair wire S r o i))
    (j : Fin m) (hj : j∈S) (b : Bool) :
    p (twin v e (j,b))=port wire (j,Bool.xor b (o ⟨j,hj⟩)) := by
  exact paired_apply p _ _ (hp (Sum.inr (Sum.inr (⟨j,hj⟩,b))))

theorem inactive_apply {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (r : Fin v → Fin (2*e+1)) (o : S → Bool) (p : Nat → Nat)
    (hp : ∀ i, LoosePathRoot.Paired p (fixedPair wire S r o i))
    (j : Fin m) (hj : j∉S) : p (twin v e (j,false))=twin v e (j,true) := by
  exact paired_apply p _ _ (hp (Sum.inr (Sum.inl ⟨j,hj⟩)))

theorem active_iff {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (r : Fin v → Fin (2*e+1)) (o : S → Bool) (p : Nat → Nat)
    (hp : ∀ i, LoosePathRoot.Paired p (fixedPair wire S r o i)) (j : Fin m) :
    j∈S ↔ p (twin v e (j,false))≠twin v e (j,true) := by
  constructor
  · intro hj
    rw [active_apply wire S r o p hp j hj false]
    have hlo := port_low wire (j,Bool.xor false (o ⟨j,hj⟩))
    have hhi := twin_high v e (j,true)
    omega
  · intro hh
    by_contra hj
    exact hh (inactive_apply wire S r o p hp j hj)

theorem path_hits {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (r : Fin v → Fin (2*e+1)) (o : S → Bool) (p : Nat → Nat)
    (hp : ∀ i, LoosePathRoot.Paired p (fixedPair wire S r o i)) (it : Fin v × Fin e) :
    Hits p (LoosePathStructure.pathTest e (it.1.val,it.2.val)) :=
  hits_of_paired p _ _ (pathPair_card r it) (hp (Sum.inl it)) (pathPair_subset r it)

theorem switch_hits {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (r : Fin v → Fin (2*e+1)) (o : S → Bool) (p : Nat → Nat)
    (hp : ∀ i, LoosePathRoot.Paired p (fixedPair wire S r o i)) (z : Fin m × Bool) :
    Hits p (LoosePathStructure.switchTest v e m wire z) := by
  classical
  rcases z with ⟨j,c⟩
  by_cases hj : j∈S
  · let b := Bool.xor c (o ⟨j,hj⟩)
    have hb : Bool.xor b (o ⟨j,hj⟩)=c := by
      dsimp [b]
      cases c <;> cases o ⟨j,hj⟩ <;> rfl
    have he := active_apply wire S r o p hp j hj b
    rw [hb] at he
    refine ⟨twin v e (j,b),?_,?_,?_⟩
    · cases b <;> simp [twin,LoosePathStructure.switchTest]
    · rw [he]
      simp [port,LoosePathStructure.switchTest]
    · rw [he]
      have hlo := port_low wire (j,c)
      have hhi := twin_high v e (j,b)
      omega
  · have he := inactive_apply wire S r o p hp j hj
    refine ⟨twin v e (j,false),?_,?_,?_⟩
    · simp [twin,LoosePathStructure.switchTest]
    · rw [he]
      simp [twin,LoosePathStructure.switchTest]
    · rw [he]
      simp [twin]

end LoosePathSoundness


namespace LoosePathFinite
open Finset LoosePathNat InvolutionGadget LoosePathConstruction

theorem hits_iff {k : Nat} (P : Equiv.Perm (Fin k)) (R : Finset Nat)
    (hb : ∀ x∈R, x<k) :
    (∃ i : Fin k, i.val∈R ∧ (P i).val∈R ∧ P i≠i) ↔ Hits (natP P) R := by
  constructor
  · rintro ⟨i,hi,hpi,hne⟩
    refine ⟨i.val,hi,?_,?_⟩
    · rw [natP_apply]; exact hpi
    · rw [natP_apply]
      exact fun h => hne (Fin.ext h)
  · rintro ⟨x,hx,hpx,hne⟩
    let i : Fin k := ⟨x,hb x hx⟩
    have heq : natP P x = (P i).val := natP_apply P i
    refine ⟨i,hx,?_,?_⟩
    · rw [←heq]; exact hpx
    · intro h
      apply hne
      rw [heq,h]

 theorem active_iff {v e m : Nat} (P : Equiv.Perm (Fin (v*(2*e+1)+2*m))) (j : Fin m) :
    (¬ ∃ i : Fin (v*(2*e+1)+2*m), i.val=v*(2*e+1)+2*j.val ∧
      (P i).val=v*(2*e+1)+2*j.val+1) ↔
    natP P (twin v e (j,false)) ≠ twin v e (j,true) := by
  have hfalse : twin v e (j,false)=v*(2*e+1)+2*j.val := by simp [twin]
  have htrue : twin v e (j,true)=v*(2*e+1)+2*j.val+1 := by simp [twin]
  constructor
  · intro h hn
    let i : Fin (v*(2*e+1)+2*m) := ⟨twin v e (j,false),twin_bound v e (j,false)⟩
    apply h
    refine ⟨i,hfalse,?_⟩
    have hn' : natP P i.val = twin v e (j,true) := hn
    rw [natP_apply,htrue] at hn'
    exact hn'
  · intro h ⟨i,hi,hpi⟩
    apply h
    have hii : i.val=twin v e (j,false) := hi.trans hfalse.symm
    rw [←hii,natP_apply,hpi,htrue]

end LoosePathFinite


namespace UniqueLabelEquiv

noncomputable def equivalence {α β : Type*} (W : α → Prop) (R : β → α → Prop)
 (exists_unique : ∀ a, W a → ∃! b, R b a)
 (sound : ∀ b a, R b a → W a) :
 {a // W a} ≃ (b : β) × {a // R b a} := by
 let forget : ((b : β) × {a // R b a}) → {a // W a} :=
  fun x => ⟨x.2.val,sound x.1 x.2.val x.2.property⟩
 have hi : Function.Injective forget := by
  rintro ⟨b,⟨a,ha⟩⟩ ⟨c,⟨a',ha'⟩⟩ he
  have haa : a=a' := congrArg Subtype.val he
  subst a'
  have hbc : b=c := (exists_unique a (sound b a ha)).unique ha ha'
  subst c
  rfl
 have hs : Function.Surjective forget := by
  intro a
  obtain ⟨b,hb,huniq⟩ := exists_unique a a.property
  exact ⟨⟨b,⟨a.val,hb⟩⟩,rfl⟩
 exact (Equiv.ofBijective forget ⟨hi,hs⟩).symm

theorem card_eq_sigma {α β : Type*} (W : α → Prop) (R : β → α → Prop)
 (exists_unique : ∀ a, W a → ∃! b, R b a)
 (sound : ∀ b a, R b a → W a) :
 Nat.card {a // W a} = Nat.card ((b : β) × {a // R b a}) :=
 Nat.card_congr (equivalence W R exists_unique sound)

theorem card_eq_sum {α β : Type*} [Fintype β] (W : α → Prop) (R : β → α → Prop)
 [∀ b, Finite {a // R b a}]
 (exists_unique : ∀ a, W a → ∃! b, R b a)
 (sound : ∀ b a, R b a → W a) :
 Nat.card {a // W a} = ∑ b, Nat.card {a // R b a} := by
 rw [card_eq_sigma W R exists_unique sound,Nat.card_sigma]

end UniqueLabelEquiv
namespace LoosePathCounting
open Finset LoosePathConstruction LoosePathNat InvolutionGadget

def Parameters {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) := (S → Bool) × {r : Fin v → Fin (2*e+1) // Pinned wire S r}

def portValue {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (z : Fin m × Bool) : Fin (2*e+1) :=
  ⟨LoosePathStructure.leaf e (wire z).2.val,LoosePathStructure.leaf_lt (wire z).2.isLt⟩

theorem pinned_iff {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (r : Fin v → Fin (2*e+1)) :
    Pinned wire S r ↔ ∀ z∈S ×ˢ (Finset.univ : Finset Bool), r (wire z).1=portValue wire z := by
  constructor
  · intro hp z hz
    apply Fin.ext
    exact Nat.add_left_cancel (hp z (Finset.mem_product.mp hz).1)
  · intro hp z hz
    have hh := congrArg Fin.val (hp z (Finset.mem_product.mpr ⟨hz,Finset.mem_univ _⟩))
    exact congrArg (fun x => (wire z).1.val*(2*e+1)+x) hh

theorem portValue_injective {v e m : Nat} (he : 0<e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) :
    Function.Injective (fun z => ((wire z).1,portValue wire z)) := by
  intro x y hh
  apply wire.injective
  apply Prod.ext
  · exact congrArg (fun z : Fin v × Fin (2*e+1) => z.1) hh
  · apply LoosePathStructure.leaf_inj he
    exact congrArg (fun z : Fin v × Fin (2*e+1) => z.2.val) hh

noncomputable def parameterEquiv {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) : Parameters wire S ≃
      ((S → Bool) × {r : Fin v → Fin (2*e+1) //
        ∀ z∈S ×ˢ (Finset.univ : Finset Bool), r (wire z).1=portValue wire z}) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.subtypeEquivRight (pinned_iff wire S))

theorem parameter_card {v e m : Nat} (he : 0<e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) (S : Finset (Fin m)) :
    Nat.card (Parameters wire S) =
      if ((S ×ˢ (Finset.univ : Finset Bool)).image (fun z => (wire z).1)).card=2*S.card
      then 2^S.card * (2*e+1)^(v-2*S.card) else 0 := by
  classical
  by_cases hc : ((S ×ˢ (Finset.univ : Finset Bool)).image (fun z => (wire z).1)).card=2*S.card
  · rw [if_pos hc,Nat.card_congr (parameterEquiv wire S)]
    exact LoosePathParameters.card_activeParameters (by omega) S (fun z => (wire z).1) (portValue wire) hc
  · rw [if_neg hc]
    haveI : IsEmpty (Parameters wire S) := ⟨fun b => hc
      (LoosePathParameters.endpoint_card_of_roots S (fun z => (wire z).1) (portValue wire)
        (portValue_injective he wire) b.2.val ((pinned_iff wire S b.2.val).mp b.2.property))⟩
    simp

def Good {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (P : Equiv.Perm (Fin (v*(2*e+1)+2*m))) : Prop :=
  Function.Involutive P ∧
  (∀ i : Fin v, ∀ t : Fin e, Hits (natP P) (LoosePathStructure.pathTest e (i.val,t.val))) ∧
  (∀ z : Fin m × Bool, Hits (natP P) (LoosePathStructure.switchTest v e m wire z)) ∧
  ∀ j : Fin m, j∈S ↔ natP P (twin v e (j,false))≠twin v e (j,true)

def Matched {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (b : Parameters wire S)
    (P : Equiv.Perm (Fin (v*(2*e+1)+2*m))) : Prop :=
  Function.Involutive P ∧ ∀ i : PairIndex v e m S,
    LoosePathRoot.Paired (natP P) (fixedPair wire S b.2.val b.1 i)

theorem good_unique {v e m : Nat} (he : 0<e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) (S : Finset (Fin m))
    (P : Equiv.Perm (Fin (v*(2*e+1)+2*m))) (hP : Good wire S P) :
    ∃! b : Parameters wire S, Matched wire S b P := by
  obtain ⟨hInv,hpath,hswitch,hactive⟩ := hP
  obtain ⟨r,o,hpin,hpairs⟩ := LoosePathExtraction.extract he wire S (natP P)
    (natP_involutive P hInv) hpath hswitch hactive
  refine ⟨⟨o,⟨r,hpin⟩⟩,⟨hInv,hpairs⟩,?_⟩
  intro b hb
  obtain ⟨hr,ho⟩ := LoosePathExtraction.parameters_unique he wire S (natP P)
    b.2.val r b.1 o hb.2 hpairs
  exact Prod.ext ho (Subtype.ext hr)

theorem matched_good {v e m : Nat}
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) (S : Finset (Fin m))
    (b : Parameters wire S) (P : Equiv.Perm (Fin (v*(2*e+1)+2*m)))
    (hP : Matched wire S b P) : Good wire S P := by
  refine ⟨hP.1,?_,?_,?_⟩
  · intro i t
    exact LoosePathSoundness.path_hits wire S b.2.val b.1 (natP P) hP.2 (i,t)
  · intro z
    exact LoosePathSoundness.switch_hits wire S b.2.val b.1 (natP P) hP.2 z
  · intro j
    exact LoosePathSoundness.active_iff wire S b.2.val b.1 (natP P) hP.2 j

end LoosePathCounting


namespace DisjointPairInvolution
open Finset
variable {ι α : Type*} [DecidableEq α]

def Support (I : Finset ι) (f : ι → Finset α) : Finset α := I.biUnion f

def Related (I : Finset ι) (f : ι → Finset α) (x y : α) : Prop :=
 ∃ i ∈ I, x ∈ f i ∧ y ∈ f i ∧ y ≠ x

theorem pair_index_unique (I : Finset ι) (f : ι → Finset α)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j))
 {i j : ι} (hi : i ∈ I) (hj : j ∈ I) {x : α} (hx : x ∈ f i) (hy : x ∈ f j) : i=j := by
 by_contra h
 exact Finset.disjoint_left.mp (hd i hi j hj h) hx hy

theorem other_unique (A : Finset α) (hc : A.card=2) (x : α) (hx : x ∈ A) :
 ∃! y, y ∈ A ∧ y ≠ x := by
 obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hc
 simp only [mem_insert,mem_singleton] at hx
 rcases hx with rfl|rfl
 · refine ⟨b,⟨by simp,Ne.symm hab⟩,?_⟩
   intro y hy
   simp only [mem_insert,mem_singleton] at hy
   exact hy.1.resolve_left hy.2
 · refine ⟨a,⟨by simp,hab⟩,?_⟩
   intro y hy
   simp only [mem_insert,mem_singleton] at hy
   exact hy.1.resolve_right hy.2

theorem related_unique (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I, (f i).card=2)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j))
 (x : α) (hx : x ∈ Support I f) : ∃! y, Related I f x y := by
 obtain ⟨i,hi,hxi⟩ := Finset.mem_biUnion.mp hx
 obtain ⟨y,hy,huniq⟩ := other_unique (f i) (hc i hi) x hxi
 refine ⟨y,⟨i,hi,hxi,hy⟩,?_⟩
 intro z hz
 obtain ⟨j,hj,hxj,hzj,hne⟩ := hz
 have hji : j=i := (pair_index_unique I f hd hi hj hxi hxj).symm
 subst j
 exact huniq z ⟨hzj,hne⟩

noncomputable def mate (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I, (f i).card=2)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j))
 (x : Support I f) : α := Classical.choose (related_unique I f hc hd x x.property)

theorem mate_spec (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I, (f i).card=2)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j))
 (x : Support I f) : Related I f x (mate I f hc hd x) :=
 (Classical.choose_spec (related_unique I f hc hd x x.property)).1

theorem mate_mem (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I, (f i).card=2)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j))
 (x : Support I f) : mate I f hc hd x ∈ Support I f := by
 obtain ⟨i,hi,hxi,hyi,hne⟩ := mate_spec I f hc hd x
 exact Finset.mem_biUnion.mpr ⟨i,hi,hyi⟩

theorem mate_ne (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I, (f i).card=2)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j))
 (x : Support I f) : mate I f hc hd x ≠ x := by
 obtain ⟨i,hi,hxi,hyi,hne⟩ := mate_spec I f hc hd x
 exact hne

theorem mate_eq (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I, (f i).card=2)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j))
 (x : Support I f) (y : α) (hy : Related I f x y) : mate I f hc hd x = y := by
 exact ((Classical.choose_spec (related_unique I f hc hd x x.property)).2 y hy).symm

noncomputable def map (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I, (f i).card=2)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j)) : Support I f → Support I f :=
 fun x => ⟨mate I f hc hd x,mate_mem I f hc hd x⟩

theorem map_involutive (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I, (f i).card=2)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j)) :
 Function.Involutive (map I f hc hd) := by
 intro x
 apply Subtype.ext
 change mate I f hc hd (map I f hc hd x)=x.val
 apply mate_eq
 obtain ⟨i,hi,hxi,hyi,hne⟩ := mate_spec I f hc hd x
 exact ⟨i,hi,hyi,hxi,Ne.symm hne⟩

noncomputable def perm (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I, (f i).card=2)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j)) : Equiv.Perm (Support I f) :=
 (map_involutive I f hc hd).toPerm

theorem perm_involutive (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I, (f i).card=2)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j)) :
 Function.Involutive (perm I f hc hd) := map_involutive I f hc hd

theorem perm_no_fixed (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I, (f i).card=2)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j))
 (x : Support I f) : perm I f hc hd x ≠ x := by
 intro h
 exact mate_ne I f hc hd x (congrArg Subtype.val h)

theorem perm_pairs (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I, (f i).card=2)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j))
 (i : ι) (hi : i ∈ I) (x y : α) (hx : x ∈ f i) (hy : y ∈ f i) (hne : y ≠ x) :
 (perm I f hc hd ⟨x,Finset.mem_biUnion.mpr ⟨i,hi,hx⟩⟩).val = y :=
 mate_eq I f hc hd _ y ⟨i,hi,hx,hy,hne⟩

theorem support_card (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I, (f i).card=2)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j)) :
 (Support I f).card = 2*I.card := by
 rw [Support,Finset.card_biUnion hd]
 calc
  (∑ i ∈ I, (f i).card) = ∑ i ∈ I, 2 := Finset.sum_congr rfl hc
  _ = 2*I.card := by simp [Nat.mul_comm]

theorem complement_card [Fintype α] (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I, (f i).card=2)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j)) :
 Fintype.card {x // x ∉ Support I f} = Fintype.card α - 2*I.card := by
 rw [Fintype.card_subtype_compl]
 simp only [Fintype.card_coe,support_card I f hc hd]

theorem complement_finset_card [Fintype α] (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I, (f i).card=2)
 (hd : ∀ i ∈ I, ∀ j ∈ I, i≠j → Disjoint (f i) (f j)) :
 (Finset.univ \ Support I f).card = Fintype.card α - 2*I.card := by
 rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,support_card I f hc hd]

end DisjointPairInvolution


namespace BoundedFinsetLift
open Finset

def lift (k : Nat) (A : Finset Nat) : Finset (Fin k) :=
 Finset.univ.filter (fun x => x.val ∈ A)

@[simp] theorem mem_lift {k : Nat} {A : Finset Nat} {x : Fin k} :
 x ∈ lift k A ↔ x.val ∈ A := by simp [lift]

@[simp] theorem lift_empty (k : Nat) : lift k ∅ = ∅ := by ext x; simp

@[simp] theorem lift_union (k : Nat) (A B : Finset Nat) :
 lift k (A ∪ B)=lift k A ∪ lift k B := by ext x; simp

@[simp] theorem lift_inter (k : Nat) (A B : Finset Nat) :
 lift k (A ∩ B)=lift k A ∩ lift k B := by ext x; simp

@[simp] theorem lift_sdiff (k : Nat) (A B : Finset Nat) :
 lift k (A \ B)=lift k A \ lift k B := by ext x; simp

theorem lift_subset {k : Nat} {A B : Finset Nat} (h : A ⊆ B) :
 lift k A ⊆ lift k B := fun _ hx => mem_lift.mpr (h (mem_lift.mp hx))

@[simp] theorem lift_biUnion {ι : Type*} (k : Nat) (I : Finset ι) (f : ι → Finset Nat) :
 lift k (I.biUnion f)=I.biUnion (fun i => lift k (f i)) := by ext x; simp

theorem image_val_lift (k : Nat) (A : Finset Nat) (hA : ∀ x ∈ A, x<k) :
 (lift k A).image Fin.val=A := by
 ext x
 constructor
 · intro hx
   obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
   exact mem_lift.mp hy
 · intro hx
   exact mem_image.mpr ⟨⟨x,hA x hx⟩,mem_lift.mpr hx,rfl⟩

@[simp] theorem lift_image_val (k : Nat) (A : Finset (Fin k)) :
 lift k (A.image Fin.val)=A := by
 ext x
 simp only [mem_lift,mem_image]
 constructor
 · rintro ⟨y,hy,he⟩
   exact (Fin.ext he) ▸ hy
 · intro hx
   exact ⟨x,hx,rfl⟩

theorem lift_card (k : Nat) (A : Finset Nat) (hA : ∀ x ∈ A,x<k) :
 (lift k A).card=A.card := by
 calc
  (lift k A).card = ((lift k A).image Fin.val).card :=
   (Finset.card_image_of_injective _ Fin.val_injective).symm
  _ = A.card := congrArg Finset.card (image_val_lift k A hA)

theorem lift_disjoint (k : Nat) (A B : Finset Nat) (h : Disjoint A B) :
 Disjoint (lift k A) (lift k B) := by
 apply Finset.disjoint_left.mpr
 intro x hx hy
 exact Finset.disjoint_left.mp h (mem_lift.mp hx) (mem_lift.mp hy)

theorem disjoint_of_lift (k : Nat) (A B : Finset Nat) (hA : ∀x∈A,x<k)
 (h : Disjoint (lift k A) (lift k B)) : Disjoint A B := by
 apply Finset.disjoint_left.mpr
 intro x hx hy
 have hx' : (⟨x,hA x hx⟩ : Fin k) ∈ lift k A := mem_lift.mpr hx
 have hy' : (⟨x,hA x hx⟩ : Fin k) ∈ lift k B := mem_lift.mpr hy
 exact Finset.disjoint_left.mp h hx' hy' 

theorem disjoint_lift_iff (k : Nat) (A B : Finset Nat) (hA : ∀x∈A,x<k) :
 Disjoint (lift k A) (lift k B) ↔ Disjoint A B :=
 ⟨disjoint_of_lift k A B hA,lift_disjoint k A B⟩

theorem eq_of_lift_eq (k : Nat) (A B : Finset Nat)
 (hA : ∀x∈A,x<k) (hB : ∀x∈B,x<k) (h : lift k A=lift k B) : A=B := by
 rw [←image_val_lift k A hA,←image_val_lift k B hB,h]

theorem lift_eq_iff (k : Nat) (A B : Finset Nat)
 (hA : ∀x∈A,x<k) (hB : ∀x∈B,x<k) : lift k A=lift k B ↔ A=B :=
 ⟨eq_of_lift_eq k A B hA hB,congrArg (lift k)⟩

end BoundedFinsetLift


namespace InvolutionExtension
abbrev Inv (α : Type*) := {P : Equiv.Perm α // Function.Involutive P}

variable {α : Type*} (p : α → Prop) [DecidablePred p]

def extendFun (q : Inv {x // p x}) (Q : Inv {x // ¬p x}) (x : α) : α :=
 if h : p x then q.1 ⟨x,h⟩ else Q.1 ⟨x,h⟩

@[simp] theorem extend_mem (q : Inv {x // p x}) (Q : Inv {x // ¬p x})
 (x : α) (hx : p x) : extendFun p q Q x = (q.1 ⟨x,hx⟩).val := by
 simp [extendFun,hx]

@[simp] theorem extend_not_mem (q : Inv {x // p x}) (Q : Inv {x // ¬p x})
 (x : α) (hx : ¬p x) : extendFun p q Q x = (Q.1 ⟨x,hx⟩).val := by
 simp [extendFun,hx]

theorem extend_involutive (q : Inv {x // p x}) (Q : Inv {x // ¬p x}) :
 Function.Involutive (extendFun p q Q) := by
 intro x
 by_cases hx : p x
 · rw [extend_mem _ _ _ _ hx,extend_mem _ _ _ _ (q.1 ⟨x,hx⟩).property]
   exact congrArg Subtype.val (q.2 ⟨x,hx⟩)
 · rw [extend_not_mem _ _ _ _ hx,extend_not_mem _ _ _ _ (Q.1 ⟨x,hx⟩).property]
   exact congrArg Subtype.val (Q.2 ⟨x,hx⟩)

def Extensions (q : Inv {x // p x}) :=
 {P : Equiv.Perm α // Function.Involutive P ∧ ∀ x : {x // p x}, P x = (q.1 x).val}

theorem preserves_compl (q : Inv {x // p x}) (P : Extensions p q)
 (x : α) (hx : ¬p x) : ¬p (P.1 x) := by
 intro h
 have he := P.2.2 ⟨P.1 x,h⟩
 have hz : x = (q.1 ⟨P.1 x,h⟩).val := (P.2.1 x).symm.trans he
 exact hx (hz.symm ▸ (q.1 ⟨P.1 x,h⟩).property)

def extract (q : Inv {x // p x}) (P : Extensions p q) : Inv {x // ¬p x} :=
 let f : {x // ¬p x} → {x // ¬p x} := fun x => ⟨P.1 x,preserves_compl p q P x x.property⟩
 have hf : Function.Involutive f := fun x => Subtype.ext (P.2.1 x)
 ⟨hf.toPerm,hf⟩

def extend (q : Inv {x // p x}) (Q : Inv {x // ¬p x}) : Extensions p q :=
 ⟨(extend_involutive p q Q).toPerm,extend_involutive p q Q,
  fun x => extend_mem p q Q x x.property⟩

def extensionEquiv (q : Inv {x // p x}) : Extensions p q ≃ Inv {x // ¬p x} where
 toFun := extract p q
 invFun := extend p q
 left_inv P := by
  apply Subtype.ext
  ext x
  change extendFun p q (extract p q P) x=P.1 x
  by_cases hx : p x
  · rw [extend_mem _ _ _ _ hx]
    exact (P.2.2 ⟨x,hx⟩).symm
  · rw [extend_not_mem _ _ _ _ hx]
    rfl
 right_inv Q := by
  apply Subtype.ext
  ext x
  change extendFun p q Q x=(Q.1 x).val
  exact extend_not_mem p q Q x x.property

def involutiveCongr {β : Type*} (e : α ≃ β) : Inv α ≃ Inv β where
 toFun P := ⟨e.symm.trans (P.1.trans e), fun y => by
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
  rw [P.2,Equiv.apply_symm_apply]⟩
 invFun Q := ⟨e.trans (Q.1.trans e.symm), fun x => by
  simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
  rw [Q.2,Equiv.symm_apply_apply]⟩
 left_inv P := by
  apply Subtype.ext
  ext x
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
 right_inv Q := by
  apply Subtype.ext
  ext x
  simp only [Equiv.trans_apply,Equiv.apply_symm_apply]

theorem card_extensions [Fintype α] (q : Inv {x // p x}) :
 Nat.card (Extensions p q) = Nat.card (Inv (Fin (Fintype.card {x // ¬p x}))) := by
 rw [Nat.card_congr (extensionEquiv p q)]
 exact Nat.card_congr (involutiveCongr (Fintype.equivFin {x // ¬p x}))

end InvolutionExtension

namespace DisjointPairInvolution
open Finset

theorem perm_mem_pair {ι α : Type*} [DecidableEq α]
 (I : Finset ι) (f : ι → Finset α)
 (hc : ∀ i ∈ I,(f i).card=2)
 (hd : ∀ i ∈ I,∀ j ∈ I,i≠j → Disjoint (f i) (f j))
 (i : ι) (hi : i∈I) (x : Support I f) (hx : x.val∈f i) :
 (perm I f hc hd x).val∈f i := by
 obtain ⟨j,hj,hxj,hyj,hne⟩ := mate_spec I f hc hd x
 have hij := pair_index_unique I f hd hi hj hx hxj
 subst j
 exact hyj
end DisjointPairInvolution

namespace BoundedPairCompletion
open Finset
variable {ι : Type*} [Fintype ι]

def finFamily (k : Nat) (f : ι → Finset Nat) (i : ι) : Finset (Fin k) :=
 BoundedFinsetLift.lift k (f i)

def support (k : Nat) (f : ι → Finset Nat) : Finset (Fin k) :=
 Finset.univ.biUnion (finFamily k f)

theorem fin_card (k : Nat) (f : ι → Finset Nat)
 (hc : ∀i,(f i).card=2) (hb : ∀i,∀x∈f i,x<k) (i : ι) :
 (finFamily k f i).card=2 := by
 rw [finFamily,BoundedFinsetLift.lift_card k (f i) (hb i),hc]

theorem fin_disjoint (k : Nat) (f : ι → Finset Nat)
 (hd : ∀i j,i≠j → Disjoint (f i) (f j)) (i j : ι) (hij : i≠j) :
 Disjoint (finFamily k f i) (finFamily k f j) :=
 BoundedFinsetLift.lift_disjoint k (f i) (f j) (hd i j hij)

noncomputable def fixedInvolution (k : Nat) (f : ι → Finset Nat)
 (hc : ∀i,(f i).card=2) (hd : ∀i j,i≠j → Disjoint (f i) (f j))
 (hb : ∀i,∀x∈f i,x<k) : InvolutionExtension.Inv {x //x∈support k f} := by
 classical
 exact ⟨DisjointPairInvolution.perm Finset.univ (finFamily k f)
  (fun i _ => fin_card k f hc hb i) (fun i _ j _ h => fin_disjoint k f hd i j h),
  DisjointPairInvolution.perm_involutive Finset.univ (finFamily k f)
  (fun i _ => fin_card k f hc hb i) (fun i _ j _ h => fin_disjoint k f hd i j h)⟩

theorem fixed_mem (k : Nat) (f : ι → Finset Nat)
 (hc : ∀i,(f i).card=2) (hd : ∀i j,i≠j → Disjoint (f i) (f j))
 (hb : ∀i,∀x∈f i,x<k) (i : ι) (x : {x //x∈support k f})
 (hx : x.val∈finFamily k f i) :
 ((fixedInvolution k f hc hd hb).1 x).val∈finFamily k f i := by
 classical
 exact DisjointPairInvolution.perm_mem_pair Finset.univ (finFamily k f)
  (fun i _ => fin_card k f hc hb i) (fun i _ j _ h => fin_disjoint k f hd i j h)
  i (mem_univ _) x hx

theorem fixed_ne (k : Nat) (f : ι → Finset Nat)
 (hc : ∀i,(f i).card=2) (hd : ∀i j,i≠j → Disjoint (f i) (f j))
 (hb : ∀i,∀x∈f i,x<k) (x : {x //x∈support k f}) :
 ((fixedInvolution k f hc hd hb).1 x).val≠x.val := by
 intro h
 exact DisjointPairInvolution.perm_no_fixed Finset.univ (finFamily k f)
  (fun i _ => fin_card k f hc hb i) (fun i _ j _ h => fin_disjoint k f hd i j h)
  x (Subtype.ext h)

theorem agrees_iff (k : Nat) (f : ι → Finset Nat)
 (hc : ∀i,(f i).card=2) (hd : ∀i j,i≠j → Disjoint (f i) (f j))
 (hb : ∀i,∀x∈f i,x<k) (P : Equiv.Perm (Fin k)) :
 (∀x : {x //x∈support k f}, P x = ((fixedInvolution k f hc hd hb).1 x).val) ↔
 ∀i,LoosePathRoot.Paired (LoosePathNat.natP P) (f i) := by
 classical
 constructor
 · intro h i n hn
   let x : Fin k := ⟨n,hb i n hn⟩
   have hx : x∈finFamily k f i := BoundedFinsetLift.mem_lift.mpr hn
   have hxS : x∈support k f := mem_biUnion.mpr ⟨i,mem_univ _,hx⟩
   have he := h ⟨x,hxS⟩
   have hm := fixed_mem k f hc hd hb i ⟨x,hxS⟩ hx
   have hne := fixed_ne k f hc hd hb ⟨x,hxS⟩
   change LoosePathNat.natP P x.val∈f i ∧ LoosePathNat.natP P x.val≠x.val
   rw [LoosePathNat.natP_apply,he]
   exact ⟨BoundedFinsetLift.mem_lift.mp hm,fun hh => hne (Fin.ext hh)⟩
 · intro h x
   obtain ⟨i,hi,hxi⟩ := mem_biUnion.mp x.property
   have hh := h i x.val.val (BoundedFinsetLift.mem_lift.mp hxi)
   rw [LoosePathNat.natP_apply] at hh
   change P x = DisjointPairInvolution.mate Finset.univ (finFamily k f)
     (fun i _ => fin_card k f hc hb i) (fun i _ j _ hh => fin_disjoint k f hd i j hh) x
   symm
   apply DisjointPairInvolution.mate_eq
   refine ⟨i,hi,hxi,BoundedFinsetLift.mem_lift.mpr hh.1,?_⟩
   intro he
   exact hh.2 (congrArg Fin.val he)

theorem completion_card (k : Nat) (f : ι → Finset Nat)
 (hc : ∀i,(f i).card=2) (hd : ∀i j,i≠j → Disjoint (f i) (f j))
 (hb : ∀i,∀x∈f i,x<k) :
 Nat.card {P : Equiv.Perm (Fin k) // Function.Involutive P ∧
   ∀i,LoosePathRoot.Paired (LoosePathNat.natP P) (f i)} =
 Nat.card (InvolutionExtension.Inv (Fin (k-2*Fintype.card ι))) := by
 classical
 let q := fixedInvolution k f hc hd hb
 let e : {P : Equiv.Perm (Fin k) // Function.Involutive P ∧
   ∀i,LoosePathRoot.Paired (LoosePathNat.natP P) (f i)} ≃
   InvolutionExtension.Extensions (fun x => x∈support k f) q :=
  Equiv.subtypeEquivRight (fun P => and_congr Iff.rfl (agrees_iff k f hc hd hb P).symm)
 rw [Nat.card_congr e,InvolutionExtension.card_extensions]
 have hn : Fintype.card {x //x∉support k f}=k-2*Fintype.card ι := by
  calc
   Fintype.card {x //x∉support k f} = (Finset.univ \ support k f).card :=
    Fintype.card_of_subtype _ (fun x => by simp)
   _ = k-2*Fintype.card ι := by
    have hh := DisjointPairInvolution.complement_finset_card Finset.univ (finFamily k f)
     (fun i _ => fin_card k f hc hb i) (fun i _ j _ h => fin_disjoint k f hd i j h)
    simpa only [support,DisjointPairInvolution.Support,Fintype.card_fin,Finset.card_univ] using hh
 rw [hn]

end BoundedPairCompletion


namespace LoosePathCompletion
open LoosePathConstruction

theorem fixed_completion_card {v e m : Nat} (he : 0<e)
 (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
 (S : Finset (Fin m)) (r : Fin v → Fin (2*e+1)) (o : S → Bool)
 (hpin : Pinned wire S r) :
 Nat.card {P : Equiv.Perm (Fin (v*(2*e+1)+2*m)) // Function.Involutive P ∧
   ∀i : PairIndex v e m S,
    LoosePathRoot.Paired (LoosePathNat.natP P) (fixedPair wire S r o i)} =
 Nat.card {Q : Equiv.Perm (Fin (v-2*S.card)) // Function.Involutive Q} := by
 have h := BoundedPairCompletion.completion_card (v*(2*e+1)+2*m) (fixedPair wire S r o)
  (fixedPair_card wire S r o) (fixedPair_disjoint he wire S r o hpin)
  (fun i x hx => fixedPair_bound wire S r o i hx)
 simpa only [free_count] using h

end LoosePathCompletion

namespace LoosePathCounting
open Finset
theorem good_card {v e m : Nat} (he : 0<e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) (S : Finset (Fin m)) :
    Nat.card {P : Equiv.Perm (Fin (v*(2*e+1)+2*m)) // Good wire S P} =
      if ((S ×ˢ (Finset.univ : Finset Bool)).image (fun z => (wire z).1)).card=2*S.card
      then 2^S.card*(2*e+1)^(v-2*S.card)*
        Nat.card {Q : Equiv.Perm (Fin (v-2*S.card)) // Function.Involutive Q} else 0 := by
  classical
  letI : Fintype (Parameters wire S) := by unfold Parameters; infer_instance
  rw [UniqueLabelEquiv.card_eq_sum (Good wire S) (Matched wire S)
    (good_unique he wire S) (matched_good wire S)]
  have hf (b : Parameters wire S) :
      Nat.card {P : Equiv.Perm (Fin (v*(2*e+1)+2*m)) // Matched wire S b P} =
      Nat.card {Q : Equiv.Perm (Fin (v-2*S.card)) // Function.Involutive Q} :=
    LoosePathCompletion.fixed_completion_card he wire S b.2.val b.1 b.2.property
  simp_rw [hf]
  rw [Finset.sum_const,smul_eq_mul,Finset.card_univ,← Nat.card_eq_fintype_card,parameter_card he]
  split_ifs <;> simp

end LoosePathCounting


namespace LoosePathPositive

theorem involutions_pos (n : Nat) :
    0 < Nat.card {P : Equiv.Perm (Fin n) // Function.Involutive P} := by
  letI : Nonempty {P : Equiv.Perm (Fin n) // Function.Involutive P} :=
    ⟨⟨Equiv.refl _,fun _ => rfl⟩⟩
  exact Nat.card_pos

theorem of_fiber {α : Type*} [Finite α] (W T : α → Prop)
    (h : 0 < Nat.card {a // W a ∧ T a}) : 0 < Nat.card {a // W a} := by
  obtain ⟨⟨a,ha⟩⟩ := (Nat.card_pos_iff.mp h).1
  letI : Nonempty {a // W a} := ⟨⟨a,ha.1⟩⟩
  exact Nat.card_pos

theorem of_empty_fiber {α : Type*} [Finite α] (W T : α → Prop) (q v : Nat)
    (hq : 0 < q)
    (hc : Nat.card {a // W a ∧ T a} =
      q^v * Nat.card {P : Equiv.Perm (Fin v) // Function.Involutive P}) :
    0 < Nat.card {a // W a} := by
  apply of_fiber W T
  rw [hc]
  exact Nat.mul_pos (Nat.pow_pos hq) (involutions_pos v)

end LoosePathPositive

namespace LoosePathOriginal
open Finset LoosePathStructure LoosePathConstruction LoosePathNat InvolutionGadget

def tests {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) : Finset (Finset Nat) :=
  ((Finset.range v ×ˢ Finset.range e).image (pathTest e)) ∪
    Finset.univ.image (switchTest v e m wire)

def wins {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (P : Equiv.Perm (Fin (v*(2*e+1)+2*m))) : Prop :=
  Function.Involutive P ∧ ∀ R∈tests wire,
    ∃ i : Fin (v*(2*e+1)+2*m), i.val∈R ∧ (P i).val∈R ∧ P i≠i

noncomputable def active {v e m : Nat} (P : Equiv.Perm (Fin (v*(2*e+1)+2*m))) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => ¬∃ i : Fin (v*(2*e+1)+2*m),
    i.val=v*(2*e+1)+2*j.val ∧ (P i).val=v*(2*e+1)+2*j.val+1)

theorem tests_bound {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (R : Finset Nat) (hR : R∈tests wire) (x : Nat) (hx : x∈R) : x<v*(2*e+1)+2*m := by
  rcases Finset.mem_union.mp hR with hR|hR
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hR
    have := path_mem_lt hz hx
    omega
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hR
    have hp := port_lt wire z
    have hz := z.1.isLt
    simp only [switchTest,Finset.mem_insert,Finset.mem_singleton] at hx
    omega

theorem path_mem_tests {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (i : Fin v) (t : Fin e) : pathTest e (i.val,t.val)∈tests wire := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨(i.val,t.val),Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr i.isLt,Finset.mem_range.mpr t.isLt⟩,rfl⟩

theorem switch_mem_tests {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (z : Fin m × Bool) : switchTest v e m wire z∈tests wire :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩)

theorem wins_iff {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (P : Equiv.Perm (Fin (v*(2*e+1)+2*m))) : wins wire P ↔
    Function.Involutive P ∧
    (∀ i : Fin v, ∀ t : Fin e, Hits (natP P) (pathTest e (i.val,t.val))) ∧
    ∀ z : Fin m × Bool, Hits (natP P) (switchTest v e m wire z) := by
  constructor
  · rintro ⟨hInv,hw⟩
    refine ⟨hInv,?_,?_⟩
    · intro i t
      have hm := path_mem_tests wire i t
      exact (LoosePathFinite.hits_iff P _ (tests_bound wire _ hm)).mp (hw _ hm)
    · intro z
      have hm := switch_mem_tests wire z
      exact (LoosePathFinite.hits_iff P _ (tests_bound wire _ hm)).mp (hw _ hm)
  · rintro ⟨hInv,hpath,hswitch⟩
    refine ⟨hInv,?_⟩
    intro R hR
    apply (LoosePathFinite.hits_iff P R (tests_bound wire R hR)).mpr
    rcases Finset.mem_union.mp hR with hh|hh
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hh
      have hz := Finset.mem_product.mp hz
      exact hpath ⟨z.1,Finset.mem_range.mp hz.1⟩ ⟨z.2,Finset.mem_range.mp hz.2⟩
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hh
      exact hswitch z

theorem mem_active {v e m : Nat} (P : Equiv.Perm (Fin (v*(2*e+1)+2*m))) (j : Fin m) :
    j∈active (v:=v) (e:=e) (m:=m) P ↔ natP P (twin v e (j,false))≠twin v e (j,true) := by
  classical
  simp only [active,Finset.mem_filter,Finset.mem_univ,true_and]
  exact LoosePathFinite.active_iff P j

theorem good_iff {v e m : Nat} (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)))
    (S : Finset (Fin m)) (P : Equiv.Perm (Fin (v*(2*e+1)+2*m))) :
    (wins wire P ∧ active (v:=v) (e:=e) (m:=m) P=S) ↔ LoosePathCounting.Good wire S P := by
  rw [wins_iff]
  constructor
  · rintro ⟨⟨hInv,hpath,hswitch⟩,ha⟩
    refine ⟨hInv,hpath,hswitch,?_⟩
    intro j
    rw [← ha]
    exact mem_active P j
  · rintro ⟨hInv,hpath,hswitch,ha⟩
    refine ⟨⟨hInv,hpath,hswitch⟩,?_⟩
    apply Finset.ext
    intro j
    exact (mem_active P j).trans (ha j).symm

theorem fiber_card {v e m : Nat} (he : 0<e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) (S : Finset (Fin m)) :
    Nat.card {P : Equiv.Perm (Fin (v*(2*e+1)+2*m)) // wins wire P ∧ active (v:=v) (e:=e) (m:=m) P=S} =
      if ((S ×ˢ (Finset.univ : Finset Bool)).image (fun z => (wire z).1)).card=2*S.card
      then 2^S.card*(2*e+1)^(v-2*S.card)*
        Nat.card {Q : Equiv.Perm (Fin (v-2*S.card)) // Function.Involutive Q} else 0 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (good_iff wire S))]
  exact LoosePathCounting.good_card he wire S

theorem wins_positive {v e m : Nat} (he : 0<e)
    (wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2))) :
    0<Nat.card {P : Equiv.Perm (Fin (v*(2*e+1)+2*m)) // wins wire P} := by
  have hc := fiber_card he wire ∅
  have hp : 0<Nat.card {P : Equiv.Perm (Fin (v*(2*e+1)+2*m)) //
      wins wire P ∧ active (v:=v) (e:=e) (m:=m) P=∅} := by
    rw [hc]
    simp only [Finset.card_empty,Finset.empty_product,Finset.image_empty,Nat.mul_zero,
      Nat.sub_zero,pow_zero,one_mul,ite_true,eq_self_iff_true]
    exact Nat.mul_pos (Nat.pow_pos (by omega)) (LoosePathPositive.involutions_pos v)
  exact LoosePathPositive.of_fiber (wins wire) (fun P => active (v:=v) (e:=e) (m:=m) P=∅) hp

end LoosePathOriginal

end PEqualNP.Outside.L_lib_930_aux

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
open PEqualNP.Outside.L_lib_930_aux in
theorem PEqualNP.Outside.L_lib_930 : ∀ (v e m : Nat), 0 < e → ∀ wire : (Fin m × Bool) ≃ (Fin v × Fin (e+2)),
  let q := 2*e+1
  let k := v*q+2*m
  let leaf := fun j : Nat => if j = 0 then 0 else if j = e+1 then 2*e else 2*j-1
  let atPort := fun z : Fin m × Bool => (wire z).1.val*q + leaf (wire z).2.val
  let path := ((Finset.range v).product (Finset.range e)).image (fun z =>
    let b := z.1*q+2*z.2
    ({b,b+1,b+2} : Finset Nat))
  let switches := Finset.univ.image (fun z : Fin m × Bool =>
    let b := v*q+2*z.1.val
    ({b,b+1,atPort z} : Finset Nat))
  let H := path ∪ switches
  let wins := fun P : Equiv.Perm (Fin k) => Function.Involutive P ∧
    ∀ R ∈ H, ∃ i : Fin k, i.val ∈ R ∧ (P i).val ∈ R ∧ P i ≠ i
  let active := fun P : Equiv.Perm (Fin k) => Finset.univ.filter (fun j : Fin m =>
    ¬ ∃ i : Fin k, i.val = v*q+2*j.val ∧ (P i).val = v*q+2*j.val+1)
  let ends := fun S : Finset (Fin m) =>
    (S.product (Finset.univ : Finset Bool)).image (fun z => (wire z).1)
  let I := fun u : Nat => Nat.card {P : Equiv.Perm (Fin u) // Function.Involutive P}
  H.card = v*e+2*m ∧ (∀ R ∈ H, R.card = 3) ∧
  (∀ i : Fin k, (H.filter (fun R => i.val ∈ R)).card = 2) ∧
  0 < Nat.card {P : Equiv.Perm (Fin k) // wins P} ∧
  ∀ S : Finset (Fin m), Nat.card {P : Equiv.Perm (Fin k) // wins P ∧ active P = S} =
    if (ends S).card = 2*S.card then
      2^S.card * q^(v-2*S.card) * I (v-2*S.card) else 0 := by
  classical
  intro v e m he wire
  dsimp only
  have ha (P : Equiv.Perm (Fin (v*(2*e+1)+2*m))) :
      (Finset.univ : Finset (Fin m)).filter (fun j =>
        ¬∃ i : Fin (v*(2*e+1)+2*m), i.val=v*(2*e+1)+2*j.val ∧
          (P i).val=v*(2*e+1)+2*j.val+1) =
      LoosePathOriginal.active (v:=v) (e:=e) (m:=m) P := by
    ext j
    simp [LoosePathOriginal.active]
  simp_rw [ha]
  change (LoosePathOriginal.tests wire).card = v*e+2*m ∧
    (∀ R∈LoosePathOriginal.tests wire,R.card=3) ∧
    (∀ i : Fin (v*(2*e+1)+2*m), ((LoosePathOriginal.tests wire).filter (fun R => i.val∈R)).card=2) ∧
    (0<Nat.card {P : Equiv.Perm (Fin (v*(2*e+1)+2*m)) // LoosePathOriginal.wins wire P}) ∧
    ∀ S : Finset (Fin m), Nat.card {P : Equiv.Perm (Fin (v*(2*e+1)+2*m)) //
      LoosePathOriginal.wins wire P ∧ LoosePathOriginal.active (v:=v) (e:=e) (m:=m) P=S} =
      if ((S ×ˢ (Finset.univ : Finset Bool)).image (fun z => (wire z).1)).card=2*S.card then
      2^S.card*(2*e+1)^(v-2*S.card)*Nat.card {Q : Equiv.Perm (Fin (v-2*S.card)) // Function.Involutive Q} else 0
  exact ⟨(LoosePathStructure.basic he wire).1,(LoosePathStructure.basic he wire).2,
    LoosePathStructure.degree he wire,LoosePathOriginal.wins_positive he wire,
    LoosePathOriginal.fiber_card he wire⟩
