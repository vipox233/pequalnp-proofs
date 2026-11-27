import Mathlib

namespace PEqualNP.Outside.L_lib_606_aux

abbrev K := ZMod 2
def bit (b : Bool) : K := if b then 1 else 0
theorem parity (k : ℕ) : bit (k % 2 == 1) = (k : K) := by
  rw [← ZMod.natCast_mod k 2]
  have h := k.mod_lt (by decide : 0<2)
  rcases (by omega : k%2=0 ∨ k%2=1) with e|e <;> rw [e] <;> rfl

noncomputable def mon {V : Type} (s : Finset V) (w : V → Bool) : K := by
  classical
  exact if ∀ v ∈ s, w v=true then 1 else 0

noncomputable def poly {V : Type} (T : Finset (Finset V)) (w : V → Bool) : K :=
  ∑ s ∈ T, mon s w
def vary {V : Type} [DecidableEq V] (U A : Finset V) (w : V → Bool) (v : V) :=
  if v ∈ U then decide (v ∈ A) else w v

theorem monSum {V : Type} [DecidableEq V] (U M : Finset V) (w : V → Bool)
    (maximal : U ⊆ M → M=U) :
    (∑ A ∈ U.powerset, mon M (vary U A w)) = if M=U then 1 else 0 := by
  classical
  have spec (A : Finset V) :
      (∀ v ∈ M, vary U A w v=true) ↔ M ∩ U ⊆ A ∧ ∀ v ∈ M, v ∉ U → w v=true := by
    constructor
    · intro h
      exact ⟨fun v hv => by
        obtain ⟨hm,hu⟩ := Finset.mem_inter.mp hv
        simpa [vary,hu] using h v hm,
        fun v hm hu => by simpa [vary,hu] using h v hm⟩
    · rintro ⟨sub,ok⟩ v hm
      by_cases hu : v ∈ U
      · simp [vary,hu,sub (Finset.mem_inter.mpr ⟨hm,hu⟩)]
      · simpa [vary,hu] using ok v hm hu
  by_cases outside : ∀ v ∈ M, v ∉ U → w v=true
  · have summand (A : Finset V) : mon M (vary U A w) = if M ∩ U ⊆ A then 1 else 0 := by
      by_cases sub : M ∩ U ⊆ A
      · exact (ite_eq_left ((spec A).mpr ⟨sub,outside⟩)).trans (ite_eq_left sub).symm
      · exact (ite_eq_right (fun h => sub ((spec A).mp h).1)).trans (ite_eq_right sub).symm
    simp_rw [summand]
    rw [Finset.sum_boole,← Finset.Icc_eq_filter_powerset,Finset.card_Icc_finset Finset.inter_subset_right]
    by_cases eq : M=U
    · subst M; simp
    · have proper : M ∩ U ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right,by
        intro equal; apply eq; apply maximal; rw [← equal]; exact Finset.inter_subset_left⟩
      have less := Finset.card_lt_card proper
      obtain ⟨e,he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt less)
      rw [ite_eq_right eq,he,pow_succ,Nat.cast_mul]
      rw [show ((2 : ℕ) : K)=0 by decide,mul_zero]
  · have ne : M ≠ U := by
      rintro rfl; exact outside (fun v hv hn => (hn hv).elim)
    simp only [mon,spec,outside,and_false,ite_false,Finset.sum_const_zero,ite_eq_right ne]

theorem cubeSum {V : Type} [DecidableEq V] (U : Finset V) (T : Finset (Finset V))
    (mem : U ∈ T) (maximal : ∀ s ∈ T, U ⊆ s → s=U) (w : V → Bool) :
    (∑ A ∈ U.powerset, poly T (vary U A w)) = 1 := by
  classical
  unfold poly
  rw [Finset.sum_comm]
  calc
    _ = ∑ s ∈ T, (if s=U then 1 else 0 : K) :=
      Finset.sum_congr rfl (fun s hs => monSum _ _ _ (maximal s hs))
    _ = 1 := by simp [mem]

theorem findSupport {V : Type} [DecidableEq V] (U : Finset V) (T : Finset (Finset V))
    (mem : U ∈ T) (maximal : ∀ s ∈ T, U ⊆ s → s=U) (w : V → Bool) :
    ∃ A ∈ U.powerset, poly T (vary U A w)=1 := by
  classical
  by_contra! no
  have zero (v : K) : v ≠ 1 → v=0 := by revert v; decide
  have h := cubeSum U T mem maximal w
  rw [Finset.sum_eq_zero (fun a ha => zero _ (no a ha))] at h
  exact zero_ne_one h

theorem repairBound {V : Type} [DecidableEq V] (U : Finset V)
    (bad good : Finset (V → Bool))
    (repair : ∀ w ∈ bad, ∃ y ∈ good, ∀ v ∉ U, y v=w v) :
    bad.card ≤ 2^U.card * good.card := by
  classical
  choose fix inside agrees using fun x : (↥bad) => repair x.val x.property
  let keep := fun (x : (↥bad)) => U.filter (fun v => x.val v = true)
  let enc : (↥bad) → (↥U.powerset) × (↥good) := fun x =>
    (⟨keep x,Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩,⟨fix x,inside x⟩)
  have inj : Function.Injective enc := by
    intro x y eq
    have own : keep x=keep y := congrArg (fun h : (↥U.powerset) × (↥good) => h.1.val) eq
    have rep : fix x=fix y := congrArg (fun h : (↥U.powerset) × (↥good) => h.2.val) eq
    apply Subtype.ext; funext v; by_cases hv : v ∈ U
    · have same : v ∈ keep x ↔ v ∈ keep y := by rw [own]
      have hbits : (x.val v=true ↔ y.val v=true) := by
        simpa only [keep,Finset.mem_filter,hv,true_and] using same
      exact Bool.eq_iff_iff.mpr hbits
    · exact (agrees x v hv).symm.trans ((congrFun rep v).trans (agrees y v hv))
  simpa using Fintype.card_le_of_injective enc inj

abbrev W (V : Type) := V → Bool
def D {V : Type} (d : ℕ) (f : W V → K) := ∃ t : Finset (Finset V),
  (∀ a ∈ t, a.card ≤ d) ∧ ∀ x, f x = ∑ a ∈ t, mon a x

theorem twoZero (z : K) : z+z=0 := by revert z; decide

theorem normalize {V I : Type} (s : Finset I) (m : I → Finset V) (d : ℕ)
    (bound : ∀ i ∈ s, (m i).card ≤ d) : D d (fun x => ∑ i ∈ s, mon (m i) x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅,by simp,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨t,ht,eq⟩ := ih (fun j hj => bound j (Finset.mem_insert_of_mem hj))
    by_cases h : m i ∈ t
    · refine ⟨t.erase (m i),fun a ha => ht a (Finset.mem_of_mem_erase ha),?_⟩
      intro x
      dsimp only at eq ⊢
      rw [Finset.sum_insert hi,eq x,← Finset.add_sum_erase t (fun a => mon a x) h,
        ← add_assoc,twoZero,zero_add]
    · refine ⟨insert (m i) t,?_,?_⟩
      · intro a ha; rcases Finset.mem_insert.mp ha with h'|h'
        · subst a; exact bound i (Finset.mem_insert_self ..)
        · exact ht a h'
      · intro x; dsimp only at eq ⊢; rw [Finset.sum_insert hi,Finset.sum_insert h,eq x]

theorem dMono {V : Type} {d e : ℕ} {f : W V → K} (h : D d f) (le : d ≤ e) : D e f := by
  obtain ⟨t,ht,eq⟩ := h
  exact ⟨t,fun a ha => (ht a ha).trans le,eq⟩

theorem dZero {V : Type} (d : ℕ) : D d (fun _ : W V => 0) :=
  ⟨∅, by simp,by simp⟩

theorem dOne {V : Type} : D 0 (fun _ : W V => 1) := by
  classical
  exact ⟨{∅},by simp,by intro x; rw [Finset.sum_singleton]; simp [mon]⟩

theorem dVar {V : Type} (v : V) : D 1 (fun x : W V => if x v = true then 1 else 0) := by
  classical
  exact ⟨{{v}},by simp,by intro x; rw [Finset.sum_singleton]; simp [mon]⟩

theorem dAdd {V : Type} {d : ℕ} {f g : W V → K} (hf : D d f) (hg : D d g) :
    D d (fun x => f x + g x) := by
  classical
  obtain ⟨a,ba,ea⟩ := hf
  obtain ⟨b,bb,eb⟩ := hg
  let mon : Finset V ⊕ Finset V → Finset V := Sum.elim id id
  have h := normalize (a.disjSum b) mon d (by
    intro i hi; cases i with
    | inl i => exact ba i (by simpa using hi)
    | inr i => exact bb i (by simpa using hi))
  simpa only [Finset.sum_disjSum,mon,Sum.elim_inl,Sum.elim_inr,id_eq,← ea,← eb] using h

theorem evUnion {V : Type} [DecidableEq V] (a b : Finset V) (x : W V) :
    mon (a ∪ b) x = mon a x * mon b x := by
  classical
  simp only [mon,Finset.forall_mem_union]
  split_ifs <;> simp_all

theorem dMul {V : Type} {d e : ℕ} {f g : W V → K} (hf : D d f) (hg : D e g) :
    D (d+e) (fun x => f x * g x) := by
  classical
  obtain ⟨a,ba,ea⟩ := hf
  obtain ⟨b,bb,eb⟩ := hg
  have h := normalize (a ×ˢ b) (fun p => p.1 ∪ p.2) (d+e) (by
    intro i hi
    exact (Finset.card_union_le ..).trans (Nat.add_le_add
      (ba i.1 (Finset.mem_product.mp hi).1) (bb i.2 (Finset.mem_product.mp hi).2)))
  simpa only [Finset.sum_product,evUnion,← Finset.mul_sum,← Finset.sum_mul,← ea,← eb] using h

theorem dProdCost {V I : Type} (s : Finset I) (cost : I → ℕ) (f : I → W V → K)
    (h : ∀ i ∈ s, D (cost i) (f i)) :
    D (∑ i ∈ s, cost i) (fun w => ∏ i ∈ s, f i w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (dOne (V:=V))
  | @insert i s hi ih =>
    simpa [hi] using dMul (h _ (Finset.mem_insert_self ..)) (ih (fun a ha => h a (Finset.mem_insert_of_mem ha)))

theorem dMatch {V : Type} {q : W V → Bool} {d : ℕ} (hq : D d (fun x => bit (q x))) (b : Bool) :
    D d (fun x => if q x=b then 1 else 0) := by
  cases b with
  | true => exact hq
  | false =>
    have h := dAdd (dMono (dOne (V:=V)) (Nat.zero_le d)) hq
    convert h using 1
    funext x; cases q x <;> decide

theorem prodTest {I : Type} (s : Finset I) (P : I → Prop) [DecidablePred P] :
    (∏ i ∈ s, if P i then (1:K) else 0) = if ∀ i ∈ s, P i then 1 else 0 := by
  classical
  by_cases ok : ∀ i ∈ s, P i
  · rw [ite_eq_left ok]; apply Finset.prod_eq_one; intro i hi; simp [ok i hi]
  · rw [ite_eq_right ok]; push Not at ok; obtain ⟨i,hi,no⟩ := ok
    exact Finset.prod_eq_zero hi (ite_eq_right no)

theorem dMux {I : Type} (i : I) (a b : Bool) :
    D 1 (fun z : W I => bit (if z i then a else b)) := by
  have h : D 1 (fun z : W I => bit (z i)) := dVar i
  cases a <;> cases b
  · simpa [bit] using dZero (V:=I) 1
  · convert dMatch h false using 1
    funext z; cases z i <;> rfl
  · convert h using 1
    funext z; cases z i <;> rfl
  · simpa [bit] using dMono (dOne (V:=I)) (by decide : 0≤1)

theorem dSumTerms {V I : Type} (s : Finset I) (f : I → W V → K) (d : ℕ)
    (h : ∀ i ∈ s, D d (f i)) : D d (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (dZero (V:=V) d)
  | @insert i s hi ih =>
    simpa [hi] using dAdd (h i (Finset.mem_insert_self ..)) (ih (fun a ha => h a (Finset.mem_insert_of_mem ha)))

theorem pull {V I : Type} (e : W I → W V) (lin : ∀ v, D 1 (fun z => bit (e z v)))
    {d : ℕ} {f : W V → K} (h : D d f) : D d (fun z => f (e z)) := by
  classical
  obtain ⟨T,sz,val⟩ := h
  have hmon (a : Finset V) : D a.card (fun z => mon a (e z)) := by
    have h := dProdCost a (fun _ => 1) (fun v z => bit (e z v)) (fun v _ => lin v)
    simpa only [Finset.sum_const,smul_eq_mul,mul_one,bit,prodTest,mon] using h
  simpa only [val] using dSumTerms T (fun a z => mon a (e z)) d (fun a ha => dMono (hmon a) (sz a ha))

theorem supportSize {n d : ℕ} (f : W (Fin n) → K) (h : D d f) (base : W (Fin n)) (yes : f base=1) :
    2^(n-d) ≤ (Finset.univ.filter (fun x => f x=1)).card := by
  classical
  let S := Finset.univ.filter (fun x => f x=1)
  obtain ⟨T,sz,val⟩ := h
  have live : T.Nonempty := by
    by_contra! h
    have e := val base; rw [yes,h,Finset.sum_empty] at e;exact one_ne_zero e
  obtain ⟨U,hu,max⟩ := T.exists_max_image Finset.card live
  have mx (a) (ha : a ∈ T) (sub : U ⊆ a) : a=U :=
    (Finset.eq_of_subset_of_card_le sub (max a ha)).symm
  have large := repairBound U Finset.univ S (by
    intro x _
    obtain ⟨A,_,hit⟩ := findSupport U T hu mx x
    refine ⟨vary U A x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(val _).trans hit⟩,?_⟩
    intro v hv; simp [vary,hv])
  have le : 2^n ≤ 2^U.card*S.card := by simpa [W] using large
  have card := sz U hu
  by_cases dn : d ≤ n
  · have ok : 2^d * 2^(n-d) ≤ 2^d*S.card := calc
      _ = 2^n := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := le.trans (Nat.mul_le_mul_right S.card (Nat.pow_le_pow_right (by decide) card))
    exact Nat.le_of_mul_le_mul_left ok (Nat.two_pow_pos d)
  · have mem : base ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,yes⟩
    simpa [Nat.sub_eq_zero_of_le (by omega : n≤d)] using Finset.card_pos.mpr ⟨base,mem⟩

end PEqualNP.Outside.L_lib_606_aux

open PEqualNP.Outside.L_lib_606_aux in
theorem PEqualNP.Outside.L_lib_606 : ∀ (g m r : Nat),
  let A := Fin (m+1)
  let V := Fin g × Fin m × Fin r
  let W := V → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)
  let Y := Fin g → A
  ∀ (label : Fin g → Fin m → A → Fin r → Bool) (pick : W → Y),
    (∀ x j i, (fun v => x (j,i,v)) ≠ label j i (pick x j)) →
    ∀ (test : Y → Bool) (base : Y) (coord : Fin g),
      let ones := ((Finset.univ : Finset A).filter (fun z =>
        test (Function.update base coord z) = true)).card
      0 < ones → ones < m+1 →
      ∀ b : Nat, deg b (fun word => test (pick word)) → max ones (m+1-ones) ≤ b := by
  classical
  intro g m r A V W deg Y label pick valid test base coord ones positive notAll degree degTest
  let color := fun a : A => test (Function.update base coord a)
  let red := Finset.univ.filter (fun a : A => color a=true)
  let blue := Finset.univ.filter (fun a : A => color a=false)
  have colors : red.card + blue.card=m+1 := by
    simpa [red,blue,A] using Finset.card_filter_add_card_filter_not
      (s:=(Finset.univ : Finset A)) (fun a => color a=true)
  have dtest : D degree (fun x => bit (test (pick x))) := by
    obtain ⟨terms,sz,ok⟩ := degTest
    refine ⟨terms,sz,?_⟩
    intro x; dsimp only at ok ⊢
    rw [ok,parity,Finset.natCast_card_filter]
    exact Finset.sum_congr rfl (fun a _ => by unfold mon; split_ifs <;> rfl)
  have opposite (b : A) :
      (Finset.univ.filter (fun a : A => color a ≠ color b)).card ≤ degree := by
    let S := Finset.univ.filter (fun a : A => color a ≠ color b)
    let e : (↥S) ≃ Fin S.card := Fintype.equivFinOfCardEq (Fintype.card_coe _)
    let Flags := Fin S.card → Bool
    let center := Function.update base coord b
    let ord := fun (j : Fin g) (i : Fin m) => (center j).succAbove i
    let fire := fun (z : Flags) (j : Fin g) (i : Fin m) =>
      if h : j=coord ∧ ord j i ∈ S then z (e ⟨ord j i,h.2⟩) else false
    let embed := fun (z : Flags) (v : V) =>
      label v.1 v.2.1 (if fire z v.1 v.2.1 then center v.1 else ord v.1 v.2.1) v.2.2
    have lin (v : V) : D 1 (fun z => bit (embed z v)) := by
      by_cases h : v.1=coord ∧ ord v.1 v.2.1 ∈ S
      · let i := e ⟨ord v.1 v.2.1,h.2⟩
        have eq (z : Flags) : embed z v =
            if z i then label v.1 v.2.1 (center v.1) v.2.2 else label v.1 v.2.1 (ord v.1 v.2.1) v.2.2 := by
          have fireEq : fire z v.1 v.2.1=z i := by
            unfold fire; split
            · rfl
            · contradiction
          dsimp only [embed]
          rw [fireEq]
          cases z i <;> rfl
        simpa only [eq] using dMux i (label v.1 v.2.1 (center v.1) v.2.2) (label v.1 v.2.1 (ord v.1 v.2.1) v.2.2)
      · have eq (z : Flags) : embed z v=label v.1 v.2.1 (ord v.1 v.2.1) v.2.2 := by
          have fireEq : fire z v.1 v.2.1=false := by
            unfold fire; split
            · contradiction
            · rfl
          dsimp only [embed];rw [fireEq]; rfl
        simp only [eq]
        cases hbit : label v.1 v.2.1 (ord v.1 v.2.1) v.2.2
        · exact dZero 1
        · exact dMono dOne (by decide : 0≤1)
    have source (z : Flags) (j : Fin g) (i : Fin m) :
        (if fire z j i then center j else ord j i) ≠ pick (embed z) j := by
      intro eq
      exact valid (embed z) j i (by rw [← eq])
    have forced (z : Flags) (j : Fin g) (off : ∀ i, fire z j i=false) :
        pick (embed z) j = center j := by
      by_contra ne
      obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq ne
      exact source z j i (by simpa [off,ord] using hi)
    have other (z : Flags) (j : Fin g) (ne : j ≠ coord) : pick (embed z) j=base j := by
      simpa [center,ne] using forced z j (fun i => by simp [fire,ne])
    have onlyCoord (z : Flags) : pick (embed z) = Function.update base coord (pick (embed z) coord) := by
      funext j; by_cases eq : j=coord
      · subst j; simp
      · simpa [eq] using other z j eq
    let empty : Flags := fun _ => false
    have baseColor : test (pick (embed empty))=color b := by
      have ee := onlyCoord empty
      have h := forced empty coord (fun i => by simp [fire,empty])
      simpa only [color] using congrArg test (ee.trans (congrArg (Function.update base coord)
        (by simpa [center] using h)))
    have changed (z : Flags) (ne : z ≠ empty) : test (pick (embed z)) ≠ color b := by
      obtain ⟨k,hk⟩ : ∃ k, z k=true := by
        by_contra! hn; apply ne; funext k; simpa [empty] using hn k
      let a := e.symm k
      obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq (show a.val ≠ center coord from by
        have diff := (Finset.mem_filter.mp a.property).2
        simpa [center] using (fun eq => diff (congrArg color eq) : a.val ≠ b))
      have key : ord coord i=a.val := hi
      have on : fire z coord i=true := by
        have mem : ord coord i ∈ S := key ▸ a.property
        simp only [fire,dite_eq_left (show coord=coord ∧ ord coord i ∈ S from ⟨rfl,mem⟩)]
        have same : (⟨ord coord i,mem⟩ : (↥S))=a := Subtype.ext key
        simpa [same,a] using hk
      have notB : pick (embed z) coord ≠ center coord := fun eq => source z coord i (by simpa [on] using eq.symm)
      obtain ⟨u,hu⟩ := Fin.exists_succAbove_eq notB
      have isOn : fire z coord u=true := by
        cases ho : fire z coord u
        · exact (source z coord u (by simpa [ho,ord] using hu)).elim
        · rfl
      have use : ord coord u ∈ S := by
        by_contra hn; simp [fire,hn] at isOn
      have v : pick (embed z) coord ∈ S := (show ord coord u=pick (embed z) coord from hu) ▸ use
      have c := (Finset.mem_filter.mp v).2
      change test (pick (embed z)) ≠ _
      exact (congrArg test (onlyCoord z)).symm ▸ c
    let one := fun z : Flags => if test (pick (embed z))=color b then (1:K) else 0
    have hdeg : D degree one := dMatch (pull embed lin dtest) (color b)
    have size := supportSize one hdeg empty (ite_eq_left baseColor)
    have setEq : Finset.univ.filter (fun z : Flags => one z=1) = {empty} := by
      ext z
      by_cases eq : z=empty
      · subst z; simp [one,baseColor]
      · simp [one,changed z eq,eq]
    rw [setEq,Finset.card_singleton] at size
    change S.card ≤ degree
    by_contra! less
    have := Nat.one_lt_two_pow (show S.card-degree ≠ 0 by omega)
    omega
  change 0 < red.card at positive
  change red.card < m+1 at notAll
  obtain ⟨a,ra⟩ := Finset.card_pos.mp positive
  obtain ⟨b,bb⟩ := Finset.card_pos.mp (show 0<blue.card by omega)
  have ha := (Finset.mem_filter.mp ra).2
  have hb := (Finset.mem_filter.mp bb).2
  have lr : red.card ≤ degree := by simpa [red,hb] using opposite b
  have lb : blue.card ≤ degree := by simpa [blue,ha] using opposite a
  change max red.card (m+1-red.card) ≤ degree
  omega
